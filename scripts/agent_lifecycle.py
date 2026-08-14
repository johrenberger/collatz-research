#!/usr/bin/env python3
"""Durable, idempotent packet lifecycle state for an external agent workspace.

The script is intentionally stdlib-only. Invoke it against the *outer* project
workspace, whose Git checkout is `<project-root>/repo` and mutable state is
`<project-root>/state`.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import subprocess
import sys
import time
from collections.abc import Iterator
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SCHEMA_VERSION = 1


def _utc_now() -> str:
    return datetime.now(UTC).isoformat()


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical(value).encode("utf-8")).hexdigest()


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def _repo_snapshot(project_root: Path) -> dict[str, Any]:
    repo = project_root / "repo"
    if not repo.is_dir():
        raise ValueError(f"missing Git checkout: {repo}")
    top = Path(_git(repo, "rev-parse", "--show-toplevel")).resolve()
    if top != repo.resolve():
        raise ValueError(f"expected repository root {repo.resolve()}, got {top}")
    return {
        "repo_head": _git(repo, "rev-parse", "HEAD"),
        "branch": _git(repo, "branch", "--show-current"),
        "worktree_clean": not bool(_git(repo, "status", "--porcelain")),
    }


@contextlib.contextmanager
def _locked_ledger(
    project_root: Path, timeout_seconds: float = 10
) -> Iterator[tuple[Path, dict[str, Any]]]:
    state = project_root / "state"
    state.mkdir(parents=True, exist_ok=True)
    lock = state / ".turn-ledger.lock"
    deadline = time.monotonic() + timeout_seconds
    fd: int | None = None
    while fd is None:
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, f"pid={os.getpid()} at={_utc_now()}\n".encode())
        except FileExistsError:
            if time.monotonic() >= deadline:
                raise TimeoutError(f"lifecycle lock is held: {lock}") from None
            time.sleep(0.05)
    ledger_path = state / "turn-ledger.json"
    try:
        if ledger_path.exists():
            ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
        else:
            ledger = {"schema_version": SCHEMA_VERSION, "turns": {}}
        if ledger.get("schema_version") != SCHEMA_VERSION:
            raise ValueError("unsupported turn ledger schema")
        yield ledger_path, ledger
        temporary = ledger_path.with_suffix(".json.tmp")
        temporary.write_text(_canonical(ledger) + "\n", encoding="utf-8")
        os.replace(temporary, ledger_path)
    finally:
        if fd is not None:
            os.close(fd)
        lock.unlink(missing_ok=True)


def _load_json(raw: str) -> Any:
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid JSON argument: {exc.msg}") from exc


def _turn_or_error(ledger: dict[str, Any], turn_id: str) -> dict[str, Any]:
    try:
        return ledger["turns"][turn_id]
    except KeyError as exc:
        raise ValueError(f"unknown turn: {turn_id}") from exc


def begin(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    payload = _load_json(args.payload_json)
    snapshot = _repo_snapshot(project)
    identity = {
        "packet_id": args.packet_id,
        "snapshot": snapshot,
        "payload_digest": _digest(payload),
    }
    with _locked_ledger(project) as (_, ledger):
        previous = ledger["turns"].get(args.turn_id)
        if previous:
            if previous["identity"] != identity:
                raise ValueError("turn ID was reused with different packet, Git state, or payload")
            return {"decision": "already_started", "turn": previous}
        record = {
            "identity": identity,
            "status": "running",
            "created_at": _utc_now(),
            "budgets": {
                "max_model_attempts": args.max_model_attempts,
                "max_tool_calls": args.max_tool_calls,
                "max_seconds": args.max_seconds,
                "model_attempts": 0,
                "tool_calls": 0,
            },
            "operations": {},
        }
        ledger["turns"][args.turn_id] = record
        return {"decision": "started", "turn": record}


def consume(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    field = "model_attempts" if args.kind == "model" else "tool_calls"
    limit = "max_model_attempts" if args.kind == "model" else "max_tool_calls"
    with _locked_ledger(project) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        if turn["status"] not in {"running", "resumable"}:
            raise ValueError(f"cannot consume budget for turn in {turn['status']}")
        turn["status"] = "running"
        if turn["budgets"][field] >= turn["budgets"][limit]:
            turn["status"] = "budget_blocked"
            turn["blocked_at"] = _utc_now()
            return {"decision": "blocked", "turn": turn}
        turn["budgets"][field] += 1
        return {"decision": "consumed", "turn": turn}


def begin_operation(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    input_value = _load_json(args.input_json)
    with _locked_ledger(project) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        key = _digest(
            {
                "packet_id": turn["identity"]["packet_id"],
                "repo_head": turn["identity"]["snapshot"]["repo_head"],
                "kind": args.operation_kind,
                "target": args.target,
                "input_digest": _digest(input_value),
            }
        )
        existing = turn["operations"].get(key)
        if existing:
            return {"decision": "duplicate", "operation_key": key, "operation": existing}
        operation = {
            "step_id": args.step_id,
            "kind": args.operation_kind,
            "target": args.target,
            "status": "intent",
            "created_at": _utc_now(),
        }
        turn["operations"][key] = operation
        return {"decision": "execute_once", "operation_key": key, "operation": operation}


def finish_operation(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    with _locked_ledger(project) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        try:
            operation = turn["operations"][args.operation_key]
        except KeyError as exc:
            raise ValueError("unknown operation key") from exc
        if operation["status"] == "succeeded":
            return {"decision": "already_succeeded", "operation": operation}
        operation["status"] = args.status
        operation["finished_at"] = _utc_now()
        operation["result_digest"] = _digest(_load_json(args.result_json))
        return {"decision": "recorded", "operation": operation}


def resume(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    with _locked_ledger(project) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        if turn["status"] in {"passed", "budget_blocked", "transport_blocked"}:
            return {"decision": "not_resumable", "turn": turn}
        intents = [key for key, op in turn["operations"].items() if op["status"] == "intent"]
        turn["status"] = "resumable"
        turn["resumed_at"] = _utc_now()
        return {"decision": "resume_from_receipt", "pending_operation_keys": intents, "turn": turn}


def finish(args: argparse.Namespace) -> dict[str, Any]:
    project = Path(args.project_root).resolve()
    with _locked_ledger(project) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        turn["status"] = args.status
        turn["finished_at"] = _utc_now()
        turn["evidence"] = _load_json(args.evidence_json)
        return {"decision": "finished", "turn": turn}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", required=True)
    commands = parser.add_subparsers(required=True, dest="command")
    begin_parser = commands.add_parser("begin")
    begin_parser.add_argument("--packet-id", required=True)
    begin_parser.add_argument("--turn-id", required=True)
    begin_parser.add_argument("--payload-json", required=True)
    begin_parser.add_argument("--max-model-attempts", type=int, default=3)
    begin_parser.add_argument("--max-tool-calls", type=int, default=20)
    begin_parser.add_argument("--max-seconds", type=int, default=900)
    begin_parser.set_defaults(handler=begin)
    consume_parser = commands.add_parser("consume")
    consume_parser.add_argument("--turn-id", required=True)
    consume_parser.add_argument("--kind", choices=("model", "tool"), required=True)
    consume_parser.set_defaults(handler=consume)
    operation_parser = commands.add_parser("begin-operation")
    operation_parser.add_argument("--turn-id", required=True)
    operation_parser.add_argument("--step-id", required=True)
    operation_parser.add_argument("--operation-kind", required=True)
    operation_parser.add_argument("--target", required=True)
    operation_parser.add_argument("--input-json", required=True)
    operation_parser.set_defaults(handler=begin_operation)
    finish_operation_parser = commands.add_parser("finish-operation")
    finish_operation_parser.add_argument("--turn-id", required=True)
    finish_operation_parser.add_argument("--operation-key", required=True)
    finish_operation_parser.add_argument("--status", choices=("succeeded", "failed"), required=True)
    finish_operation_parser.add_argument("--result-json", required=True)
    finish_operation_parser.set_defaults(handler=finish_operation)
    resume_parser = commands.add_parser("resume")
    resume_parser.add_argument("--turn-id", required=True)
    resume_parser.set_defaults(handler=resume)
    finish_parser = commands.add_parser("finish")
    finish_parser.add_argument("--turn-id", required=True)
    finish_parser.add_argument(
        "--status", choices=("passed", "blocked", "transport_blocked"), required=True
    )
    finish_parser.add_argument("--evidence-json", required=True)
    finish_parser.set_defaults(handler=finish)
    return parser


def main() -> int:
    parser = _parser()
    args = parser.parse_args()
    try:
        print(json.dumps(args.handler(args), sort_keys=True))
    except (OSError, ValueError, subprocess.CalledProcessError, TimeoutError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
