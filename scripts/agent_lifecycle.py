#!/usr/bin/env python3
"""Durable, idempotent packet lifecycle state for an agent repository.

The script is intentionally stdlib-only. New deployments pass an explicit Git
checkout and external state directory; the former outer-workspace layout remains
supported only for backwards-compatible recovery.
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

SCHEMA_VERSION = 3


def _utc_now() -> str:
    return datetime.now(UTC).isoformat()


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical(value).encode("utf-8")).hexdigest()


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def _repo_snapshot(repo: Path) -> dict[str, Any]:
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


def _paths(args: argparse.Namespace) -> tuple[Path, Path]:
    if args.repo_path or args.state_dir:
        if not args.repo_path or not args.state_dir:
            raise ValueError("--repo-path and --state-dir must be supplied together")
        if args.project_root:
            raise ValueError("use either --project-root or --repo-path/--state-dir")
        return Path(args.repo_path).resolve(), Path(args.state_dir).resolve()
    if not args.project_root:
        raise ValueError("supply --repo-path and --state-dir")
    project = Path(args.project_root).resolve()
    return project / "repo", project / "state"


@contextlib.contextmanager
def _locked_ledger(
    state: Path, timeout_seconds: float = 10
) -> Iterator[tuple[Path, dict[str, Any]]]:
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
        if ledger.get("schema_version") in {1, 2}:
            ledger["schema_version"] = SCHEMA_VERSION
            ledger.setdefault("operations", {})
            ledger.setdefault("review_requests", {})
        if ledger.get("schema_version") != SCHEMA_VERSION:
            raise ValueError("unsupported turn ledger schema")
        ledger.setdefault("operations", {})
        ledger.setdefault("review_requests", {})
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
    repo, state = _paths(args)
    payload = _load_json(args.payload_json)
    snapshot = _repo_snapshot(repo)
    identity = {
        "packet_id": args.packet_id,
        "snapshot": snapshot,
        "payload_digest": _digest(payload),
    }
    with _locked_ledger(state) as (_, ledger):
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
    _, state = _paths(args)
    field = "model_attempts" if args.kind == "model" else "tool_calls"
    limit = "max_model_attempts" if args.kind == "model" else "max_tool_calls"
    with _locked_ledger(state) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        if turn["status"] not in {"running", "resumable"}:
            raise ValueError(f"cannot consume budget for turn in {turn['status']}")
        turn["status"] = "running"
        created_at = datetime.fromisoformat(turn["created_at"])
        if (datetime.now(UTC) - created_at).total_seconds() >= turn["budgets"]["max_seconds"]:
            turn["status"] = "budget_blocked"
            turn["blocked_at"] = _utc_now()
            return {"decision": "blocked", "turn": turn}
        if turn["budgets"][field] >= turn["budgets"][limit]:
            turn["status"] = "budget_blocked"
            turn["blocked_at"] = _utc_now()
            return {"decision": "blocked", "turn": turn}
        turn["budgets"][field] += 1
        return {"decision": "consumed", "turn": turn}


def begin_operation(args: argparse.Namespace) -> dict[str, Any]:
    _, state = _paths(args)
    input_value = _load_json(args.input_json)
    with _locked_ledger(state) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        if turn["status"] not in {"running", "resumable"}:
            raise ValueError(f"cannot create an operation for turn in {turn['status']}")
        turn["status"] = "running"
        key = _digest(
            {
                "packet_id": turn["identity"]["packet_id"],
                "repo_head": turn["identity"]["snapshot"]["repo_head"],
                "kind": args.operation_kind,
                "target": args.target,
                "input_digest": _digest(input_value),
            }
        )
        existing = ledger["operations"].get(key)
        if existing:
            return {"decision": "duplicate", "operation_key": key, "operation": existing}
        operation = {
            "turn_id": args.turn_id,
            "step_id": args.step_id,
            "kind": args.operation_kind,
            "target": args.target,
            "status": "intent",
            "created_at": _utc_now(),
        }
        ledger["operations"][key] = operation
        turn["operations"][key] = operation
        return {"decision": "execute_once", "operation_key": key, "operation": operation}


def finish_operation(args: argparse.Namespace) -> dict[str, Any]:
    _, state = _paths(args)
    with _locked_ledger(state) as (_, ledger):
        _turn_or_error(ledger, args.turn_id)
        try:
            operation = ledger["operations"][args.operation_key]
        except KeyError as exc:
            raise ValueError("unknown operation key") from exc
        if operation["turn_id"] != args.turn_id:
            raise ValueError("operation does not belong to this turn")
        if operation["status"] == "succeeded":
            return {"decision": "already_succeeded", "operation": operation}
        operation["status"] = args.status
        operation["finished_at"] = _utc_now()
        operation["result_digest"] = _digest(_load_json(args.result_json))
        return {"decision": "recorded", "operation": operation}


def resume(args: argparse.Namespace) -> dict[str, Any]:
    _, state = _paths(args)
    with _locked_ledger(state) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        if turn["status"] in {"passed", "budget_blocked", "transport_blocked"}:
            return {"decision": "not_resumable", "turn": turn}
        intents = [
            key
            for key, op in ledger["operations"].items()
            if op.get("turn_id") == args.turn_id and op["status"] == "intent"
        ]
        turn["status"] = "resumable"
        turn["resumed_at"] = _utc_now()
        return {"decision": "resume_from_receipt", "pending_operation_keys": intents, "turn": turn}


def finish(args: argparse.Namespace) -> dict[str, Any]:
    _, state = _paths(args)
    with _locked_ledger(state) as (_, ledger):
        turn = _turn_or_error(ledger, args.turn_id)
        turn["status"] = args.status
        turn["finished_at"] = _utc_now()
        turn["evidence"] = _load_json(args.evidence_json)
        return {"decision": "finished", "turn": turn}


def request_review(args: argparse.Namespace) -> dict[str, Any]:
    """Create an idempotent independent-review handoff for one PR head."""
    _, state = _paths(args)
    payload = _load_json(args.payload_json)
    key = _digest(
        {
            "repository": args.repository,
            "pr_number": args.pr_number,
            "head_sha": args.head_sha,
        }
    )
    with _locked_ledger(state) as (_, ledger):
        existing = ledger["review_requests"].get(key)
        if existing:
            if existing["payload_digest"] != _digest(payload):
                raise ValueError("review request identity was reused with different payload")
            return {"decision": "already_requested", "review_key": key, "review": existing}
        review = {
            "repository": args.repository,
            "pr_number": args.pr_number,
            "head_sha": args.head_sha,
            "round": args.round,
            "status": "awaiting_review",
            "created_at": _utc_now(),
            "payload_digest": _digest(payload),
        }
        ledger["review_requests"][key] = review
        return {"decision": "review_requested", "review_key": key, "review": review}


def record_review(args: argparse.Namespace) -> dict[str, Any]:
    """Persist an immutable reviewer receipt for a previously requested head."""
    _, state = _paths(args)
    receipt = _load_json(args.receipt_json)
    with _locked_ledger(state) as (_, ledger):
        try:
            review = ledger["review_requests"][args.review_key]
        except KeyError as exc:
            raise ValueError("unknown review request") from exc
        if review["status"] == "reviewed":
            if review["receipt_digest"] != _digest(receipt):
                raise ValueError("review receipt conflicts with existing receipt")
            return {"decision": "already_recorded", "review_key": args.review_key, "review": review}
        if receipt.get("repository") != review["repository"]:
            raise ValueError("review receipt repository does not match request")
        if receipt.get("pr_number") != review["pr_number"]:
            raise ValueError("review receipt PR number does not match request")
        if receipt.get("head_sha") != review["head_sha"]:
            raise ValueError("review receipt head SHA does not match request")
        if receipt.get("round") != review["round"]:
            raise ValueError("review receipt round does not match request")
        if receipt.get("verdict") not in {"approved", "changes_requested", "escalated"}:
            raise ValueError("review receipt has invalid verdict")
        review["status"] = "reviewed"
        review["recorded_at"] = _utc_now()
        review["receipt_digest"] = _digest(receipt)
        review["receipt"] = receipt
        return {"decision": "review_recorded", "review_key": args.review_key, "review": review}


def claim_review(args: argparse.Namespace) -> dict[str, Any]:
    """Atomically lease the next pending review handoff to one dispatcher."""
    _, state = _paths(args)
    with _locked_ledger(state) as (_, ledger):
        candidates = [
            (key, review)
            for key, review in ledger["review_requests"].items()
            if review["status"] == "awaiting_review"
        ]
        if args.review_key:
            candidates = [item for item in candidates if item[0] == args.review_key]
        if not candidates:
            return {"decision": "none_pending"}
        key, review = min(candidates, key=lambda item: item[1]["created_at"])
        review["status"] = "dispatched"
        review["dispatched_at"] = _utc_now()
        review["dispatcher"] = args.dispatcher
        return {"decision": "claimed", "review_key": key, "review": review}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root")
    parser.add_argument("--repo-path")
    parser.add_argument("--state-dir")
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
    request_review_parser = commands.add_parser("request-review")
    request_review_parser.add_argument("--repository", required=True)
    request_review_parser.add_argument("--pr-number", type=int, required=True)
    request_review_parser.add_argument("--head-sha", required=True)
    request_review_parser.add_argument("--round", type=int, default=1)
    request_review_parser.add_argument("--payload-json", required=True)
    request_review_parser.set_defaults(handler=request_review)
    record_review_parser = commands.add_parser("record-review")
    record_review_parser.add_argument("--review-key", required=True)
    record_review_parser.add_argument("--receipt-json", required=True)
    record_review_parser.set_defaults(handler=record_review)
    claim_review_parser = commands.add_parser("claim-review")
    claim_review_parser.add_argument("--dispatcher", required=True)
    claim_review_parser.add_argument("--review-key")
    claim_review_parser.set_defaults(handler=claim_review)
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
