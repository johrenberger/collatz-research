"""Black-box tests for the external-workspace lifecycle ledger."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).parents[1] / "scripts" / "agent_lifecycle.py"


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)


@pytest.fixture
def project(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "Lifecycle Test")
    (repo / "README.md").write_text("test\n", encoding="utf-8")
    _git(repo, "add", "README.md")
    _git(repo, "commit", "-m", "initial")
    return tmp_path


def _run(project: Path, *args: str, expect: int = 0) -> dict[str, object]:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--project-root", str(project), *args],
        text=True,
        capture_output=True,
    )
    assert result.returncode == expect, result.stderr
    return json.loads(result.stdout if expect == 0 else result.stderr)


def _run_direct(repo: Path, state: Path, *args: str, expect: int = 0) -> dict[str, object]:
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-path",
            str(repo),
            "--state-dir",
            str(state),
            *args,
        ],
        text=True,
        capture_output=True,
    )
    assert result.returncode == expect, result.stderr
    return json.loads(result.stdout if expect == 0 else result.stderr)


def test_duplicate_turn_is_a_noop_and_identity_mismatch_is_rejected(project: Path) -> None:
    args = (
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-1",
        "--payload-json",
        '{"objective":"test"}',
    )
    assert _run(project, *args)["decision"] == "started"
    assert _run(project, *args)["decision"] == "already_started"
    mismatch = _run(
        project,
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-1",
        "--payload-json",
        '{"objective":"different"}',
        expect=2,
    )
    assert "reused" in mismatch["error"]


def test_operation_intent_prevents_duplicate_mutation_and_resume_preserves_receipt(
    project: Path,
) -> None:
    _run(project, "begin", "--packet-id", "packet-1", "--turn-id", "turn-1", "--payload-json", "{}")
    first = _run(
        project,
        "begin-operation",
        "--turn-id",
        "turn-1",
        "--step-id",
        "post-review",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        '{"body":"review"}',
    )
    assert first["decision"] == "execute_once"
    duplicate = _run(
        project,
        "begin-operation",
        "--turn-id",
        "turn-1",
        "--step-id",
        "post-review",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        '{"body":"review"}',
    )
    assert duplicate["decision"] == "duplicate"
    resumed = _run(project, "resume", "--turn-id", "turn-1")
    assert first["operation_key"] in resumed["pending_operation_keys"]


def test_direct_checkout_uses_external_state_and_preserves_operation_receipts_across_turns(
    project: Path,
) -> None:
    repo = project / "repo"
    state = project / "external-state"
    _run_direct(
        repo,
        state,
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-1",
        "--payload-json",
        "{}",
    )
    first = _run_direct(
        repo,
        state,
        "begin-operation",
        "--turn-id",
        "turn-1",
        "--step-id",
        "post-review",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        '{"body":"review"}',
    )
    _run_direct(
        repo,
        state,
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-2",
        "--payload-json",
        "{}",
    )
    duplicate = _run_direct(
        repo,
        state,
        "begin-operation",
        "--turn-id",
        "turn-2",
        "--step-id",
        "replayed-review",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        '{"body":"review"}',
    )
    assert duplicate["decision"] == "duplicate"
    assert duplicate["operation_key"] == first["operation_key"]
    assert (state / "turn-ledger.json").exists()
    assert not (repo / "state").exists()


def test_explicit_budget_blocks_before_an_unbounded_tool_loop(project: Path) -> None:
    _run(
        project,
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-1",
        "--payload-json",
        "{}",
        "--max-tool-calls",
        "1",
    )
    assert (
        _run(project, "consume", "--turn-id", "turn-1", "--kind", "tool")["decision"] == "consumed"
    )
    assert (
        _run(project, "consume", "--turn-id", "turn-1", "--kind", "tool")["decision"] == "blocked"
    )


def test_elapsed_budget_blocks_a_later_controller_action(project: Path) -> None:
    _run(
        project,
        "begin",
        "--packet-id",
        "packet-1",
        "--turn-id",
        "turn-1",
        "--payload-json",
        "{}",
        "--max-seconds",
        "1",
    )
    ledger_path = project / "state" / "turn-ledger.json"
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    ledger["turns"]["turn-1"]["created_at"] = "2000-01-01T00:00:00+00:00"
    ledger_path.write_text(json.dumps(ledger), encoding="utf-8")

    assert (
        _run(project, "consume", "--turn-id", "turn-1", "--kind", "model")["decision"] == "blocked"
    )


def test_finished_turn_cannot_create_a_new_external_operation(project: Path) -> None:
    _run(project, "begin", "--packet-id", "packet-1", "--turn-id", "turn-1", "--payload-json", "{}")
    _run(project, "finish", "--turn-id", "turn-1", "--status", "passed", "--evidence-json", "{}")
    blocked = _run(
        project,
        "begin-operation",
        "--turn-id",
        "turn-1",
        "--step-id",
        "late-write",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        "{}",
        expect=2,
    )
    assert "cannot create" in blocked["error"]


def test_operation_receipt_cannot_be_finished_by_a_different_turn(project: Path) -> None:
    _run(project, "begin", "--packet-id", "packet-1", "--turn-id", "turn-1", "--payload-json", "{}")
    first = _run(
        project,
        "begin-operation",
        "--turn-id",
        "turn-1",
        "--step-id",
        "post-review",
        "--operation-kind",
        "github-comment",
        "--target",
        "pull/23",
        "--input-json",
        "{}",
    )
    _run(project, "begin", "--packet-id", "packet-1", "--turn-id", "turn-2", "--payload-json", "{}")
    rejected = _run(
        project,
        "finish-operation",
        "--turn-id",
        "turn-2",
        "--operation-key",
        str(first["operation_key"]),
        "--status",
        "succeeded",
        "--result-json",
        "{}",
        expect=2,
    )
    assert "does not belong" in rejected["error"]


def test_review_request_is_deduped_by_repository_pr_and_head_sha(project: Path) -> None:
    args = (
        "request-review",
        "--repository",
        "johrenberger/collatz-research",
        "--pr-number",
        "65",
        "--head-sha",
        "a" * 40,
        "--round",
        "1",
        "--payload-json",
        '{"validation":"green"}',
    )
    first = _run(project, *args)
    replay = _run(project, *args)
    assert first["decision"] == "review_requested"
    assert replay["decision"] == "already_requested"
    assert replay["review_key"] == first["review_key"]


def test_review_receipt_must_match_requested_pr_head_and_is_immutable(project: Path) -> None:
    requested = _run(
        project,
        "request-review",
        "--repository",
        "johrenberger/collatz-research",
        "--pr-number",
        "65",
        "--head-sha",
        "b" * 40,
        "--payload-json",
        "{}",
    )
    key = str(requested["review_key"])
    receipt = {
        "repository": "johrenberger/collatz-research",
        "pr_number": 65,
        "head_sha": "b" * 40,
        "round": 1,
        "model": "openai/gpt-5.6-terra",
        "verdict": "approved",
        "review_url": "https://example.invalid/review/1",
        "findings": [],
    }
    recorded = _run(
        project,
        "record-review",
        "--review-key",
        key,
        "--receipt-json",
        json.dumps(receipt),
    )
    assert recorded["decision"] == "review_recorded"
    assert _run(
        project,
        "record-review",
        "--review-key",
        key,
        "--receipt-json",
        json.dumps(receipt),
    )["decision"] == "already_recorded"
    receipt["verdict"] = "changes_requested"
    conflict = _run(
        project,
        "record-review",
        "--review-key",
        key,
        "--receipt-json",
        json.dumps(receipt),
        expect=2,
    )
    assert "conflicts" in conflict["error"]


def test_only_one_dispatcher_can_claim_a_pending_review(project: Path) -> None:
    requested = _run(
        project,
        "request-review",
        "--repository",
        "johrenberger/collatz-research",
        "--pr-number",
        "65",
        "--head-sha",
        "c" * 40,
        "--payload-json",
        "{}",
    )
    claimed = _run(project, "claim-review", "--dispatcher", "terra-worker")
    assert claimed["decision"] == "claimed"
    assert claimed["review_key"] == requested["review_key"]
    assert _run(project, "claim-review", "--dispatcher", "another-worker")["decision"] == "none_pending"
