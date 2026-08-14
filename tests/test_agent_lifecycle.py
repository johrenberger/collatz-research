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


def test_operation_intent_prevents_duplicate_mutation_and_resume_preserves_receipt(project: Path) -> None:
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
    assert _run(project, "consume", "--turn-id", "turn-1", "--kind", "tool")["decision"] == "consumed"
    assert _run(project, "consume", "--turn-id", "turn-1", "--kind", "tool")["decision"] == "blocked"
