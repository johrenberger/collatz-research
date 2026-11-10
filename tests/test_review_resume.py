"""Tests for reviewer-session resume, scoped dispatch, and failed-dispatch requeue."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).parents[1]
LIFECYCLE = REPO / "scripts" / "agent_lifecycle.py"
DISPATCHER = REPO / "scripts" / "dispatch_codex_pr_review.py"
PLUGIN = REPO / "integrations" / "openclaw-lifecycle-plugin" / "index.js"


def _run(state: Path, *args: str) -> dict[str, object]:
    result = subprocess.run(
        [
            sys.executable,
            str(LIFECYCLE),
            "--repo-path",
            str(REPO),
            "--state-dir",
            str(state),
            *args,
        ],
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


def _request(state: Path, pr_number: int, head_sha: str, payload: dict[str, object]) -> str:
    return str(
        _run(
            state,
            "request-review",
            "--repository",
            "johrenberger/collatz-research",
            "--pr-number",
            str(pr_number),
            "--head-sha",
            head_sha,
            "--payload-json",
            json.dumps(payload),
        )["review_key"]
    )


def _record(state: Path, review_key: str, receipt: dict[str, object]) -> None:
    _run(state, "record-review", "--review-key", review_key, "--receipt-json", json.dumps(receipt))


def _first_round_receipt(pr_number: int, head_sha: str, session_key: str) -> dict[str, object]:
    return {
        "repository": "johrenberger/collatz-research",
        "pr_number": pr_number,
        "head_sha": head_sha,
        "round": 1,
        "model": "openai/gpt-5.6-terra",
        "verdict": "changes_requested",
        "continuation_handle": {"session_key": session_key},
        "findings": [{"severity": "P2", "summary": "stale wording"}],
    }


def test_a_claimed_handoff_carries_the_prior_rounds_receipt(tmp_path: Path) -> None:
    state = tmp_path / "state"
    first_key = _request(state, 7, "head-one", {"round": 1})
    _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", first_key)
    _record(state, first_key, _first_round_receipt(7, "head-one", "agent:main:reviewer-7"))

    second_key = _request(state, 7, "head-two", {"round": 2})
    claimed = _run(
        state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", second_key
    )

    prior = claimed["prior_review"]
    assert prior is not None
    assert prior["head_sha"] == "head-one"
    assert prior["receipt"]["continuation_handle"]["session_key"] == "agent:main:reviewer-7"


def test_a_first_round_claim_has_no_prior_review(tmp_path: Path) -> None:
    state = tmp_path / "state"
    key = _request(state, 8, "head-only", {"round": 1})
    claimed = _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", key)

    assert claimed["prior_review"] is None


def test_claiming_a_scoped_key_does_not_lease_an_older_pending_handoff(tmp_path: Path) -> None:
    state = tmp_path / "state"
    older = _request(state, 9, "older-head", {"round": 1})
    newer = _request(state, 10, "newer-head", {"round": 1})

    claimed = _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", newer)

    assert claimed["review_key"] == newer
    assert claimed["review"]["pr_number"] == 10

    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    assert ledger["review_requests"][older]["status"] == "awaiting_review"


def test_the_newest_pending_handoff_is_leased_by_default(tmp_path: Path) -> None:
    state = tmp_path / "state"
    older = _request(state, 12, "older-head", {"round": 1})
    newer = _request(state, 13, "newer-head", {"round": 1})

    claimed = _run(state, "claim-review", "--dispatcher", "terra-reviewer")

    assert claimed["review_key"] == newer
    assert claimed["review"]["pr_number"] == 13

    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    assert ledger["review_requests"][older]["status"] == "awaiting_review"


def test_the_claim_does_not_persist_the_prior_receipt_into_the_ledger(tmp_path: Path) -> None:
    state = tmp_path / "state"
    first_key = _request(state, 11, "head-one", {"round": 1})
    _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", first_key)
    _record(state, first_key, _first_round_receipt(11, "head-one", "agent:main:reviewer-11"))

    second_key = _request(state, 11, "head-two", {"round": 2})
    _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", second_key)

    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    assert "prior_review" not in ledger["review_requests"][second_key]


def _reviewer_receipt(pr_number: int, head_sha: str, session_key: str) -> dict[str, object]:
    return {
        "repository": "johrenberger/collatz-research",
        "pr_number": pr_number,
        "head_sha": head_sha,
        "round": 1,
        "model": "openai/gpt-5.6-terra",
        "verdict": "approved",
        "review_url": None,
        "continuation_handle": {"session_key": session_key},
        "findings": [],
    }


def _write_fake_openclaw(
    directory: Path,
    receipt: dict[str, object],
    named_answer: str,
    named_exit: int = 0,
) -> Path:
    """Write a fake openclaw answering the named-session and exec calls."""
    bin_dir = directory / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    body = (
        "#!/usr/bin/env python3\n"
        "import json, sys\n"
        "RECEIPT = " + repr(receipt) + "\n"
        "if '--session-key' in sys.argv:\n"
        f"    sys.stdout.write(json.dumps({{'text': {json.dumps(named_answer)}}}))\n"
        f"    raise SystemExit({named_exit})\n"
        "sys.stdout.write(json.dumps({'text': json.dumps(RECEIPT)}))\n"
    )
    script = bin_dir / "openclaw"
    script.write_text(body, encoding="utf-8")
    script.chmod(0o755)
    return bin_dir


def _dispatch(state: Path, bin_dir: Path, review_key: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(DISPATCHER),
            "--repo-path",
            str(REPO),
            "--state-dir",
            str(state),
            "--review-key",
            review_key,
        ],
        text=True,
        capture_output=True,
        env={**os.environ, "PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}"},
    )


def _stored_handle(state: Path, review_key: str) -> dict[str, object]:
    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    receipt = ledger["review_requests"][review_key]["receipt"]
    assert isinstance(receipt, dict)
    handle = receipt["continuation_handle"]
    assert isinstance(handle, dict)
    return handle


def test_the_dispatcher_records_a_resumable_handle(tmp_path: Path) -> None:
    state = tmp_path / "state"
    receipt = _reviewer_receipt(7, "head-one", "agent:main:reviewer-7")
    bin_dir = _write_fake_openclaw(tmp_path, receipt, json.dumps(receipt))

    key = _request(state, 7, "head-one", {"round": 1})
    result = _dispatch(state, bin_dir, key)
    assert result.returncode == 0, result.stderr

    handle = _stored_handle(state, key)
    assert handle["session_key"] == "agent:main:collatz-review-pr7"
    assert handle["reported_session_key"] == "agent:main:reviewer-7"
    assert handle["resumed"] is False


def test_the_dispatcher_falls_back_when_the_named_session_fails(tmp_path: Path) -> None:
    state = tmp_path / "state"
    receipt = _reviewer_receipt(7, "head-one", "agent:main:reviewer-7")
    bin_dir = _write_fake_openclaw(tmp_path, receipt, "session unreachable", named_exit=3)

    key = _request(state, 7, "head-one", {"round": 1})
    result = _dispatch(state, bin_dir, key)
    assert result.returncode == 0, result.stderr

    # A failed resume must not leave a handle that a later round would retry.
    assert _stored_handle(state, key)["session_key"] is None


def test_the_dispatcher_falls_back_when_the_named_session_answers_without_a_receipt(
    tmp_path: Path,
) -> None:
    state = tmp_path / "state"
    receipt = _reviewer_receipt(7, "head-one", "agent:main:reviewer-7")
    bin_dir = _write_fake_openclaw(tmp_path, receipt, "no receipt here")

    key = _request(state, 7, "head-one", {"round": 1})
    result = _dispatch(state, bin_dir, key)
    assert result.returncode == 0, result.stderr

    assert _stored_handle(state, key)["session_key"] is None


def test_a_failed_dispatch_returns_its_handoff_to_the_pending_pool(tmp_path: Path) -> None:
    state = tmp_path / "state"
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    script = bin_dir / "openclaw"
    script.write_text(
        "#!/usr/bin/env python3\n"
        "import sys\n"
        "sys.stderr.write('provider refused the dispatch')\n"
        "raise SystemExit(4)\n",
        encoding="utf-8",
    )
    script.chmod(0o755)

    key = _request(state, 7, "head-one", {"round": 1})
    result = _dispatch(state, bin_dir, key)
    assert result.returncode != 0

    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    entry = ledger["review_requests"][key]
    # A lease covers only an awaiting_review entry, so a handoff left at
    # dispatched could never be leased again and the gate became
    # permanently unsatisfiable for this pull request.
    assert entry["status"] == "awaiting_review"
    assert "dispatch failed" in entry["requeue_note"]


def test_requeue_review_leaves_a_recorded_review_untouched(tmp_path: Path) -> None:
    state = tmp_path / "state"
    key = _request(state, 7, "head-one", {"round": 1})
    _run(state, "claim-review", "--dispatcher", "terra-reviewer", "--review-key", key)
    _record(state, key, _first_round_receipt(7, "head-one", "agent:main:reviewer-7"))

    result = _run(
        state,
        "requeue-review",
        "--review-key",
        key,
        "--reason",
        "dispatch failed: provider refused",
    )

    assert result["decision"] == "already_recorded"

    ledger = json.loads((state / "turn-ledger.json").read_text(encoding="utf-8"))
    assert ledger["review_requests"][key]["status"] == "reviewed"


def test_the_plugin_dispatches_the_handoff_it_just_created() -> None:
    source = PLUGIN.read_text(encoding="utf-8")

    assert "dispatchReview(config, handoff.review_key)" in source
    assert "--review-key" in source


# Envelopes captured from the real CLI, not fabricated by a fake binary.
REAL_EXEC_ENVELOPE = {
    "ok": True,
    "text": '{"verdict": "approved", "findings": []}',
}

REAL_NAMED_SESSION_ENVELOPE = {
    "runId": "7bd6e711-ede4-4a03-9539-366a5692be86",
    "status": "ok",
    "summary": "completed",
    "result": {
        "payloads": [{"text": '{"verdict": "approved", "findings": []}', "mediaUrl": None}],
        "meta": {"durationMs": 2514, "provider": "minimax"},
    },
}


def _dispatcher_module():
    import importlib.util

    spec = importlib.util.spec_from_file_location("dispatcher", DISPATCHER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_the_receipt_is_read_from_the_real_exec_envelope() -> None:
    module = _dispatcher_module()

    assert module._extract_text(REAL_EXEC_ENVELOPE) == REAL_EXEC_ENVELOPE["text"]


def test_the_receipt_is_read_from_the_real_named_session_envelope() -> None:
    module = _dispatcher_module()

    envelope = REAL_NAMED_SESSION_ENVELOPE
    expected = envelope["result"]["payloads"][0]["text"]

    assert module._extract_text(envelope) == expected
