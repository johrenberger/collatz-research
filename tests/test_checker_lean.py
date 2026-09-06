"""Differential checks between the Python checker and Lean trajectory evaluation.

These tests compare the Python checker's accepted certificate output against the
Lean `CollatzResearch.trajectory` evaluation. They are *supporting evidence* for
the Lean checker-soundness theorem (`DescentWitness.Valid.sound` in Story 06b),
not a substitute for the formal Lean-internal bridge.

Per the PR #10 Codex review (P1): expand from a single endpoint fixture to a
deterministic corpus of valid descent certificates, compare full trajectories
(not just endpoints), and cover relevant rejection/boundary cases.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest
from collatz_research.canonical import write_jsonl
from collatz_research.certificates import build_descent_certificate
from collatz_research.checker import (
    ERR_NOT_DESCENT,
    ERR_TRAJECTORY_MISMATCH,
    ERR_TRAJECTORY_UNDEFINED,
    CertificateCheckError,
    check_certificate,
)
from collatz_research.trajectory import iterate

LAKE_AVAILABLE = shutil.which("lake") is not None
skip_if_no_lake = pytest.mark.skipif(not LAKE_AVAILABLE, reason="Lean toolchain is not available")


# Deterministic corpus of (start, steps) pairs that produce valid descent
# certificates. Each pair must satisfy:
#   - start is positive odd (Python's accelerated_step precondition)
#   - the trajectory stays on the positive odd domain for `steps` steps
#   - trajectory(start, steps) < start  (strict descent)
#
# Verified locally by running `iterate` over each entry and checking
# trajectory[start_index] < start for every intermediate.
VALID_CORPUS: list[tuple[int, int]] = [
    (5, 1),  # canonical fixture: 5 → 1
    (5, 2),  # 5 → 1 → 1 (absorbing at 1)
    (9, 5),  # 9 → 7 → 11 → 17 → 13 → 5
    (3, 5),  # 3 → 5 → 1 → 1 → 1 → 1
    (15, 7),  # 15 → 23 → 35 → 53 → 5 → 1 → 1 → 1
    (7, 5),  # 7 → 11 → 17 → 13 → 5 → 1
]


# Python-only rejection cases. These do NOT touch Lean; they exercise the
# Python checker's fail-closed behavior on malformed / non-descent certificates.
# They live in test_checker.py as part of the mutation-rejection suite; here
# we list the Python-rejected cases that are most relevant to the Lean
# boundary (matching the rejection categories defined in Certificate.lean's
# Valid).
PYTHON_REJECTION_CASES: list[tuple[str, dict, str]] = [
    (
        "even_start_undefined",
        {"schema_version": "1.0", "start": 6, "steps": 1, "target": 11},
        ERR_TRAJECTORY_UNDEFINED,
    ),
    (
        "even_start_2_steps",
        {"schema_version": "1.0", "start": 4, "steps": 2, "target": 1},
        ERR_TRAJECTORY_UNDEFINED,
    ),
    (
        "not_descent_target_eq_start",
        {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1},
        ERR_NOT_DESCENT,
    ),
    (
        "ascent_target",
        {"schema_version": "1.0", "start": 3, "steps": 1, "target": 5},
        ERR_NOT_DESCENT,
    ),
    (
        "trajectory_mismatch",
        {"schema_version": "1.0", "start": 5, "steps": 1, "target": 999},
        ERR_TRAJECTORY_MISMATCH,
    ),
]


@skip_if_no_lake
@pytest.mark.parametrize("start,steps", VALID_CORPUS)
def test_checker_corpus_matches_lean_endpoint(tmp_path, start, steps) -> None:
    """The Python checker's accepted endpoint equals the Lean trajectory endpoint."""
    cert = build_descent_certificate(start, steps)
    path = tmp_path / "certificate.jsonl"
    path.write_bytes(write_jsonl([cert.as_dict()]))
    checked = check_certificate(path)

    lean_file = tmp_path / "CheckerFixture.lean"
    lean_file.write_text(
        "\n".join(
            [
                "import CollatzResearch.Certificate",
                "",
                f"#eval CollatzResearch.trajectory {checked.start} {checked.steps}",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    repo_root = Path(__file__).parents[1]
    result = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=repo_root,
        check=True,
        text=True,
        capture_output=True,
    )
    assert result.stdout.strip() == str(checked.target), (
        f"Lean endpoint mismatch for ({start}, {steps}): "
        f"Python={checked.target}, Lean={result.stdout.strip()}"
    )


@skip_if_no_lake
@pytest.mark.parametrize("start,steps", VALID_CORPUS)
def test_checker_corpus_full_trajectory_matches_lean(tmp_path, start, steps) -> None:
    """The full Python trajectory (each step) matches Lean's step-by-step trajectory."""
    cert = build_descent_certificate(start, steps)
    path = tmp_path / "certificate.jsonl"
    path.write_bytes(write_jsonl([cert.as_dict()]))
    checked = check_certificate(path)
    expected_trajectory = tuple(iterate(start, steps))

    lean_file = tmp_path / "CheckerFull.lean"
    # Build a Lean list literal of the trajectory: [(trajectory start 0), (trajectory start 1), ...]
    elements = ", ".join(
        f"CollatzResearch.trajectory {checked.start} {k}" for k in range(steps + 1)
    )
    lean_file.write_text(
        "\n".join(
            [
                "import CollatzResearch.Certificate",
                "",
                f"#eval [{elements}]",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    repo_root = Path(__file__).parents[1]
    result = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=repo_root,
        check=True,
        text=True,
        capture_output=True,
    )
    # Lean returns a list literal like "[1, 5, 1, 1]"; parse and compare element-wise.
    lean_output = result.stdout.strip()
    assert lean_output.startswith("[") and lean_output.endswith(
        "]"
    ), f"Unexpected Lean output for ({start}, {steps}): {lean_output!r}"
    lean_values = tuple(int(s.strip()) for s in lean_output[1:-1].split(",") if s.strip())
    assert lean_values == expected_trajectory, (
        f"Full trajectory mismatch for ({start}, {steps}): "
        f"Python={expected_trajectory}, Lean={lean_values}"
    )


@pytest.mark.parametrize(
    "case_name,record,expected_category",
    PYTHON_REJECTION_CASES,
    ids=[c[0] for c in PYTHON_REJECTION_CASES],
)
def test_checker_rejects_malformed_or_non_descent(
    tmp_path, case_name, record, expected_category
) -> None:
    """Python checker fails closed with stable rejection categories."""
    path = tmp_path / f"{case_name}.jsonl"
    path.write_bytes(write_jsonl([record]))

    with pytest.raises(CertificateCheckError) as exc_info:
        check_certificate(path)
    assert exc_info.value.category == expected_category, (
        f"{case_name}: expected category {expected_category}, " f"got {exc_info.value.category}"
    )
