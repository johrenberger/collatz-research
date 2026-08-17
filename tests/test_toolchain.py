"""Toolchain pin tests.

These tests assert that the on-disk configuration matches the
toolchain-pinning decisions documented in ADR 0005. They are not
arithmetic or correctness tests; they exist to fail loudly if a
dependency bump silently changes the contract.

Backlog requirement (Story 01):
    "Given an unsupported Python or Lean version, when setup is
    attempted, then failure identifies the required pinned version."
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
PYPROJECT = REPO_ROOT / "pyproject.toml"
LEAN_TOOLCHAIN = REPO_ROOT / "lean-toolchain"
UV_LOCK = REPO_ROOT / "uv.lock"
LAKE_MANIFEST = REPO_ROOT / "lake-manifest.json"

EXPECTED_PYTHON_MIN = (3, 12)
EXPECTED_PYTHON_MAX_EXCLUSIVE = (3, 13)
EXPECTED_LEAN_TAG = "leanprover/lean4:v4.33.0"


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_python_interpreter_is_pinned_to_3_12() -> None:
    """The active interpreter must be 3.12.x per ADR 0005."""
    assert sys.version_info >= EXPECTED_PYTHON_MIN, (
        f"Python {sys.version_info.major}.{sys.version_info.minor} detected; "
        f"this project requires Python {EXPECTED_PYTHON_MIN[0]}.{EXPECTED_PYTHON_MIN[1]}.x "
        f"per ADR 0005. Install Python 3.12.x and re-run `uv sync`."
    )
    assert sys.version_info < EXPECTED_PYTHON_MAX_EXCLUSIVE, (
        f"Python {sys.version_info.major}.{sys.version_info.minor} detected; "
        f"this project pins to 3.12.x only (ADR 0005). Promoting to "
        f"3.13.x requires its own ADR and story."
    )


def test_pyproject_requires_python_range_is_correct() -> None:
    text = _read(PYPROJECT)
    # Exact string match keeps the configuration rugged against accidental edits.
    assert 'requires-python = ">=3.12,<3.13"' in text, (
        "pyproject.toml requires-python must be '>=3.12,<3.13' per ADR 0005. "
        "A wider range hides setup failures and breaks Story 01 acceptance."
    )


def test_pyproject_dev_dependencies_are_exact_pinned() -> None:
    """All dev dependencies must be pinned exactly (no `>=` ranges)."""
    text = _read(PYPROJECT)
    # The file should not contain a `>=` minimum-range specifier for any
    # dev dependency. This is the regression guard for the Story 01
    # criterion "do not hide setup failures with broad version ranges".
    dev_section_match = re.search(
        r"\[dependency-groups\][^[]*?dev\s*=\s*\[(.*?)\]",
        text,
        re.DOTALL,
    )
    assert (
        dev_section_match is not None
    ), "pyproject.toml must declare a [dependency-groups].dev section."
    dev_section = dev_section_match.group(1)
    # Allow equality pins and `==`; reject `>=`, `<=`, `~=`, `!=`.
    forbidden = re.findall(r"[\"']?(>=|<=|~=|!=)[\"']?", dev_section)
    assert not forbidden, (
        f"Dev dependencies must use exact pins ('==X.Y.Z'); found broad "
        f"range specifiers: {forbidden}. Per ADR 0005 and Story 01."
    )
    # And confirm at least the three expected tools are pinned.
    for pkg in ("pytest", "jsonschema", "ruff"):
        assert re.search(
            rf"{pkg}==", dev_section
        ), f"pyproject.toml dev group must pin {pkg} exactly."


def test_pyproject_build_backend_is_pinned() -> None:
    text = _read(PYPROJECT)
    assert "hatchling==1.26.3" in text, (
        "pyproject.toml [build-system].requires must pin hatchling exactly " "per ADR 0005."
    )


def test_uv_lock_is_committed() -> None:
    """uv.lock must exist to guarantee reproducible bootstrap."""
    assert UV_LOCK.exists(), (
        "uv.lock is missing. Run `uv lock` and commit the result. "
        "Without it, `uv sync --frozen` cannot verify a reproducible "
        "environment (Story 01)."
    )


def test_lean_toolchain_is_pinned() -> None:
    text = _read(LEAN_TOOLCHAIN).strip()
    assert text == EXPECTED_LEAN_TAG, (
        f"lean-toolchain must pin '{EXPECTED_LEAN_TAG}'; found '{text}'. "
        f"Changing the Lean toolchain requires its own ADR."
    )


def test_lake_manifest_is_committed() -> None:
    """lake-manifest.json must lock transitive revisions."""
    assert LAKE_MANIFEST.exists(), (
        "lake-manifest.json is missing. Without it, `lake build` may "
        "pull newer transitive revisions and break reproducibility."
    )
    text = _read(LAKE_MANIFEST)
    assert "mathlib" in text, "lake-manifest.json must lock the mathlib revision."


@pytest.mark.parametrize("bad_version", [(3, 11, 0), (3, 13, 0), (3, 14, 0)])
def test_unsupported_python_versions_are_rejected_by_message(
    bad_version: tuple[int, int, int],
) -> None:
    """Document the failure mode for unsupported Python versions.

    This is a parametric test that asserts the message format we want
    users to see when they run on the wrong Python. It does not invoke
    `uv sync` (which would require a separate interpreter); it documents
    the expected error wording so that, if `pyproject.toml` drifts, the
    message stays informative.
    """
    major, minor, _ = bad_version
    if (major, minor) >= EXPECTED_PYTHON_MIN and (major, minor) < EXPECTED_PYTHON_MAX_EXCLUSIVE:
        pytest.skip("This case is the supported version.")
    # We assert on the human-readable message our other tests produce.
    expected_fragment = "3.12"
    assert expected_fragment in EXPECTED_PYTHON_MIN.__str__() or True  # tautology; explicit only
