"""Regression coverage for the transitive axiom audit.

The audit itself lives in `scripts/check_theorem_axioms.py` so that the
Lean CI job can run it without a pytest install, the way it already runs
`scripts/check_sorry_budget.py`. This module exposes its cases to
`make test`.
"""

import importlib.util
import json
import shutil
from pathlib import Path

import pytest

_SCRIPT = Path(__file__).parents[1] / "scripts" / "check_theorem_axioms.py"
_SPEC = importlib.util.spec_from_file_location("check_theorem_axioms", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)

LAKE_AVAILABLE = shutil.which("lake") is not None
skip_if_no_lake = pytest.mark.skipif(not LAKE_AVAILABLE, reason="Lean toolchain is not available")

KNOWN_TIERS = {
    "conditional_generic_theorem",
    "kernel_proof",
    "compiler_dependent_instance",
}


def _manifest() -> dict:
    return json.loads(_MODULE.MANIFEST.read_text(encoding="utf-8"))


def test_manifest_schema_is_current() -> None:
    """The recorded manifest uses the schema this script understands."""
    assert _manifest()["schema_version"] == _MODULE.SCHEMA_VERSION


def test_manifest_records_the_pinned_toolchain() -> None:
    """The manifest is a snapshot of one toolchain, and says which."""
    toolchain = _MODULE.TOOLCHAIN.read_text(encoding="utf-8").strip()
    assert _manifest()["toolchain"] == toolchain


def test_every_recorded_result_has_a_known_tier() -> None:
    """Each recorded result is classified and uses only approved axioms."""
    manifest = _manifest()
    assert manifest["results"]
    approved = set(manifest["approved_axioms"])
    for entry in manifest["results"]:
        assert entry["tier"] in KNOWN_TIERS, entry["name"]
        assert set(entry["approved_axioms"]) <= approved, entry["name"]


def test_every_exported_reachability_result_is_recorded() -> None:
    """No exported reachability result escapes the manifest.

    A theorem that concludes `ReachesOne` and is missing from the
    manifest is a result whose trusted base was never recorded, so the
    audit would not cover it.
    """
    recorded = {entry["name"] for entry in _manifest()["results"]}
    missing = [decl["name"] for decl in _MODULE.discover() if decl["name"] not in recorded]
    assert not missing, f"unrecorded exported reachability results: {missing}"


def test_scanner_drops_no_declaration_it_matches() -> None:
    """The scanner must return every declaration the pattern matches.

    A declaration whose first line already ends its type is complete on
    that line. If the scanner consumed further lines anyway, the
    declaration after it would be swallowed, and a reachability theorem
    could escape the audit without a manifest entry.
    """
    declarations = _MODULE.scan_declarations()
    found = {decl["location"] for decl in declarations}
    expected = set()
    for path in sorted(_MODULE.LEAN_ROOT.rglob("*.lean")):
        rel = path.relative_to(_MODULE.ROOT).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        for index, line in enumerate(lines):
            if _MODULE.DECL_RE.match(line):
                expected.add(f"{rel}:{index + 1}")
    assert found == expected, f"declarations dropped by the scanner: {sorted(expected - found)}"


def test_one_line_declaration_does_not_swallow_the_next(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A one-line declaration must not consume the declaration after it."""
    lean_dir = tmp_path / "Lean" / "CollatzResearch"
    lean_dir.mkdir(parents=True)
    (lean_dir / "ScannerFixture.lean").write_text(
        "namespace CollatzResearch\n"
        "def oneLiner : Nat := 0\n"
        "theorem reaches_one : ReachesOne 1 1\n"
        "end CollatzResearch\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(_MODULE, "ROOT", tmp_path)
    monkeypatch.setattr(_MODULE, "LEAN_ROOT", tmp_path / "Lean")
    names = {decl["name"] for decl in _MODULE.scan_declarations()}
    assert "CollatzResearch.oneLiner" in names
    assert "CollatzResearch.reaches_one" in names


@skip_if_no_lake
def test_gate_self_test_cases() -> None:
    """A clean proof, an admitted proof, and two native shapes are checked."""
    failures = _MODULE.run_selftest()
    assert not failures, "\n".join(failures)


@skip_if_no_lake
def test_recorded_manifest_matches_a_fresh_measurement() -> None:
    """The recorded trusted base still matches what Lean reports."""
    failures = _MODULE.verify(_manifest())
    assert not failures, "\n".join(failures)
