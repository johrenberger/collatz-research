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
        code = _MODULE.blank_comments("\n".join(lines)).splitlines()
        for index, line in enumerate(code):
            if _MODULE.DECL_RE.match(line.lstrip()):
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


def test_indented_declaration_is_discovered(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A declaration indented inside a namespace is discovered.

    Lean does not require a top-level declaration to start at column
    zero. A reachability theorem written with an indentation would
    otherwise stay out of discovery, and the completeness gate would
    pass without recording or auditing it.
    """
    lean_dir = tmp_path / "Lean" / "CollatzResearch"
    lean_dir.mkdir(parents=True)
    (lean_dir / "IndentedFixture.lean").write_text(
        "namespace CollatzResearch\n"
        "  theorem indented_reaches_one : ReachesOne 1 1 := by sorry\n"
        "end CollatzResearch\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(_MODULE, "ROOT", tmp_path)
    monkeypatch.setattr(_MODULE, "LEAN_ROOT", tmp_path / "Lean")
    names = {decl["name"] for decl in _MODULE.scan_declarations()}
    assert "CollatzResearch.indented_reaches_one" in names


def test_declaration_inside_a_comment_is_not_discovered(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A declaration keyword inside a comment is not a declaration.

    The scanner matches the declaration keyword anywhere on the line,
    so a comment that quotes a theorem must be blanked out first.
    """
    lean_dir = tmp_path / "Lean" / "CollatzResearch"
    lean_dir.mkdir(parents=True)
    (lean_dir / "CommentFixture.lean").write_text(
        "namespace CollatzResearch\n"
        "  /- theorem quoted_reaches_one : ReachesOne 1 1 := by sorry -/\n"
        "end CollatzResearch\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(_MODULE, "ROOT", tmp_path)
    monkeypatch.setattr(_MODULE, "LEAN_ROOT", tmp_path / "Lean")
    names = {decl["name"] for decl in _MODULE.scan_declarations()}
    assert "CollatzResearch.quoted_reaches_one" not in names


def test_binder_style_hypothesis_is_conditional() -> None:
    """A hypothesis written as a binder still makes a result conditional.

    Lean usually writes a hypothesis as a binder rather than as an
    arrow in the type, so the classification comes from the elaborated
    environment.
    """
    assert _MODULE.is_conditional(1, 0, 0) is True
    assert _MODULE.is_conditional(2, 0, 0) is True
    assert _MODULE.is_conditional(0, 0, 0) is False


def test_instance_implicit_proposition_is_a_premise() -> None:
    """An instance-implicit proposition is a premise unless synthesis supplies it.

    A binder of the form `[h : Fact p]` needs a proof of `p` from the
    caller, because instance synthesis cannot conjure one, so the result
    carries a hypothesis. An instance that synthesis does supply carries
    none.
    """
    assert _MODULE.is_conditional(1, 1, 1) is True
    assert _MODULE.is_conditional(1, 1, 0) is False


def test_binder_style_result_is_recorded_as_conditional() -> None:
    """A result whose hypothesis is a binder is recorded as conditional.

    `acceleratedStep_odd_of_odd` takes its hypothesis as a binder, so
    the recorded tier must not be the unconditional one.
    """
    entries = {entry["name"]: entry for entry in _manifest()["results"]}
    name = "CollatzResearch.acceleratedStep_odd_of_odd"
    assert entries[name]["tier"] == "conditional_generic_theorem"


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
