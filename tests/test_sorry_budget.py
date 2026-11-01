import importlib.util
import json
import shutil
from pathlib import Path

import pytest

_SCRIPT = Path(__file__).parents[1] / "scripts" / "check_sorry_budget.py"
_SPEC = importlib.util.spec_from_file_location("check_sorry_budget", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)


def test_current_tracked_admissions_stay_within_budget() -> None:
    """The recorded budget matches what Lean's own diagnostics report."""
    if shutil.which("lake") is None:
        pytest.skip("Lean toolchain is not available")
    assert _MODULE.main() == 0


def test_budget_schema_is_current() -> None:
    baseline = json.loads(_MODULE.BASELINE.read_text(encoding="utf-8"))
    assert baseline["schema_version"] == _MODULE.SCHEMA_VERSION


def test_every_tracked_module_exists() -> None:
    baseline = json.loads(_MODULE.BASELINE.read_text(encoding="utf-8"))
    root = Path(__file__).parents[1]
    for rel in baseline["expected"]:
        assert (root / rel).is_file(), rel


def test_every_not_elaborated_module_exists() -> None:
    baseline = json.loads(_MODULE.BASELINE.read_text(encoding="utf-8"))
    root = Path(__file__).parents[1]
    for rel in baseline.get("not_elaborated", {}):
        assert (root / rel).is_file(), rel


def test_counts_axiom_declarations() -> None:
    assert _MODULE.count_keyword_declarations("axiom foo : True\n") == 1


def test_counts_axiom_modifier_forms() -> None:
    assert _MODULE.count_keyword_declarations("private axiom hidden : True\n") == 1
    assert _MODULE.count_keyword_declarations("protected axiom hidden : True\n") == 1
    assert (
        _MODULE.count_keyword_declarations("namespace X\nprotected axiom hidden : True\nend X\n")
        == 1
    )


def test_counts_opaque_declarations() -> None:
    assert _MODULE.count_keyword_declarations("opaque escapeHatch : True\n") == 1
    assert _MODULE.count_keyword_declarations("private opaque escapeHatch : True\n") == 1


def test_ignores_quoted_identifiers() -> None:
    # A quoted identifier is a user-chosen name, not the keyword.
    assert _MODULE.count_keyword_declarations("def «axiom» : Nat := 1\n") == 0
    assert _MODULE.count_keyword_declarations("def «opaque» : Nat := 1\n") == 0
    assert _MODULE.count_keyword_declarations("def x : Nat := «axiom»\n") == 0


def test_ignores_comments_and_strings() -> None:
    assert _MODULE.count_keyword_declarations("-- axiom foo : True\n") == 0
    assert _MODULE.count_keyword_declarations("/- opaque foo : True -/\n") == 0
    assert _MODULE.count_keyword_declarations('def msg : String := "axiom foo : True"\n') == 0


def test_does_not_count_admit_or_sorryax_identifiers() -> None:
    # `admit` and `sorryAx` are legal Lean identifiers, not admissions.
    assert _MODULE.count_keyword_declarations("def admit : Nat := 1\n") == 0
    assert (
        _MODULE.count_keyword_declarations(
            "namespace UserChosen\ndef sorryAx : Nat := 1\nend UserChosen\n"
        )
        == 0
    )


def test_does_not_count_sorry_lexically() -> None:
    # `sorry` admissions are counted from Lean's own diagnostics, never from
    # the source text: a lexical scan cannot see a synthesised `sorry`.
    assert _MODULE.count_keyword_declarations("theorem t : True := by\n  sorry\n") == 0
    assert _MODULE.count_keyword_declarations("theorem t : True := by\n  · sorry\n") == 0
