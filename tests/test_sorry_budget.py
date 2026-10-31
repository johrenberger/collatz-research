import importlib.util
from pathlib import Path

_SCRIPT = Path(__file__).parents[1] / "scripts" / "check_sorry_budget.py"
_SPEC = importlib.util.spec_from_file_location("check_sorry_budget", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)


def test_current_tracked_admissions_stay_within_budget() -> None:
    assert _MODULE.main() == 0


def test_counts_bullet_form_hole() -> None:
    source = "theorem t : True := by\n  \u00b7 sorry\n"
    assert _MODULE.count_admissions(source) == 1


def test_counts_admit_and_axiom_holes() -> None:
    assert _MODULE.count_admissions("theorem t : True := by\n  admit\n") == 1
    assert _MODULE.count_admissions("axiom foo : True\n") == 1


def test_counts_axiom_modifier_forms() -> None:
    assert _MODULE.count_admissions("private axiom hidden : True\n") == 1
    assert _MODULE.count_admissions("protected axiom hidden : True\n") == 1
    assert _MODULE.count_admissions("namespace X\nprotected axiom hidden : True\nend X\n") == 1


def test_counts_opaque_declarations() -> None:
    assert _MODULE.count_admissions("opaque escapeHatch : True\n") == 1
    assert _MODULE.count_admissions("private opaque escapeHatch : True\n") == 1


def test_ignores_quoted_identifiers() -> None:
    # «sorry» is a user-chosen identifier, not the keyword.
    assert _MODULE.count_admissions("def «sorry» : Nat := 1\n") == 0
    assert _MODULE.count_admissions("def «opaque» : Nat := 1\n") == 0
    assert _MODULE.count_admissions("def x : Nat := «sorry»\n") == 0


def test_counts_admissions_inside_interpolation_holes() -> None:
    source = 'def interpolated : String := s!"{(by exact (sorry : Nat))}"\n'
    assert _MODULE.count_admissions(source) == 1
    assert _MODULE.count_admissions('def plain : String := "sorry"\n') == 0
    assert _MODULE.count_admissions('def ok : String := s!"{1}"\n') == 0


def test_ignores_comments_and_strings() -> None:
    source = (
        "-- sorry\n"
        "/- sorry -/\n"
        "/-! sorry -/\n"
        "/-- sorry -/\n"
        'theorem t : String := "sorry"\n'
    )
    assert _MODULE.count_admissions(source) == 0


def test_ignores_words_that_only_contain_an_admission() -> None:
    assert _MODULE.count_admissions("theorem t : Nat := sorryCount\n") == 0
    assert _MODULE.count_admissions("theorem t : Nat := 0 -- sorryAx\n") == 0
