import importlib.util
from pathlib import Path

_SCRIPT = Path(__file__).parents[1] / "scripts" / "check_sorry_budget.py"
_SPEC = importlib.util.spec_from_file_location("check_sorry_budget", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)


def test_current_tracked_admissions_stay_within_budget() -> None:
    assert _MODULE.main() == 0
