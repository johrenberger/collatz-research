"""Regression coverage for the Lean admission oracle.

The checks live in `scripts/check_admission_oracle.py` so that the Lean CI
job can run them without a pytest install; this module exposes them as
pytest cases for `make test`.
"""

import importlib.util
import shutil
from pathlib import Path

import pytest

_SCRIPT = Path(__file__).parents[1] / "scripts" / "check_admission_oracle.py"
_SPEC = importlib.util.spec_from_file_location("check_admission_oracle", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)

LAKE_AVAILABLE = shutil.which("lake") is not None
skip_if_no_lake = pytest.mark.skipif(not LAKE_AVAILABLE, reason="Lean toolchain is not available")


@skip_if_no_lake
@pytest.mark.parametrize(
    "name,source,expected_sorry,expected_lexical",
    _MODULE.CASES,
    ids=[case[0] for case in _MODULE.CASES],
)
def test_admission_oracle_case(tmp_path, name, source, expected_sorry, expected_lexical) -> None:
    failures = _MODULE.run_case(name, source, expected_sorry, expected_lexical, tmp_path)
    assert not failures, "\n".join(failures)


@skip_if_no_lake
def test_macro_fixture_is_invisible_to_a_lexical_scan() -> None:
    """The fixture must not contain the admission substring in any casing."""
    assert "sorry" not in _MODULE.MACRO_SORRY.lower()
