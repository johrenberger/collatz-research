#!/usr/bin/env python3
"""Regression checks for the Lean admission oracle.

Each case writes a small Lean fixture, elaborates it with Lean, and checks
that the admission oracle reports exactly the admitted declarations that Lean
itself reports.  The script has no pytest dependency so that the Lean CI job
can run it directly:

    python3 scripts/check_admission_oracle.py

The cases cover the failure modes a lexical scan cannot handle: a `sorry`
that an elaborator synthesises without the word appearing in the source, the
modifier forms of `axiom` and `opaque`, and the legal Lean identifiers
`admit` and `sorryAx` that a word-boundary scan used to count.
"""

from __future__ import annotations

import importlib.util
import re
import shutil
import sys
import tempfile
from pathlib import Path

_CHECKER = Path(__file__).with_name("check_sorry_budget.py")
_SPEC = importlib.util.spec_from_file_location("check_sorry_budget", _CHECKER)
assert _SPEC and _SPEC.loader
_CHECK = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_CHECK)

# A custom elaborator that synthesises a `sorry` term.  The word `sorry`
# never appears in this source, so no lexical scan of the file can see the
# admission -- only Lean can.
MACRO_SORRY = """import Lean

open Lean Elab Term in
elab "redacted" : term => do
  let e ← Lean.Meta.mkSorry (Lean.mkConst ``True) (synthetic := false)
  pure e

theorem sneaky : True := redacted
"""

# (name, source, expected Lean `hasSorry` count, expected lexical count)
CASES: list[tuple[str, str, int, int]] = [
    (
        "plain sorry",
        "theorem t : True := by\n  sorry\n",
        1,
        0,
    ),
    (
        "bullet sorry",
        "theorem t : True := by\n  · sorry\n",
        1,
        0,
    ),
    (
        "three holes in one declaration",
        "theorem t : True ∧ True ∧ True := by\n"
        "  refine ⟨?_, ?_, ?_⟩\n"
        "  · sorry\n  · sorry\n  · sorry\n",
        1,
        0,
    ),
    (
        "two admitted declarations",
        "theorem a : True := by\n  sorry\n\ntheorem b : True := by\n  sorry\n",
        2,
        0,
    ),
    (
        "macro generated sorry",
        MACRO_SORRY,
        1,
        0,
    ),
    (
        "legal identifiers",
        "def admit : Nat := 1\n\nnamespace UserChosen\ndef sorryAx : Nat := 1\nend UserChosen\n",
        0,
        0,
    ),
    (
        "comments and strings",
        '-- sorry\n/- opaque escape : True -/\ndef msg : String := "axiom foo : True"\n',
        0,
        0,
    ),
    (
        "private axiom",
        "private axiom hidden : True\n",
        0,
        1,
    ),
    (
        "opaque declaration",
        "opaque escapeHatch : True\n",
        0,
        1,
    ),
]

DEFAULT_TIMEOUT = 600


def run_case(
    name: str,
    source: str,
    expected_sorry: int,
    expected_lexical: int,
    workdir: Path,
) -> list[str]:
    """Elaborate one fixture and return a list of failure messages."""
    path = workdir / f"{name.replace(' ', '_')}.lean"
    path.write_text(source, encoding="utf-8")
    count, problems = _CHECK.lean_sorry_declarations(path, DEFAULT_TIMEOUT)
    lexical = _CHECK.count_keyword_declarations(source)
    failures: list[str] = []
    if problems:
        failures.append(f"{name}: Lean could not elaborate the fixture: {'; '.join(problems)}")
        return failures
    if count != expected_sorry:
        failures.append(
            f"{name}: Lean reported {count} admitted declarations, " f"expected {expected_sorry}"
        )
    if lexical != expected_lexical:
        failures.append(
            f"{name}: the lexical component counted {lexical}, " f"expected {expected_lexical}"
        )
    return failures


def main() -> int:
    if shutil.which("lake") is None:
        print(
            "the admission oracle regression checks need `lake` on PATH",
            file=sys.stderr,
        )
        return 2
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        for name, source, expected_sorry, expected_lexical in CASES:
            failures.extend(run_case(name, source, expected_sorry, expected_lexical, workdir))
    if re.search(r"\bsorry\b", MACRO_SORRY):
        failures.append(
            "the macro fixture must not contain the word `sorry` in its source: "
            "a lexical scan of it must not be able to find the admission"
        )
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"admission oracle regression checks passed ({len(CASES)} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
