#!/usr/bin/env python3
"""Reject increases in tracked Lean proof admissions.

An admission is an unproven obligation in Lean source: a `sorry` hole, an
`admit` placeholder, an `axiom` declaration, or a direct use of `sorryAx`.
Only code positions count. Lean block comments (nested), line comments, and
string literals are stripped first, so prose never counts while a
bullet-form hole does. `axiom` is a reserved Lean keyword, so every
occurrence of it in code is a declaration -- including the `private axiom`
and `protected axiom` modifier forms.

The recorded budget in `docs/lean-sorry-budget.json` is an exact baseline,
not a ceiling. Every tracked file must hold exactly the number of
admissions recorded for it, and every Lean file that is not tracked must
hold none:

  * more admissions than recorded: new proof debt, rejected;
  * fewer admissions than recorded: stale record, rejected (lower the
    recorded budget in the same change that closed the admissions).

Counting unit: one admission hole. The Lean warning for a sorry-bearing
declaration counts declarations, so three holes in one declaration produce
one warning; this counter reports three, which is the number of unproven
obligations the project tracks.

Schema versions:
  1: line-anchored `sorry` count. Blind to bullet-form holes, blind to
     comments and strings, and tolerant of per-file headroom.
  2: exact hole baseline over code positions (current).
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).parents[1]
BASELINE = ROOT / "docs" / "lean-sorry-budget.json"
SCHEMA_VERSION = 2

ADMISSION = re.compile(r"\b(?:sorry|sorryAx|admit|axiom)\b")


def strip_comments_and_strings(src: str) -> str:
    """Return src with comments and string literals blanked out.

    Block comments nest in Lean, so they are matched by depth. A string
    literal is consumed whole, so a comment marker or a quote inside it
    cannot start a comment or end the string early.
    """
    out: list[str] = []
    i = 0
    n = len(src)
    while i < n:
        if src[i] == '"':
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
            out.append(" ")
            continue
        if src.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            out.append(" ")
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            out.append(" ")
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def count_admissions(text: str) -> int:
    """Count admitted proof holes in Lean source."""
    code = strip_comments_and_strings(text)
    return len(ADMISSION.findall(code))


def main() -> int:
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    version = baseline.get("schema_version")
    if version != SCHEMA_VERSION:
        print(
            f"unsupported Lean admission budget schema {version!r}" f" (expected {SCHEMA_VERSION})",
            file=sys.stderr,
        )
        return 2
    expected = baseline["expected"]
    actual: dict[str, int] = {}
    for path in sorted((ROOT / "Lean").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        count = count_admissions(path.read_text(encoding="utf-8"))
        if count:
            actual[rel] = count

    failures: list[str] = []
    for rel, count in sorted(actual.items()):
        if rel not in expected:
            failures.append(f"{rel}: {count} admissions are not tracked in the budget")
        elif count > expected[rel]:
            failures.append(
                f"{rel}: {count} admissions exceed the recorded budget "
                f"{expected[rel]} (new proof debt)"
            )
        elif count < expected[rel]:
            failures.append(
                f"{rel}: {count} admissions but the recorded budget is "
                f"{expected[rel]} (lower the recorded budget)"
            )
    for rel, count in sorted(expected.items()):
        if count and rel not in actual:
            failures.append(
                f"{rel}: the recorded budget is {count} but no admissions remain "
                "(lower the recorded budget)"
            )

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("Lean admission budget respected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
