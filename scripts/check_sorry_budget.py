#!/usr/bin/env python3
"""Reject increases in tracked Lean proof admissions.

An admission is a declaration Lean accepted without checking its content:
a `sorry` hole, an `admit` placeholder, an `axiom` declaration, a direct
use of `sorryAx`, or an `opaque` declaration. Only code positions count.
Lean block comments (nested), line comments, and string literals are
stripped first, so prose never counts while a bullet-form hole does.

`sorry`, `admit`, `sorryAx`, `axiom`, and `opaque` are reserved Lean
keywords, so outside a quoted identifier (`«sorry»`) every occurrence of
one in code is a declaration -- including the `private axiom`,
`protected axiom`, and `private opaque` modifier forms. A quoted identifier
is a user-chosen name and is skipped. `opaque` is counted because it hides the value
from the kernel: it
is discharged through an `Inhabited`/`Nonempty` instance, and for a
proposition `Nonempty p` is classically equivalent to `p`, so an opaque
declaration can hide a proposition proof from review.

Interpolated string literals (`s!"..."` and friends) embed Lean code in
`{...}` holes, so those holes are scanned as code while the surrounding
literal text is discarded. Without that, a `sorry` inside an interpolation
hole would be invisible even though Lean itself reports "declaration uses
`sorry`" for it.

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

ADMISSION = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|opaque)\b")


def _scan_string(src: str, i: int, interpolated: bool) -> tuple[int, str]:
    """Scan a string literal starting at the opening quote.

    Returns the index just past the literal and the code it contributes.
    A plain literal contributes nothing. An interpolated literal contributes
    the code of its holes, with comments and nested literals stripped.
    """
    n = len(src)
    out: list[str] = []
    i += 1
    while i < n:
        ch = src[i]
        if ch == "\\":
            i += 2
            out.append(" ")
            continue
        if ch == '"':
            i += 1
            return i, "".join(out)
        if interpolated and ch == "{":
            if src[i + 1 : i + 2] == "{":
                # Escaped literal brace, not a hole.
                i += 2
                out.append("  ")
                continue
            hole, i = _scan_hole(src, i)
            # Separate from adjacent literal text: without the spaces the
            # hole content would be glued onto the preceding characters and
            # a leading keyword would miss its word boundary.
            out.append(" " + strip_comments_and_strings(hole) + " ")
            continue
        out.append(" ")
        i += 1
    return i, "".join(out)


def _scan_hole(src: str, i: int) -> tuple[str, int]:
    """Scan an interpolation hole starting at a brace. Returns text and index."""
    n = len(src)
    depth = 1
    start = i + 1
    i += 1
    while i < n:
        two = src[i : i + 2]
        if two == "/-":
            inner = 1
            j = i + 2
            while j < n and inner:
                if src.startswith("/-", j):
                    inner += 1
                    j += 2
                elif src.startswith("-/", j):
                    inner -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j, _ = _scan_string(src, i, src[i - 1 : i] == "!")
            i = j
            continue
        if src[i] == "{":
            depth += 1
            i += 1
            continue
        if src[i] == "}":
            depth -= 1
            if depth == 0:
                return src[start:i], i + 1
            i += 1
            continue
        i += 1
    return src[start:i], i


def strip_comments_and_strings(src: str) -> str:
    """Return src with comments and string literals reduced to code only.

    Lean block comments nest, line comments run to end of line, and plain
    string literals hold data only. Interpolated string literals embed Lean
    code in holes, so those holes are kept as code.
    """
    out: list[str] = []
    i = 0
    n = len(src)
    while i < n:
        two = src[i : i + 2]
        if two == "/-":
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
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            out.append(" ")
            continue
        if two == '!"':
            # Interpolated literal: the identifier prefix ends in a bang.
            i, text = _scan_string(src, i + 1, True)
            out.append(text)
            continue
        if src[i] == "«":
            # Quoted identifier: a user-chosen name, not the keyword.
            j = src.find("»", i + 1)
            j = n if j < 0 else j + 1
            out.append(" " * (j - i))
            i = j
            continue
        if src[i] == '"':
            i, text = _scan_string(src, i, False)
            out.append(text)
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
