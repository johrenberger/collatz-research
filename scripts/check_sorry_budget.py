#!/usr/bin/env python3
"""Enforce the exact Lean admission budget from Lean's own diagnostics.

The budget in `docs/lean-sorry-budget.json` is an exact per-file baseline of
admitted declarations. Two components feed the count.

1. `sorry` and `sorryAx` admissions are counted from Lean's own report.
   Elaborating a file with `lake env lean --json <file>` makes Lean emit one
   `hasSorry` diagnostic for every declaration that references `sorryAx` --
   the same signal Lean prints as "declaration uses sorry". Reading Lean's
   report instead of scanning the source text is what makes this gate sound:
   a custom elaborator can synthesise a `sorry` term without the word ever
   appearing in the source, and only Lean can see that. The count is per
   *declaration*: Lean reports one diagnostic per declaration, so three holes
   inside one declaration count as one admitted declaration.

2. `axiom` and `opaque` declarations are counted from the source text. Lean
   emits no diagnostic for them, and they are reserved Lean keywords, so a
   word-boundary match in a code position identifies the declaration --
   including the `private axiom`, `protected axiom` and `private opaque`
   modifier forms. Comments and string literals are stripped before matching.

`admit` and `sorryAx` are NOT reserved Lean keywords: `def admit : Nat := 1`
and `namespace User def sorryAx : Nat := 1` are legal Lean programs. The
lexical component therefore never counts them, and a real `sorryAx` use is
caught by the Lean diagnostic instead.

A file that Lean cannot elaborate at all is listed in the `not_elaborated`
section of the budget together with the reason. Such a file is outside the
trusted chain -- nothing can import a module that does not elaborate -- so
only the lexical component applies to it. The list is checked in both
directions: a file that newly stops elaborating fails the gate, and a
recorded file that elaborates again fails the gate until its entry is
removed and the recorded budget is updated.

The project has to be built before the gate runs: `lake env lean <file>`
elaborates that one file and loads its imports from the build cache, so a
file whose imports are not built fails the gate with an elaboration error.

The recorded budget is an exact baseline, not a ceiling:

  * more admitted declarations than recorded: new proof debt, rejected;
  * fewer than recorded: stale record, rejected (lower the recorded budget in
    the same change that closed the admissions).

Schema versions:
  1: line-anchored `sorry` count.
  2: exact hole baseline over code positions (lexical only).
  3: exact admitted-declaration baseline; `sorry`/`sorryAx` counted from
     Lean's own `hasSorry` diagnostics, `axiom`/`opaque` counted lexically.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).parents[1]
BASELINE = ROOT / "docs" / "lean-sorry-budget.json"
SCHEMA_VERSION = 3

# Lean's severity tag for a declaration that references `sorryAx`.
SORRY_KIND = "hasSorry"

# `axiom` and `opaque` are reserved Lean keywords.
KEYWORD_DECLARATION = re.compile(r"\b(?:axiom|opaque)\b")

LEAN_ROOT = ROOT / "Lean"

DEFAULT_JOBS = 2
DEFAULT_TIMEOUT = 900


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
        if src[i] == "\u00ab":
            # Quoted identifier: a user-chosen name, not the keyword.
            j = src.find("\u00bb", i + 1)
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


def count_keyword_declarations(text: str) -> int:
    """Count the lexically detectable admitted declarations in Lean source.

    Only `axiom` and `opaque` are counted here. `sorry` and `sorryAx` are
    counted from Lean's own diagnostics instead, because a lexical scan
    cannot see a `sorry` that an elaborator synthesised.
    """
    code = strip_comments_and_strings(text)
    return len(KEYWORD_DECLARATION.findall(code))


def lean_sorry_declarations(path: Path, timeout: int) -> tuple[int, list[str]]:
    """Elaborate one file with Lean and count its `hasSorry` diagnostics.

    Returns the number of admitted declarations Lean reported, plus a list
    of problems that make that number unreliable (an elaboration error, or a
    Lean invocation that failed outright).
    """
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "--json", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return 0, [f"{path.name}: Lean elaboration timed out after {timeout}s"]
    except OSError as exc:
        return 0, [f"{path.name}: could not run Lean: {exc}"]

    count = 0
    problems: list[str] = []
    for line in proc.stdout.splitlines() + proc.stderr.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(message, dict):
            continue
        if message.get("kind") == SORRY_KIND:
            count += 1
        elif message.get("severity") == "error":
            position = message.get("pos") or {}
            problems.append(
                f"{message.get('fileName', path.name)}:"
                f"{position.get('line', '?')}:{position.get('column', '?')}: "
                f"{message.get('data', 'elaboration error')}"
            )
    if not problems and proc.returncode != 0:
        problems.append(f"{path.name}: Lean exited with status {proc.returncode}")
    return count, problems


def _int_env(name: str, default: int) -> int:
    """Read a positive integer from the environment, falling back to default."""
    try:
        value = int(os.environ.get(name, default))
    except ValueError:
        return default
    return value if value > 0 else default


def main() -> int:
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    version = baseline.get("schema_version")
    if version != SCHEMA_VERSION:
        print(
            f"unsupported Lean admission budget schema {version!r} " f"(expected {SCHEMA_VERSION})",
            file=sys.stderr,
        )
        return 2
    expected = baseline["expected"]
    not_elaborated = baseline.get("not_elaborated", {})

    if shutil.which("lake") is None:
        print(
            "the Lean admission budget needs `lake` on PATH; "
            "install the Lean toolchain named in lean-toolchain",
            file=sys.stderr,
        )
        return 2

    timeout = _int_env("LEAN_ADMISSION_TIMEOUT", DEFAULT_TIMEOUT)
    jobs = min(_int_env("LEAN_ADMISSION_JOBS", DEFAULT_JOBS), os.cpu_count() or 1)

    failures: list[str] = []
    paths = sorted(LEAN_ROOT.rglob("*.lean"))
    known = {path.relative_to(ROOT).as_posix() for path in paths}
    for rel in sorted(not_elaborated):
        if rel not in known:
            failures.append(f"{rel}: recorded as not elaborable but the file does not exist")

    actual: dict[str, int] = {}
    if not failures:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            results = list(pool.map(lambda p: lean_sorry_declarations(p, timeout), paths))
        for path, (count, problems) in zip(paths, results, strict=True):
            rel = path.relative_to(ROOT).as_posix()
            lexical = count_keyword_declarations(path.read_text(encoding="utf-8"))
            if problems:
                if rel not in not_elaborated:
                    failures.extend(problems)
                    continue
                # A recorded non-elaborable module: the oracle cannot see
                # inside it, so only the lexical component applies.
                total = lexical
            else:
                if rel in not_elaborated:
                    failures.append(
                        f"{rel}: the budget records this file as not elaborable, "
                        "but Lean elaborates it now (drop the entry and "
                        "update the recorded budget)"
                    )
                    continue
                total = count + lexical
            if total:
                actual[rel] = total

    for rel, count in sorted(actual.items()):
        if rel not in expected:
            failures.append(f"{rel}: {count} admitted declarations are not tracked in the budget")
        elif count > expected[rel]:
            failures.append(
                f"{rel}: {count} admitted declarations exceed the recorded budget "
                f"{expected[rel]} (new proof debt)"
            )
        elif count < expected[rel]:
            failures.append(
                f"{rel}: {count} admitted declarations but the recorded budget is "
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
