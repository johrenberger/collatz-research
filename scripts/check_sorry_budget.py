#!/usr/bin/env python3
"""Reject increases in tracked Lean `sorry` declarations."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).parents[1]
BASELINE = ROOT / "docs" / "lean-sorry-budget.json"
SORRY = re.compile(r"^\s*sorry\b")


def count_sorries(path: Path) -> int:
    return sum(bool(SORRY.search(line)) for line in path.read_text(encoding="utf-8").splitlines())


def main() -> int:
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    if baseline.get("schema_version") != 1:
        print("unsupported Lean sorry budget schema", file=sys.stderr)
        return 2
    allowed = baseline["allowed"]
    actual = {
        path.relative_to(ROOT).as_posix(): count_sorries(path)
        for path in (ROOT / "Lean").rglob("*.lean")
    }
    failures = [
        f"{path}: {actual.get(path, 0)} admissions exceed budget {limit}"
        for path, limit in sorted(allowed.items())
        if actual.get(path, 0) > limit
    ]
    untracked = {path: count for path, count in actual.items() if count and path not in allowed}
    failures.extend(
        f"{path}: {count} untracked admissions" for path, count in sorted(untracked.items())
    )
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("Lean admission budget respected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
