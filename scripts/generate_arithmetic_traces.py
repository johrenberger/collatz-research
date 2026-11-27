"""Generate the concrete Lean trace fixtures for story R04.

The numbers in the generated Lean module come from the untrusted Python
reference arithmetic. Lean re-checks every equation with the kernel, and the
acceptance theorems in ArithmeticWitnessTests prove that the accepted traces
are the canonical accelerated trajectories. The generator contributes data,
never a proof.

The output is deterministic: the same inputs produce a byte-identical file.
The --check mode verifies that the committed file is current, which is what
keeps the generated Lean terms reproducible in CI.

Usage:
    python3 scripts/generate_arithmetic_traces.py           # write the file
    python3 scripts/generate_arithmetic_traces.py --check   # verify it is current
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

from collatz_research.arithmetic_trace import (  # noqa: E402
    ArithmeticTrace,
    build_trace,
    trace_to_one,
)

TARGET = ROOT / "Lean" / "CollatzResearch" / "ArithmeticWitnessTraces.lean"

HEADER = """import CollatzResearch.ArithmeticWitness

/-!
# Concrete arithmetic trace fixtures (story R04)

This module is **generated** by `scripts/generate_arithmetic_traces.py`.
Regenerate it with that script; do not edit it by hand.

The numbers below come from the untrusted Python reference arithmetic. Lean
re-checks every equation in `CollatzResearch.ArithmeticWitness`, and the
acceptance theorems in `ArithmeticWitnessTests` prove that the accepted
traces are the canonical accelerated trajectories.

The generator is deterministic: the same inputs produce a byte-identical file.
-/

namespace CollatzResearch
"""


def render_steps(trace: ArithmeticTrace) -> str:
    """Render the steps of a trace as a Lean list of StepWitness values."""
    if not trace.steps:
        return "[]"
    entries = ", ".join(f"⟨{s.exponent}, {s.successor}⟩" for s in trace.steps)
    return f"[{entries}]"


def render_trace(name: str, summary: str, trace: ArithmeticTrace) -> str:
    """Render one trace as a Lean TraceWitness definition."""
    lines = [f"/-- {summary} -/", f"def {name} : TraceWitness :=", f"  {{ start := {trace.start}"]
    lines.append(f"    steps := {render_steps(trace)}")
    lines.append(f"    endpoint := {trace.endpoint} }}")
    return "\n".join(lines)


def render_module() -> str:
    """Render the whole generated Lean module."""
    three = build_trace(3, 2)
    twenty_seven = trace_to_one(27)

    blocks = [
        render_trace(
            "traceThreeFiveOne",
            "The odd trajectory 3 -> 5 -> 1, two accelerated steps.",
            three,
        ),
        render_trace(
            "traceTwentySeven",
            f"The trajectory from 27: {len(twenty_seven.steps)} accelerated steps to 1.",
            twenty_seven,
        ),
    ]
    return "\n\n".join([HEADER, *blocks]) + "\n\nend CollatzResearch\n"


def main(argv: list[str] | None = None) -> int:
    """Write or check the generated module."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that the committed file matches the generated output",
    )
    args = parser.parse_args(argv)

    rendered = render_module()
    if args.check:
        if not TARGET.exists():
            print(f"missing {TARGET.relative_to(ROOT)}", file=sys.stderr)
            return 1
        current = TARGET.read_text(encoding="utf-8")
        if current != rendered:
            print(
                f"{TARGET.relative_to(ROOT)} is stale; regenerate it with "
                "scripts/generate_arithmetic_traces.py",
                file=sys.stderr,
            )
            return 1
        print(f"{TARGET.relative_to(ROOT)} is up to date")
        return 0

    TARGET.write_text(rendered, encoding="utf-8")
    print(f"wrote {TARGET.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
