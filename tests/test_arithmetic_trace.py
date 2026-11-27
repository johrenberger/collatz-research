"""Tests for the untrusted arithmetic-trace producer (story R04).

These tests cover the Python half of the R04 boundary: the raw numbers the
producer emits, the arithmetic equations those numbers must satisfy, and the
rejection of malformed input. The Lean side re-checks every equation; these
tests check that the producer is well-behaved and deterministic, which is
what makes the generated Lean terms reproducible.

No test here asserts a convergence claim. A bound that is hit is an unknown
outcome, never a negative universal conclusion.
"""

from __future__ import annotations

import pytest
from collatz_research.arithmetic_trace import (
    ArithmeticStep,
    accelerated_step_witness,
    build_trace,
    lean_step_list,
    lean_trace,
    trace_to_one,
    trace_values,
    witness_matches_reference,
)


def test_step_witness_equation_holds():
    """Every generated step satisfies its own arithmetic equation."""
    for value in (1, 3, 5, 7, 27, 41, 97):
        witness = accelerated_step_witness(value)
        assert witness.equation_holds(value)


def test_step_witness_matches_reference_implementation():
    """The witness encoding agrees with the reference accelerated step."""
    for value in (1, 3, 5, 7, 27, 41, 97, 111, 223):
        assert witness_matches_reference(value)


def test_three_five_one_trace():
    """The trace 3 -> 5 -> 1 has the expected raw numbers."""
    trace = build_trace(3, 2)
    assert trace.start == 3
    assert trace.steps == (ArithmeticStep(1, 5), ArithmeticStep(4, 1))
    assert trace.endpoint == 1
    assert trace.equation_holds()
    assert trace.values() == [3, 5, 1]


def test_twenty_seven_trace_reaches_one():
    """The trace from 27 reaches 1 and satisfies every equation."""
    trace = trace_to_one(27)
    assert trace.start == 27
    assert trace.endpoint == 1
    assert trace.equation_holds()
    assert len(trace.steps) == 41


def test_zero_step_trace_is_empty():
    """The zero-step trace for input 1 carries no steps."""
    trace = build_trace(1, 0)
    assert trace.steps == ()
    assert trace.endpoint == 1
    assert trace.equation_holds()


def test_build_trace_rejects_even_start():
    """An even start is refused: the accelerated map needs an odd input."""
    with pytest.raises(ValueError):
        build_trace(2, 1)


def test_build_trace_rejects_non_positive_start():
    """A non-positive start is refused."""
    with pytest.raises(ValueError):
        build_trace(0, 1)


def test_build_trace_rejects_negative_length():
    """A negative step count is refused."""
    with pytest.raises(ValueError):
        build_trace(3, -1)


def test_step_witness_rejects_even_value():
    """A step witness needs a positive odd input."""
    with pytest.raises(ValueError):
        accelerated_step_witness(4)


def test_trace_to_one_rejects_even_start():
    """The trace builder refuses an even start."""
    with pytest.raises(ValueError):
        trace_to_one(2)


def test_trace_to_one_bound_is_unknown_not_a_claim():
    """A hit step limit raises, rather than claiming non-convergence."""
    with pytest.raises(ValueError):
        trace_to_one(27, limit=1)


def test_trace_values_matches_step_successors():
    """The visited values are the start followed by the step successors."""
    assert trace_values(3, 2) == [3, 5, 1]


def test_wrong_equation_is_detected():
    """A corrupted successor breaks the arithmetic equation."""
    good = ArithmeticStep(1, 5)
    bad = ArithmeticStep(1, 6)
    assert good.equation_holds(3)
    assert not bad.equation_holds(3)


def test_lean_rendering_is_deterministic():
    """The Lean rendering of a trace is stable and well-formed."""
    trace = build_trace(3, 2)
    assert lean_step_list(trace.steps) == "[⟨1, 5⟩, ⟨4, 1⟩]"
    rendered = lean_trace(trace.start, trace.steps, trace.endpoint)
    assert rendered == "{ start := 3, steps := [⟨1, 5⟩, ⟨4, 1⟩], endpoint := 1 }"
    assert lean_step_list(trace.steps) == lean_step_list(trace.steps)


def test_generated_module_is_reproducible():
    """Regenerating the Lean fixture module reproduces it byte for byte."""
    import sys
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root / "scripts"))

    from generate_arithmetic_traces import render_module

    target = root / "Lean" / "CollatzResearch" / "ArithmeticWitnessTraces.lean"
    assert target.read_text(encoding="utf-8") == render_module()
