"""Untrusted trace producer for the Lean arithmetic-witness checker (story R04).

This module is the Python half of the R04 boundary. It computes *raw
numbers*: the exponent and successor of each accelerated step, plus the
claimed endpoint. Those numbers are untrusted; the Lean side
(Lean/CollatzResearch/ArithmeticWitness.lean) re-checks every arithmetic
equation with the kernel and proves that the accepted trace is the canonical
trajectory.

The trust direction is deliberate and one-way: Python may propose, Lean
disposes. Nothing here is a proof, and no Python result is consumed as a
Lean hypothesis. See ADR 0003 (Python is untrusted).
"""

from __future__ import annotations

from dataclasses import dataclass

from .accelerated import accelerated_step, two_adic_valuation


@dataclass(frozen=True)
class ArithmeticStep:
    """One raw accelerated step: the exponent of two and the successor."""

    exponent: int
    successor: int

    def equation_holds(self, value: int) -> bool:
        """Return whether the arithmetic equation holds for the given value."""
        return 3 * value + 1 == 2**self.exponent * self.successor


@dataclass(frozen=True)
class ArithmeticTrace:
    """A raw accelerated trace: the start, the steps, and the endpoint."""

    start: int
    steps: tuple[ArithmeticStep, ...]
    endpoint: int

    def equation_holds(self) -> bool:
        """Return whether every step equation holds along the trace."""
        value = self.start
        for step in self.steps:
            if not step.equation_holds(value):
                return False
            value = step.successor
        return True

    def values(self) -> list[int]:
        """Return the values the trace visits, start included."""
        return [self.start, *(step.successor for step in self.steps)]


def accelerated_step_witness(value: int) -> ArithmeticStep:
    """Return the raw step witness for one positive odd value."""
    if value <= 0 or value % 2 == 0:
        raise ValueError("accelerated_step_witness requires a positive odd integer")
    numerator = 3 * value + 1
    exponent = two_adic_valuation(numerator)
    return ArithmeticStep(exponent=exponent, successor=numerator >> exponent)


def build_trace(start: int, length: int) -> ArithmeticTrace:
    """Build a raw trace of the given number of accelerated steps.

    The trace is a *candidate*: it is well-formed by construction, but the
    arithmetic is only re-checked in Lean.
    """
    if start <= 0 or start % 2 == 0:
        raise ValueError("build_trace requires a positive odd start")
    if length < 0:
        raise ValueError("build_trace requires a non-negative length")
    steps: list[ArithmeticStep] = []
    value = start
    for _ in range(length):
        witness = accelerated_step_witness(value)
        steps.append(witness)
        value = witness.successor
    return ArithmeticTrace(start=start, steps=tuple(steps), endpoint=value)


def trace_to_one(start: int, limit: int = 100_000) -> ArithmeticTrace:
    """Build the raw trace from a start value until it reaches 1.

    Raises ValueError if the trace does not reach 1 within the step limit.
    A bound that is hit is an unknown outcome, never a claim that the
    trajectory does not converge.
    """
    if start <= 0 or start % 2 == 0:
        raise ValueError("trace_to_one requires a positive odd start")
    steps: list[ArithmeticStep] = []
    value = start
    for _ in range(limit):
        if value == 1:
            return ArithmeticTrace(start=start, steps=tuple(steps), endpoint=value)
        witness = accelerated_step_witness(value)
        steps.append(witness)
        value = witness.successor
    raise ValueError(f"trace from {start} did not reach 1 within {limit} steps")


def trace_values(start: int, length: int) -> list[int]:
    """Return the values visited by the accelerated trajectory from a start."""
    return build_trace(start, length).values()


def witness_matches_reference(value: int) -> bool:
    """Return whether a step witness agrees with the reference step function.

    This is a differential cross-check between the witness encoding and the
    existing reference implementation in the accelerated module. It is a
    consistency check, not a proof.
    """
    witness = accelerated_step_witness(value)
    return witness.successor == accelerated_step(value)


def lean_step_list(steps: tuple[ArithmeticStep, ...]) -> str:
    """Render the steps of a trace as a Lean list of StepWitness values."""
    entries = ", ".join(f"⟨{step.exponent}, {step.successor}⟩" for step in steps)
    return f"[{entries}]"


def lean_trace(start: int, steps: tuple[ArithmeticStep, ...], endpoint: int) -> str:
    """Render a whole trace as a Lean TraceWitness value."""
    return f"{{ start := {start}, steps := {lean_step_list(steps)}, endpoint := {endpoint} }}"
