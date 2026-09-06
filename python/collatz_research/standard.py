"""Standard (unaccelerated) Collatz map, parity/positivity predicates, and
finite-trajectory witness.

The standard map `C(n) = n/2 if n is even else 3n + 1` is the canonical
Collatz iteration; the accelerated map `T` is defined on the odd domain
by `T(n) = C^{1 + ν₂(3n+1)}(n) = (3n + 1) / 2^{ν₂(3n + 1)}`.

These two implementations are independent and reconciled by the
differential test suite (`tests/test_differential.py`). The Lean
counterpart is `CollatzResearch.Dynamics.standardStep`.

The trajectory witness (`standard_trajectory`) is intentionally untrusted:
it produces concrete numerical sequences for examples and tests, but it
is not the proof authority. The Lean `CollatzResearch.Equivalence`
module is the proof authority for the formal equivalence.
"""

from __future__ import annotations


def standard_step(n: int) -> int:
    """Apply the standard Collatz map C on the positive integer domain.

    C(n) = n / 2  if n is even
    C(n) = 3n + 1 if n is odd
    """
    if n < 1:
        raise ValueError("standard_step is defined here only for positive integers")
    if n % 2 == 0:
        return n // 2
    return 3 * n + 1


def is_positive(n: int) -> bool:
    """`True` iff n is a strictly positive integer."""
    return n > 0


def is_odd(n: int) -> bool:
    """`True` iff n is a positive odd integer.

    Mirrors Mathlib's `Nat.Odd`, which requires `n % 2 = 1` on positive
    inputs (Nat cannot be 0 and odd simultaneously).
    """
    return n > 0 and n % 2 == 1


def is_even(n: int) -> bool:
    """`True` iff n is a positive even integer."""
    return n > 0 and n % 2 == 0


def standard_trajectory(start: int, steps: int) -> list[int]:
    """Return the finite standard trajectory from `start` for `steps + 1` values.

    Element 0 is `start`; element `k` is `C^k(start)`, the result of applying
    the standard Collatz map `k` times. The returned list has length
    `steps + 1`. Raises `ValueError` if `start < 1` or `steps < 0`.

    This is an untrusted witness for examples and tests. The formal
    statement of equivalence with the accelerated map is in
    `CollatzResearch.Equivalence.standardTrajectory` (Lean).
    """
    if start < 1:
        raise ValueError("standard_trajectory is defined for positive integers")
    if steps < 0:
        raise ValueError("steps must be non-negative")
    trajectory = [start]
    current = start
    for _ in range(steps):
        current = standard_step(current)
        trajectory.append(current)
    return trajectory
