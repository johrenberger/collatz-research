"""Reference arithmetic for candidate generation; not a proof implementation."""


def two_adic_valuation(value: int) -> int:
    """Return v_2(value) for a non-negative integer.

    By convention (ADR-0006), v_2(0) = 0, matching Mathlib's
    `Nat.factorization`. Negative inputs raise `ValueError`.

    The Collatz domain is the positive integers, so v_2 is only ever
    called with strictly positive inputs in production code; the
    zero-handling is for symmetry with the Lean counterpart and for
    the differential test suite.
    """
    if value < 0:
        raise ValueError("two_adic_valuation is defined here only for non-negative integers")
    if value == 0:
        return 0
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def accelerated_step(odd_positive: int) -> int:
    """Apply (3n + 1) / 2^v2(3n + 1) on the positive odd domain."""
    if odd_positive <= 0 or odd_positive % 2 == 0:
        raise ValueError("accelerated_step requires a positive odd integer")
    successor = 3 * odd_positive + 1
    return successor >> two_adic_valuation(successor)
