# ADR 0006: Two-adic valuation convention for zero

Status: accepted.

## Context

The accelerated Collatz map `T(n) = (3n + 1) / 2^{ν₂(3n + 1)}` invokes
the two-adic valuation on the strictly positive integer `3n + 1` (because
the precondition on `T` is `n` is a positive odd, so `3n + 1 ≥ 4`).
In practice today, no caller ever invokes `ν₂` on zero, and the question
of `ν₂(0)` is a convention question rather than a correctness question.

However, the two implementations disagree on what `ν₂(0)` should do:

- Python (`collatz_research.accelerated.two_adic_valuation`):
  raises `ValueError("two_adic_valuation is defined here only for positive integers")`.
- Lean (`CollatzResearch.Basic.twoAdicValuation`):
  `n.factorization 2`, which by Mathlib's convention is `0` for `n = 0`.

This divergence is invisible to the current code paths but would become
visible the moment a caller (e.g., a generalized certificate, a partial
trajectory, a numerical search) needs `ν₂(0)` to mean something. It is
also a wrong-direction inconsistency: Mathlib is the proof authority,
so the Lean convention should be canonical and Python should match.

## Decision

Define **`ν₂(0) = 0`**.

This is consistent with:

- Mathlib's `Nat.factorization`, which maps `0 ↦ 0` for every prime.
- The standard convention for the discrete valuation at a prime of the
  local ring `ℤ_(p)`, where `ν_p(0) = +∞` for the *extended* valuation,
  but the *integer* valuation commonly takes `ν_p(0) = 0` to keep the
  function total.
- Project simplicity: the Python implementation becomes total and
  matches Lean, so a future "expose ν₂ as a generic helper" change does
  not need to invent a special case.

The Python precondition is relaxed accordingly:

```python
def two_adic_valuation(value: int) -> int:
    """Return v_2(value) for a non-negative integer.

    By convention (ADR-0006), v_2(0) = 0.
    """
    if value < 0:
        raise ValueError(...)
    if value == 0:
        return 0
    ...
```

Negative inputs still raise (the Collatz domain is `ℕ`, not `ℤ`).

## Consequences

- **Python and Lean agree.** A future test that crosses implementations
  no longer needs a special case for `0`.
- **No behavioural change** for any existing call site. Every caller
  passes a strictly positive integer (`3n + 1` with `n ≥ 1` odd, so
  `3n + 1 ≥ 4`).
- The Python contract is now total on `ℕ` and partial on `ℤ` (negative
  raises). The Lean contract is total on `ℕ`. The two contracts differ
  only on `value < 0`, where the Python `ValueError` is a defensive
  boundary for callers using signed integers; in pure Lean terms this
  boundary does not exist (no negatives in `Nat`).
- A new test (`tests/test_accelerated.py::test_two_adic_valuation_zero`)
  asserts `two_adic_valuation(0) == 0`.

## Note on generalization

If a future story needs the extended valuation `ν₂(0) = +∞` (e.g., to
expose `T` on the full `ℕ` including `0`), this ADR should be revisited
and an additional helper (`two_adic_valuation_extended`) added. The
total-on-ℕ contract for `two_adic_valuation` should remain `0` to keep
the function usable in finite-arithmetic contexts.
