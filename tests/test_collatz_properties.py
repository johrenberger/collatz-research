"""Property-based tests using Hypothesis.

These tests are property-based, not example-based: Hypothesis generates
inputs in a wide range and asserts invariants that should hold for every
input. They complement the example-based tests in `test_differential.py`
and `test_accelerated.py` by catching invariants that finite examples miss.

The invariants asserted here correspond to the architecture session's
property suite proposal (`T(n) > 0`, `C(2n) == n`, `C(odd n) == 3n+1`,
`v_2(n) >= 0`).
"""

from __future__ import annotations

from collatz_research.accelerated import accelerated_step, two_adic_valuation
from collatz_research.standard import standard_step
from hypothesis import given
from hypothesis import strategies as st

# `accelerated_step` raises ValueError on even inputs (its contract is the
# positive-odd domain), so the strategy must filter to odd numbers.
odd_positive = st.integers(min_value=1, max_value=10**9).filter(lambda n: n % 2 == 1)


@given(st.integers(min_value=1, max_value=10**9))
def test_standard_step_matches_definition(n: int) -> None:
    """C(n) = n/2 if n even, 3n+1 if n odd."""
    result = standard_step(n)
    if n % 2 == 0:
        assert result == n // 2
    else:
        assert result == 3 * n + 1


@given(odd_positive)
def test_accelerated_step_positive(n: int) -> None:
    """T(n) > 0 for every n in the positive odd domain.

    Regression for an earlier buggy implementation that returned 0.
    """
    assert accelerated_step(n) > 0


@given(st.integers(min_value=1, max_value=10**9))
def test_two_adic_valuation_non_negative(n: int) -> None:
    """v_2(n) >= 0 for every n in the positive domain."""
    assert two_adic_valuation(n) >= 0


@given(st.integers(min_value=1, max_value=10**9))
def test_two_adic_valuation_zero_for_odd(n: int) -> None:
    """v_2(n) = 0 for odd n."""
    if n % 2 == 1:
        assert two_adic_valuation(n) == 0


@given(odd_positive)
def test_accelerated_step_strictly_less_than_2n(n: int) -> None:
    """T(n) < 2n for n in the positive odd domain.

    T collapses k = 1 + v_2(3n+1) >= 2 standard steps into one, so the
    numerator 3n+1 is divided by at least 2, giving an upper bound of
    (3n+1)/2 < 2n. The accelerated map can increase (T(3) = 5 > 3),
    so the natural lower bound is `> 0` (already covered above); the
    natural upper bound is `< 2n`, not `<= n`.
    """
    assert accelerated_step(n) < 2 * n
