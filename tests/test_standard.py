import pytest
from collatz_research.accelerated import accelerated_step, two_adic_valuation
from collatz_research.standard import (
    is_even,
    is_odd,
    is_positive,
    standard_step,
    standard_trajectory,
)


def test_standard_step_odd() -> None:
    assert standard_step(1) == 4
    assert standard_step(3) == 10
    assert standard_step(5) == 16
    assert standard_step(7) == 22


def test_standard_step_even() -> None:
    assert standard_step(2) == 1
    assert standard_step(4) == 2
    assert standard_step(8) == 4
    assert standard_step(16) == 8


def test_standard_step_rejects_non_positive() -> None:
    with pytest.raises(ValueError):
        standard_step(0)
    with pytest.raises(ValueError):
        standard_step(-1)


def test_predicates() -> None:
    assert is_positive(1) and is_positive(7)
    assert not is_positive(0) and not is_positive(-3)

    assert is_odd(1) and is_odd(7)
    assert not is_odd(2) and not is_odd(0) and not is_odd(-3)

    assert is_even(2) and is_even(8)
    assert not is_even(1) and not is_even(0) and not is_even(-3)


def test_standard_trajectory_basic() -> None:
    # steps=0 returns [start]
    assert standard_trajectory(3, 0) == [3]
    assert standard_trajectory(7, 0) == [7]

    # Length is always steps + 1
    assert len(standard_trajectory(3, 5)) == 6
    assert len(standard_trajectory(1, 10)) == 11

    # Specific traces
    assert standard_trajectory(3, 1) == [3, 10]
    assert standard_trajectory(3, 2) == [3, 10, 5]
    assert standard_trajectory(1, 3) == [1, 4, 2, 1]  # accelerated fixed point
    assert standard_trajectory(7, 2) == [7, 22, 11]


def test_standard_trajectory_rejects_invalid() -> None:
    with pytest.raises(ValueError):
        standard_trajectory(0, 1)
    with pytest.raises(ValueError):
        standard_trajectory(-1, 1)
    with pytest.raises(ValueError):
        standard_trajectory(3, -1)


def test_standard_trajectory_witnesses_accelerated_equivalence() -> None:
    """For odd n: standard_trajectory(n, 1 + ν₂(3n+1)) ends at T(n).

    This is the Python witness for Story 03's one-step forward
    equivalence. The Lean proof lives in
    `CollatzResearch.Equivalence.acceleratedStep_equiv_standardStep`.
    """
    cases = [1, 3, 5, 7, 11, 13, 15, 27]
    for n in cases:
        k = 1 + two_adic_valuation(3 * n + 1)
        trajectory = standard_trajectory(n, k)
        assert trajectory[-1] == accelerated_step(n), (
            f"standard_trajectory({n}, {k}) ends at {trajectory[-1]} "
            f"but accelerated_step({n}) = {accelerated_step(n)}"
        )


def test_standard_trajectory_reaches_one_for_known_inputs() -> None:
    """All canonical test vectors from `docs/test-vectors.json` reach 1
    via the standard trajectory. (Untrusted — this is a witness for
    examples, not a proof of global convergence.)
    """
    import json
    from pathlib import Path

    vectors_path = Path(__file__).parent.parent / "docs" / "test-vectors.json"
    with vectors_path.open() as f:
        data = json.load(f)

    for vec in data["vectors"]:
        if "standard_trajectory_to_1" not in vec:
            continue
        n = vec["input"]
        expected = vec["standard_trajectory_to_1"]
        live = standard_trajectory(n, len(expected) - 1)
        assert live == expected, (
            f"standard_trajectory({n}, {len(expected) - 1}) = {live} " f"!= expected {expected}"
        )
