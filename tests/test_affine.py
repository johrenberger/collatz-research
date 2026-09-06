"""Unit + property tests for the symbolic affine executor.

Story 04: branch words, affine maps over ℤ with exact arithmetic,
composition, applicability, and differential tests against the
canonical test corpus.
"""

import json
from pathlib import Path

import pytest
from collatz_research.accelerated import accelerated_step, two_adic_valuation
from collatz_research.affine import AffineMap, BranchWord
from hypothesis import given, settings
from hypothesis import strategies as st

# --- Unit tests: AffineMap ---


def test_affine_identity() -> None:
    """Identity map: n ↦ n for any n."""
    id_map = AffineMap.identity()
    for n in [0, 1, 7, 100, -3]:
        assert id_map.apply(n) == n


def test_affine_step_basic() -> None:
    """Single-step map: n ↦ (3n + 1) / 2^k for valid (n, k)."""
    # T(1) = (3*1 + 1) / 2^2 = 1
    assert AffineMap.step(2).apply(1) == 1
    # T(3) = (3*3 + 1) / 2^1 = 5
    assert AffineMap.step(1).apply(3) == 5
    # T(5) = (3*5 + 1) / 2^4 = 1
    assert AffineMap.step(4).apply(5) == 1


def test_affine_step_rejects_zero_k() -> None:
    """step(k) requires k >= 1."""
    with pytest.raises(ValueError):
        AffineMap.step(0)


def test_affine_apply_rejects_indivisible() -> None:
    """apply raises on a violated divisibility rather than truncating."""
    # T requires 2^k | (3n+1). For n=3, ν₂(10) = 1, so step(2) does NOT
    # divide (3*3+1) = 10.
    with pytest.raises(ValueError):
        AffineMap.step(2).apply(3)


def test_affine_compose_left_associative() -> None:
    """Composition is associative: (m1 ∘ m2) ∘ m3 = m1 ∘ (m2 ∘ m3)."""
    m1 = AffineMap.step(1)
    m2 = AffineMap.step(2)
    m3 = AffineMap.step(1)
    assert (m1.compose(m2)).compose(m3) == m1.compose(m2.compose(m3))


def test_affine_compose_apply_compatible() -> None:
    """apply of composition equals composition of apply."""
    m1 = AffineMap.step(2)
    m2 = AffineMap.step(1)
    n = 3  # m2(3)=5 is odd, so the intermediate value is valid for m1
    assert (m1.compose(m2)).apply(n) == m1.apply(m2.apply(n))


# --- Unit tests: BranchWord ---


def test_branch_word_empty_is_identity() -> None:
    """The empty word is the identity on the positive odd domain."""
    assert BranchWord.empty().to_affine() == AffineMap.identity()
    for n in [1, 7, 13]:
        assert BranchWord.empty().execute(n) == n


def test_branch_word_singleton_applies_to() -> None:
    """A singleton word applies iff its valuation matches ν₂(3n+1)."""
    # 1 → T(1) = 1; branch word [2] applies to 1 (ν₂(4) = 2)
    w = BranchWord(valuations=(2,))
    assert w.applies_to(1)
    # [1] does NOT apply to 1
    w1 = BranchWord(valuations=(1,))
    assert not w1.applies_to(1)
    # [1] applies to 3 (ν₂(10) = 1)
    assert w1.applies_to(3)


def test_branch_word_singleton_execute_matches_accelerated_step() -> None:
    """For each test vector, executing the singleton word equals T(n)."""
    cases = [(1, 2), (3, 1), (5, 4), (7, 1), (11, 1), (13, 3), (27, 1)]
    for n, k in cases:
        w = BranchWord(valuations=(k,))
        assert w.applies_to(n)
        assert w.execute(n) == accelerated_step(n)


def test_branch_word_multi_step_trajectory_27_to_91() -> None:
    """The 8-step trajectory from 27 reaches 91."""
    w = BranchWord(valuations=(1, 2, 1, 1, 1, 1, 2, 2))
    assert w.applies_to(27)
    assert w.execute(27) == 91


def test_branch_word_rejects_non_odd_or_non_positive() -> None:
    """applies_to rejects non-positive or even inputs."""
    w = BranchWord(valuations=(1,))
    assert not w.applies_to(0)
    assert not w.applies_to(-1)
    assert not w.applies_to(2)


def test_branch_word_rejects_zero_k() -> None:
    """A valuation of 0 is rejected at construction time."""
    with pytest.raises(ValueError):
        BranchWord(valuations=(0,))


# --- Test corpus differential tests ---


def _load_corpus() -> dict:
    vectors_path = Path(__file__).parent.parent / "docs" / "test-vectors-affine.json"
    with vectors_path.open() as f:
        return json.load(f)


def test_affine_corpus_matches_execute() -> None:
    """Each corpus vector: BranchWord.execute(input) == expected_result."""
    data = _load_corpus()
    for vec in data["vectors"]:
        n = vec["input"]
        word = BranchWord(valuations=tuple(vec["branch_word"]))
        expected = vec["expected_result"]
        assert word.applies_to(n), f"word {vec['branch_word']} does not apply to {n}"
        assert word.execute(n) == expected, (
            f"execute({n}, {vec['branch_word']}) = {word.execute(n)} " f"!= expected {expected}"
        )


def test_affine_corpus_to_affine_matches_execute() -> None:
    """Each corpus vector: word.to_affine().apply(input) == execute(input)."""
    data = _load_corpus()
    for vec in data["vectors"]:
        n = vec["input"]
        word = BranchWord(valuations=tuple(vec["branch_word"]))
        assert word.to_affine().apply(n) == word.execute(n)


# --- Property tests (Hypothesis) ---


@given(st.integers(min_value=1, max_value=10_000))
@settings(max_examples=200)
def test_branch_word_singleton_matches_accelerated_step(n: int) -> None:
    """For any odd n in [1, 10000]: BranchWord([ν₂(3n+1)]).execute(n) == T(n)."""
    if n % 2 == 0:
        return  # applies_to rejects even inputs
    k = two_adic_valuation(3 * n + 1)
    w = BranchWord(valuations=(k,))
    assert w.applies_to(n)
    assert w.execute(n) == accelerated_step(n)
