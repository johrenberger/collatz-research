"""Tests for the partition checker."""

from __future__ import annotations

import pytest
from collatz_research.partitions import (
    ERR_INCOMPLETE,
    ERR_INVALID_RESIDUE,
    ERR_NON_DISJOINT,
    PartitionError,
    is_partition,
)

# --- Valid partitions ---


def test_valid_trivial_partition_3() -> None:
    assert is_partition(3, [0, 1, 2]) is True


def test_valid_singleton_partition_1() -> None:
    assert is_partition(1, [0]) is True


def test_valid_reordered_partition() -> None:
    """Order of residues does not matter."""
    assert is_partition(4, [3, 1, 0, 2]) is True


def test_valid_large_partition() -> None:
    m = 100
    assert is_partition(m, list(range(m))) is True


def test_valid_partition_with_repeated_attempts() -> None:
    """Same partition checked multiple times returns True each time."""
    ps = [0, 1, 2, 3, 4]
    for _ in range(3):
        assert is_partition(5, ps) is True


# --- INVALID_RESIDUE ---


def test_m_zero_raises_invalid_residue() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(0, [0])
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_m_negative_raises_invalid_residue() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(-1, [0])
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_negative_residue_raises_invalid_residue() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [-1, 0, 1])
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_residue_equal_to_m_raises_invalid_residue() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1, 3])
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_residue_greater_than_m_raises_invalid_residue() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1, 5])
    assert exc_info.value.category == ERR_INVALID_RESIDUE


# --- NON_DISJOINT ---


def test_duplicate_residue_raises_non_disjoint() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1, 1])
    assert exc_info.value.category == ERR_NON_DISJOINT


def test_all_same_residue_raises_non_disjoint() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 0, 0])
    assert exc_info.value.category == ERR_NON_DISJOINT


def test_duplicate_after_valid_residues_raises_non_disjoint() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(4, [0, 1, 2, 2])
    assert exc_info.value.category == ERR_NON_DISJOINT


# --- INCOMPLETE ---


def test_missing_residue_raises_incomplete() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1])  # missing 2
    assert exc_info.value.category == ERR_INCOMPLETE


def test_empty_partition_raises_incomplete() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [])
    assert exc_info.value.category == ERR_INCOMPLETE


def test_gapped_partition_raises_incomplete() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(5, [0, 1, 3, 4])  # missing 2
    assert exc_info.value.category == ERR_INCOMPLETE


def test_only_zero_raises_incomplete() -> None:
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0])  # missing 1, 2
    assert exc_info.value.category == ERR_INCOMPLETE


# --- Error precedence (advertised order) ---


def test_invalid_residue_checked_first() -> None:
    """Invalid residue is checked before disjointness and completeness."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1, -1, 1])  # negative AND duplicate
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_disjoint_checked_before_complete() -> None:
    """Disjointness is checked before completeness."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, 1, 1])  # duplicate; missing 2
    assert exc_info.value.category == ERR_NON_DISJOINT


def test_m_validity_checked_before_residue() -> None:
    """Modulus validity is checked before residue validity."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(0, [-1])  # m=0 invalid
    assert exc_info.value.category == ERR_INVALID_RESIDUE


# --- Type validation (P1 review feedback on PR #9) ---


def test_rejects_bool_modulus() -> None:
    """Adversarial: bool modulus is rejected as ERR_INVALID_RESIDUE (not treated as int)."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(True, [0])  # type: ignore[arg-type]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_bool_residue() -> None:
    """Adversarial: bool residue is rejected as ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0, True])  # type: ignore[list-item]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_string_modulus() -> None:
    """Adversarial: string modulus is rejected as ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition("3", [0, 1, 2])  # type: ignore[arg-type]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_string_residue() -> None:
    """Adversarial: string residue is rejected as ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, ["0", "1"])  # type: ignore[list-item]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_float_modulus() -> None:
    """Adversarial: float modulus is rejected as ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3.0, [0, 1, 2])  # type: ignore[arg-type]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_float_residue() -> None:
    """Adversarial: float residue is rejected as ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [0.0, 1.0, 2.0])  # type: ignore[list-item]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_rejects_non_iterable_residues() -> None:
    """Adversarial: non-iterable input is rejected with ERR_INVALID_RESIDUE."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, 5)  # type: ignore[arg-type]
    assert exc_info.value.category == ERR_INVALID_RESIDUE


def test_accepts_iterator_residues() -> None:
    """Functional: an iterator (consumed once) is accepted."""

    def gen():
        yield 0
        yield 1
        yield 2

    assert is_partition(3, gen()) is True


def test_accepts_empty_list() -> None:
    """Functional: empty list raises INCOMPLETE (not INVALID_RESIDUE)."""
    with pytest.raises(PartitionError) as exc_info:
        is_partition(3, [])
    assert exc_info.value.category == ERR_INCOMPLETE
