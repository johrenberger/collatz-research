"""Partition checker for residue classes.

A partition of ℤ/mℤ is a list of residues that:
- Covers all of ℤ/mℤ (completeness): every `r ∈ [0, m)` is in the partition.
- Has no duplicates (disjointness): `r1 ≠ r2` for any `r1, r2` in the partition.
- All residues are in `[0, m)` (validity).

The `is_partition` function checks all three conditions and raises
`PartitionError` with a stable category on failure. Type checking is
strict: `m` and each residue must be a non-bool `int`; non-iterable
inputs are rejected. This prevents untrusted callers from sneaking
non-integer values past the comparison operators (P1 review feedback
on PR #9).
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

# Error categories (stable, uppercase).
ERR_INVALID_RESIDUE = "INVALID_RESIDUE"
ERR_INCOMPLETE = "INCOMPLETE"
ERR_NON_DISJOINT = "NON_DISJOINT"


class PartitionError(Exception):
    """Raised when a residue partition fails validation."""

    def __init__(self, category: str, message: str):
        self.category = category
        self.message = message
        super().__init__(f"{category}: {message}")


def _is_non_bool_int(x: Any) -> bool:
    """True iff `x` is an `int` but not a `bool`."""
    return isinstance(x, int) and not isinstance(x, bool)


def is_partition(m: int, residues: Sequence[int]) -> bool:
    """Check whether `residues` is a valid partition of ℤ/mℤ.

    The checks run in a fixed order:
    1. Modulus type validity (must be a non-bool `int`).
    2. Modulus value validity (m >= 1).
    3. Residues collection type (must be iterable).
    4. Per-residue type validity (each must be a non-bool `int`).
    5. Per-residue value validity (each r in [0, m)).
    6. Disjointness (no duplicates).
    7. Completeness (covers all of [0, m)).

    Raises `PartitionError` with a stable category if the partition
    is invalid. Returns `True` if the partition is valid.
    """
    # 1. Modulus type.
    if not _is_non_bool_int(m):
        raise PartitionError(
            ERR_INVALID_RESIDUE,
            f"modulus m must be int (got {type(m).__name__}: {m!r})",
        )

    # 2. Modulus value.
    if m < 1:
        raise PartitionError(ERR_INVALID_RESIDUE, f"modulus m = {m} must be >= 1")

    # 3. Residues collection type — must be iterable.
    try:
        residues_list = list(residues)
    except TypeError as e:
        raise PartitionError(
            ERR_INVALID_RESIDUE,
            f"residues must be iterable (got {type(residues).__name__})",
        ) from e

    # 4 & 5. Per-residue type + value.
    for r in residues_list:
        if not _is_non_bool_int(r):
            raise PartitionError(
                ERR_INVALID_RESIDUE,
                f"residue must be int (got {type(r).__name__}: {r!r})",
            )
        if r < 0 or r >= m:
            raise PartitionError(
                ERR_INVALID_RESIDUE,
                f"residue {r} not in [0, {m})",
            )

    # 6. Disjointness — no duplicates.
    seen: set[int] = set()
    for r in residues_list:
        if r in seen:
            raise PartitionError(
                ERR_NON_DISJOINT,
                f"residue {r} appears more than once",
            )
        seen.add(r)

    # 7. Completeness — every r in [0, m) is in the partition.
    missing = set(range(m)) - seen
    if missing:
        missing_sorted = sorted(missing)
        raise PartitionError(
            ERR_INCOMPLETE,
            f"missing residues: {missing_sorted}",
        )

    return True
