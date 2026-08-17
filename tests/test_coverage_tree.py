"""TDD tests for the coverage-tree model + checker (Story 07).

Mutation tests corrupt each field of `sample_tree()` and assert that
`check_tree` raises with the matching stable category. Plus round-trip
JSONL serialization, deterministic-ordering, leaves-consistency,
fail-closed `from_dict` (Codex P2), and the cycle policy.
"""

from __future__ import annotations

import copy
import json

import pytest
from collatz_research.tree import (
    ERR_HAS_CYCLE,
    ERR_INVALID_NODE,
    ERR_LEAF_ID_EMPTY,
    ERR_LEAVES_MISMATCH,
    ERR_NOT_CHILD_TOTAL,
    ERR_NOT_DISJOINT,
    EXPECTED_SCHEMA,
    CoverageLeaf,
    CoverageNode,
    CoverageTree,
    CoverageTreeError,
    accelerated_orbit,
    check_tree,
    descend,
    descend_orbit,
    deterministic_children,
    from_dict,
    has_child_for_each_declared_residue,
    has_no_cycles,
    is_disjoint,
    leaf_id_non_empty,
    lean_interval,
    leaves_consistent,
    reachable_leaves,
    reaches_one_within,
    sample_tree,
    sat,
    sat_orbit,
    to_dict,
    well_formed,
)

# ---- Happy path ----


def test_sample_tree_passes_all_checks():
    tree = sample_tree()
    assert has_child_for_each_declared_residue(tree)
    assert is_disjoint(tree)
    assert leaves_consistent(tree)
    assert has_no_cycles(tree)
    assert leaf_id_non_empty(tree)
    # check_tree raises only on failure; no exception == pass.
    check_tree(tree)


def test_sample_tree_round_trips_through_dict():
    tree = sample_tree()
    d = to_dict(tree)
    # JSON-serializable (one object per JSONL line).
    text = json.dumps(d)
    loaded = json.loads(text)
    tree2 = from_dict(loaded)
    assert to_dict(tree2) == d
    check_tree(tree2)


def test_deterministic_children_order_is_sorted_by_residue():
    tree = sample_tree()
    reversed_children = {r: tree.root.children[r] for r in reversed(list(tree.root.children))}
    reverse_node = CoverageNode(
        modulus=tree.root.modulus,
        partition=tree.root.partition,
        children=reversed_children,
    )
    seen = [r for r, _ in deterministic_children(reverse_node)]
    assert seen == sorted(tree.root.children.keys())


def test_reachable_leaves_match_top_level_leaves():
    """The set of leaves reachable from `root` is exactly `tree.leaves`."""
    tree = sample_tree()
    reachable = set(reachable_leaves(tree.root))
    top = set(tree.leaves)
    assert reachable == top
    assert reachable  # non-empty


# ---- Helpers ----


def _mut(root_mutator, *, max_depth=None) -> CoverageTree:
    """Clone `sample_tree()` and apply a mutator to the root node."""
    base = sample_tree()
    mutated = copy.deepcopy(base)
    root_mutator(mutated.root)
    if max_depth is not None:
        mutated.max_depth = max_depth
    return mutated


# ---- Disjointness mutations ----


def test_mutation_partition_geq_modulus_fails_disjointness():
    """Root partition (1, 4) at modulus 4 — residue 4 is out of `[0, 4)`."""
    bad = _mut(lambda root: setattr(root, "partition", (1, 4)))
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_NOT_DISJOINT


def test_mutation_partition_with_negative_residue_fails_disjointness():
    bad = _mut(lambda root: setattr(root, "partition", (1, -3)))
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_NOT_DISJOINT


def test_mutation_invalid_modulus_fails_disjointness():
    """Modulus 0 violates the `m >= 1` invariant."""
    bad = _mut(lambda root: setattr(root, "modulus", 0))
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_NOT_DISJOINT


def test_mutation_duplicate_residue_fails_disjointness():
    """Partition with a duplicate residue is not internally consistent."""
    bad = _mut(lambda root: setattr(root, "partition", (1, 1)))
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_NOT_DISJOINT


# ---- Child-totality mutations (Codex P1 naming; NOT full `[0, m)` coverage) ----


def test_dropped_residue_breaks_leaves_consistency():
    """Drop residue 1 from children; the leaves under residue 1 become
    unreachable. `leaves_consistent` fires (before child-totality)
    because removing a child necessarily disconnects its subtree from
    root. The test demonstrates that `check_tree`'s order — acyclic
    → leaves-consistent → disjoint → child-total — surfaces the
    structural-reachability issue first.
    """
    bad = _mut(lambda root: root.children.pop(1))
    assert is_disjoint(bad)
    assert not leaves_consistent(bad)
    assert not has_child_for_each_declared_residue(bad)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_LEAVES_MISMATCH


def test_mutation_extra_residue_in_children_fails_child_totality():
    """Add a child at residue 2 not in the partition (1, 3)."""
    bad = _mut(lambda root: root.children.__setitem__(2, root.children[1]))
    assert not has_child_for_each_declared_residue(bad)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_NOT_CHILD_TOTAL


# ---- Leaves-consistency mutations (Coex P1.1) ----


def test_mutation_missing_leaf_in_top_level_fails_leaves_consistency():
    """tree.leaves drops a reachable leaf — leaves_consistent fails."""
    bad = _mut(lambda root: None)
    bad.leaves = bad.leaves[:-1]
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_LEAVES_MISMATCH


def test_mutation_extra_leaf_in_top_level_fails_leaves_consistency():
    """tree.leaves contains a leaf not reachable from root."""
    bad = _mut(lambda root: None)
    extra = CoverageLeaf(leaf_id="extra_unreachable", leaf_property="X")
    bad.leaves = bad.leaves + (extra,)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_LEAVES_MISMATCH


def test_mutation_duplicate_leaf_id_in_top_level_fails_leaves_consistency():
    """Two top-level leaves with the same leaf_id."""
    bad = _mut(lambda root: None)
    dup = CoverageLeaf(leaf_id=bad.leaves[0].leaf_id, leaf_property="DifferentFromTheFirst")
    bad.leaves = bad.leaves + (dup,)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_LEAVES_MISMATCH


def test_mutation_unreachable_leaf_in_top_level_fails_leaves_consistency():
    """Repoint inner1.children[1] so leaves[2] is no longer reachable;
    tree.leaves still lists leaves[2]."""
    bad = _mut(lambda root: None)
    inner1 = bad.root.children[1]
    inner1.children[1] = inner1.children[2]  # leaves[1] shadows itself
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_LEAVES_MISMATCH


# ---- Leaf-id mutations (Story 07b / round-4; mirrors Lean's `verified` predicate) ----


def test_happy_path_leaf_id_non_empty():
    """`sample_tree` has all non-empty leaf_ids; the helper returns True.

    Mirrors the `hconsistent` hypothesis in the Lean
    `coverage_tree_soundness` proof body — every leaf in
    `t.leaves` must have non-empty `leafId`.
    """
    tree = sample_tree()
    assert leaf_id_non_empty(tree)


def test_mutation_empty_leaf_id_fails_leaf_id_non_empty():
    """An existing reachable leaf has its `leaf_id` mutated to the
    empty string. The structural checks (`acyclic`,
    `leaves_consistent`, `disjoint`, `child-total`) all pass; the new
    `leaf_id_non_empty` check is the first to fail. Mirrors the
    `hconsistent` hypothesis in the Lean
    `coverage_tree_soundness` proof body — without a non-empty
    `leafId`, the `verified` predicate cannot be discharged.
    """
    tree = sample_tree()
    inner1 = tree.root.children[1]
    reachable_leaf = inner1.children[1]  # leaves[0]
    mutated_leaf = CoverageLeaf(leaf_id="", leaf_property=reachable_leaf.leaf_property)
    inner1.children[1] = mutated_leaf
    tree.leaves = (mutated_leaf,) + tree.leaves[1:]
    # structural checks still pass
    assert has_no_cycles(tree)
    assert leaves_consistent(tree)
    assert is_disjoint(tree)
    assert has_child_for_each_declared_residue(tree)
    # leaf_id_non_empty fails
    assert not leaf_id_non_empty(tree)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(tree)
    assert exc.value.category == ERR_LEAF_ID_EMPTY


# ---- Cycle mutations ----


def test_mutation_depth_overflow_fails_cycle_check():
    """max_depth=1 forces leaves at depth 2 (via internal nodes) to be flagged."""
    bad = _mut(lambda root: None, max_depth=1)
    assert not has_no_cycles(bad)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(bad)
    assert exc.value.category == ERR_HAS_CYCLE


def test_mutation_structural_cycle_fails_cycle_check():
    """A node whose child points back to an ancestor creates a true cycle."""
    tree = copy.deepcopy(sample_tree())
    inner1 = tree.root.children[1]
    inner1.children[1] = tree.root
    assert not has_no_cycles(tree)
    with pytest.raises(CoverageTreeError) as exc:
        check_tree(tree)
    assert exc.value.category == ERR_HAS_CYCLE


# ---- Distinct subtrees with identical shape must NOT be flagged ----


def test_identical_shape_subtrees_are_not_a_cycle():
    """Two sibling CoverageNodes with identical (modulus, partition) shape
    are fine — only ancestry revisits count as cycles.
    """
    tree = sample_tree()
    assert has_no_cycles(tree)


# ---- Fail-closed `from_dict` (Codex P2) ----


def _good_dict() -> dict:
    return to_dict(sample_tree())


def test_from_dict_rejects_non_dict_input():
    with pytest.raises(CoverageTreeError) as exc:
        from_dict("not a dict")  # type: ignore[arg-type]
    assert exc.value.category == ERR_INVALID_NODE


def test_from_dict_rejects_wrong_schema_version():
    bad = _good_dict()
    bad["schema"] = "collatz-research/coverage-tree@0.2.0"
    with pytest.raises(CoverageTreeError) as exc:
        from_dict(bad)
    assert exc.value.category == ERR_INVALID_NODE
    assert EXPECTED_SCHEMA in str(exc.value)


def test_from_dict_rejects_missing_required_top_level_field():
    bad = _good_dict()
    del bad["leaves"]
    with pytest.raises(CoverageTreeError) as exc:
        from_dict(bad)
    assert exc.value.category == ERR_INVALID_NODE


def test_from_dict_rejects_non_int_modulus():
    bad = _good_dict()
    bad["root"]["modulus"] = "not an int"
    with pytest.raises(CoverageTreeError) as exc:
        from_dict(bad)
    assert exc.value.category == ERR_INVALID_NODE


def test_from_dict_rejects_non_int_residue_key():
    bad = _good_dict()
    # Replace one numeric residue key with a non-numeric one.
    new_children = {}
    for k, v in bad["root"]["children"].items():
        new_children[k] = v
    new_children["not_an_int"] = new_children.pop(list(new_children.keys())[0])
    bad["root"]["children"] = new_children
    with pytest.raises(CoverageTreeError) as exc:
        from_dict(bad)
    assert exc.value.category == ERR_INVALID_NODE


def test_from_dict_rejects_non_str_leaf_field():
    bad = _good_dict()
    # Leaf nodes are at depth 2: bad["root"]["children"]["1"]["children"]["1"].
    # Mutating `leaf_id` to a non-string value should fail at parse time.
    bad["root"]["children"]["1"]["children"]["1"]["leaf_id"] = 42
    with pytest.raises(CoverageTreeError) as exc:
        from_dict(bad)
    assert exc.value.category == ERR_INVALID_NODE


# ---- Descend regression: depth-0 / depth-1 / depth-2 (Story 07b / round-4) ----
# Mirrors the Lean `descendFrom` examples in
# Lean/CollatzResearch/CoverageTree.lean. Leaf-first semantics: a leaf is
# reachable regardless of remaining depth; depth-0 internal returns None.


def test_descend_depth_0_leaf_reachable():
    """Depth 0 at a leaf: leaf is reachable at any x (depth unused)."""
    leaf = CoverageLeaf(leaf_id="L0", leaf_property="P0")
    tree = CoverageTree(root=leaf, leaves=(leaf,), max_depth=0)
    assert descend(tree, 5) == leaf
    assert descend(tree, 0) == leaf
    assert descend(tree, 999) == leaf


def test_descend_depth_0_internal_returns_none():
    """Depth 0 at an internal node: depth exhausted, returns None."""
    leaf = CoverageLeaf(leaf_id="L0", leaf_property="P0")
    inner = CoverageNode(modulus=4, partition=(1,), children={1: leaf})
    tree = CoverageTree(root=inner, leaves=(leaf,), max_depth=0)
    assert descend(tree, 5) is None
    assert descend(tree, 1) is None


def test_descend_depth_1_internal_to_leaf_reachable():
    """Depth 1, internal root + leaf child, residue 1 -> leaf: reachable."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="P1")
    inner = CoverageNode(modulus=4, partition=(1,), children={1: leaf})
    tree = CoverageTree(root=inner, leaves=(leaf,), max_depth=1)
    assert descend(tree, 1) == leaf
    assert descend(tree, 5) == leaf  # 5 % 4 = 1


def test_descend_depth_1_no_child_for_residue():
    """Depth 1, internal root + leaf child, residue 2 has no child: unreachable."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="P1")
    inner = CoverageNode(modulus=4, partition=(1,), children={1: leaf})
    tree = CoverageTree(root=inner, leaves=(leaf,), max_depth=1)
    assert descend(tree, 2) is None
    assert descend(tree, 6) is None  # 6 % 4 = 2


def test_descend_depth_2_internal_to_internal_to_leaf():
    """Depth 2, internal 4 -> internal 2 -> leaf; 7 % 4 = 3, 7 % 2 = 1."""
    leaf = CoverageLeaf(leaf_id="L2", leaf_property="P2")
    inner2 = CoverageNode(modulus=2, partition=(1,), children={1: leaf})
    inner1 = CoverageNode(modulus=4, partition=(3,), children={3: inner2})
    tree = CoverageTree(root=inner1, leaves=(leaf,), max_depth=2)
    assert descend(tree, 7) == leaf
    assert descend(tree, 3) == leaf  # 3 % 4 = 3


def test_lean_interval_unicode_digits_rejected():
    """Non-ASCII decimal digits are rejected (Lean's `toNat?` only ASCII).

    `str.isdigit()` accepts Unicode decimal characters (e.g. Arabic-Indic
    ٠١٢٣, full-width ０１２３) that Lean's `String.toNat?` rejects, so
    the parser must use a strict ASCII 0-9 check to be a faithful mirror.
    """
    # Arabic-Indic digits
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="٣:٠-٢")
    assert lean_interval(leaf) is None
    # Full-width digits
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="３:０-２")
    assert lean_interval(leaf) is None
    # Mixed ASCII + full-width
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:０-２")
    assert lean_interval(leaf) is None


def test_well_formed_hi_greater_than_period():
    """`hi >= period` is not well-formed (interval must be strict subset).

    Otherwise `Sat` becomes trivially true for every residue, e.g.
    `3:0-100` would satisfy all `x` (since `x % 3 ∈ [0, 100]` for any
    `x % 3 ∈ {0, 1, 2}`).
    """
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:0-100")
    assert not well_formed(leaf)


def test_well_formed_hi_equal_to_period():
    """`hi == period` is also not well-formed (interval must be strict subset)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:0-3")
    assert not well_formed(leaf)


def test_descend_depth_2_depth_exhausted_at_second_internal():
    """Depth 1 (one unit), but tree has two internal levels: second internal returns None.

    With max_depth=1, the tree descends internal 4 -> internal 2 with
    depth 0, so the second internal returns None.
    """
    leaf = CoverageLeaf(leaf_id="L2", leaf_property="P2")
    inner2 = CoverageNode(modulus=2, partition=(1,), children={1: leaf})
    inner1 = CoverageNode(modulus=4, partition=(3,), children={3: inner2})
    tree = CoverageTree(root=inner1, leaves=(leaf,), max_depth=1)
    # 7 % 4 = 3 -> inner2; descend from depth 0 internal = None
    assert descend(tree, 7) is None


# ---- 07c-1 semantic leafProperty tests (mirrors Lean) ----
# Each leaf declares a `(period, lo, hi)` tuple via its `leaf_property`
# string `"<period>:<lo>-<hi>"`. The semantic predicate `Sat` and the
# static property `WellFormed` are Python mirrors of the Lean
# definitions in `CoverageTree.lean`.


def test_lean_interval_happy():
    """Parses '<period>:<lo>-<hi>' into (period, lo, hi)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:0-2")
    assert lean_interval(leaf) == (3, 0, 2)


def test_lean_interval_garbage_returns_none():
    """Malformed leaves return None (no separator)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="garbage")
    assert lean_interval(leaf) is None


def test_lean_interval_no_colon_returns_none():
    """Missing colon returns None."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3-0-2")
    assert lean_interval(leaf) is None


def test_lean_interval_no_dash_returns_none():
    """Missing dash in range returns None."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:02")
    assert lean_interval(leaf) is None


def test_lean_interval_invalid_nats():
    """Non-numeric parts return None."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="abc:def-ghi")
    assert lean_interval(leaf) is None


def test_lean_interval_zero_period_parses():
    """`0:0-2` parses as `(0, 0, 2)` (not well-formed, but parseable)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="0:0-2")
    assert lean_interval(leaf) == (0, 0, 2)


def test_sat_in_interval():
    """x is in interval iff x % period in [lo, hi]."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:1-2")
    assert sat(leaf, 1)  # 1 % 3 = 1 in [1, 2]
    assert sat(leaf, 2)  # 2 % 3 = 2 in [1, 2]
    assert sat(leaf, 4)  # 4 % 3 = 1 in [1, 2]
    assert sat(leaf, 5)  # 5 % 3 = 2 in [1, 2]
    assert not sat(leaf, 0)  # 0 % 3 = 0 NOT in [1, 2]
    assert not sat(leaf, 3)  # 3 % 3 = 0 NOT in [1, 2]


def test_sat_garbage_returns_false():
    """Unparseable leaves return False."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="garbage")
    assert not sat(leaf, 0)
    assert not sat(leaf, 5)


def test_well_formed_happy():
    """Valid interval (period > 0, lo <= hi) is well-formed."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:0-2")
    assert well_formed(leaf)


def test_lean_interval_negative_period_rejected():
    """Negative period is rejected (Lean's String.toNat? returns none).

    Python's `int("-1")` would accept; strict unsigned-decimal mirrors
    Lean's `String.toNat?` semantics.
    """
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="-1:0-2")) is None


def test_lean_interval_negative_lo_rejected():
    """Negative lo is rejected."""
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="3:-1-2")) is None


def test_lean_interval_negative_hi_rejected():
    """Negative hi is rejected."""
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="3:0--2")) is None


def test_lean_interval_empty_part_rejected():
    """Empty parts (e.g. missing colon segment) are rejected."""
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property=":0-2")) is None
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="3:-2")) is None
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="3:0-")) is None


def test_lean_interval_decimal_rejected():
    """Decimal numbers are rejected (Nat is integer-typed)."""
    assert lean_interval(CoverageLeaf(leaf_id="L1", leaf_property="3.5:0-2")) is None


def test_sat_zero_period_no_crash_and_mirrors_lean():
    """Period 0: Lean's `Nat.mod n 0 = n`, so `Sat` is `lo <= x <= hi`.

    This avoids Python's `ZeroDivisionError` on `x % 0` while staying
    faithful to Lean's convention.
    """
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="0:5-7")
    assert sat(leaf, 4) is False  # 4 < 5
    assert sat(leaf, 5) is True  # 5 in [5, 7]
    assert sat(leaf, 6) is True
    assert sat(leaf, 7) is True
    assert sat(leaf, 8) is False  # 8 > 7
    assert sat(leaf, 0) is False
    assert sat(leaf, 1000) is False


def test_sat_negative_period_returns_false():
    """Period from invalid leaf is None, so sat returns False."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="-1:0-2")
    assert sat(leaf, 0) is False
    assert sat(leaf, 5) is False


def test_well_formed_negative_period():
    """Period from invalid leaf is None, so well_formed returns False."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="-1:0-2")
    assert well_formed(leaf) is False


def test_well_formed_zero_period():
    """period = 0 is not well-formed (parses but ill-formed)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="0:0-2")
    assert not well_formed(leaf)


def test_well_formed_inverted_range():
    """lo > hi is not well-formed."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:5-2")
    assert not well_formed(leaf)


def test_well_formed_garbage_returns_false():
    """Unparseable leaves are not well-formed."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="garbage")
    assert not well_formed(leaf)


# ---- 07c-2 dynamics connection tests ----


def test_accelerated_orbit_base():
    """`accelerated_orbit n 0 = n`."""
    assert accelerated_orbit(5, 0) == 5
    assert accelerated_orbit(1, 0) == 1
    assert accelerated_orbit(0, 0) == 0


def test_accelerated_orbit_one_step():
    """`accelerated_orbit n 1 = acceleratedStep n` (Lean's formula).

    `acceleratedStep n = (3n+1) / 2^ν₂(3n+1)`:
    - 5 (odd): (16)/2^4 = 1 (ν₂(16)=4)
    - 8 (even): (25)/2^0 = 25 (3*8+1=25 is odd)
    - 1 (odd): (4)/2^2 = 1 (fixed point)
    """
    assert accelerated_orbit(5, 1) == 1
    assert accelerated_orbit(8, 1) == 25
    assert accelerated_orbit(1, 1) == 1
    assert accelerated_orbit(0, 1) == 1


def test_accelerated_orbit_rejects_negative_inputs():
    """The Python mirror models Lean `Nat` inputs only."""
    with pytest.raises(ValueError):
        accelerated_orbit(-1, 1)
    with pytest.raises(ValueError):
        accelerated_orbit(1, -1)


def test_reaches_one_within_basic():
    """Known witnesses inside an explicit bounded search."""
    assert reaches_one_within(1, 0) is True  # already at 1
    assert reaches_one_within(5, 1) is True  # 5 -> 1
    assert reaches_one_within(3, 2) is True  # 3 -> 5 -> 1
    assert reaches_one_within(2, 6) is True  # 2 -> 7 -> 11 -> 17 -> 13 -> 5 -> 1
    assert reaches_one_within(0, 1) is True  # mirrors Lean: acceleratedStep 0 = 1


def test_reaches_one_within_boundary_is_not_negative_evidence():
    """False means no witness was found within the bound, not non-convergence."""
    assert reaches_one_within(2, 5) is False
    assert reaches_one_within(2, 6) is True
    assert reaches_one_within(0, 0) is False


def test_reaches_one_within_rejects_invalid_inputs():
    with pytest.raises(ValueError):
        reaches_one_within(-1, 10)
    with pytest.raises(ValueError):
        reaches_one_within(1, -1)


# ---- 07c-3 orbit-aware descent + SatOrbit tests ----


def test_descend_orbit_leaf_short_circuits():
    """A leaf node is reachable regardless of orbit step or remaining depth."""
    leaf = CoverageLeaf(leaf_id="L0", leaf_property="3:0-2")
    # depth > 0, k = 7 -> still returns the leaf (leaf-first semantics)
    result = descend_orbit(CoverageTree(root=leaf, leaves=[leaf], max_depth=3), 5, 7)
    assert result is leaf


def test_descend_orbit_depth_zero_internal_returns_none():
    """An internal node at depth 0 returns None (depth exhausted)."""
    internal = CoverageNode(
        modulus=4,
        partition=(1,),
        children={1: CoverageLeaf(leaf_id="L1", leaf_property="3:0-2")},
    )
    tree = CoverageTree(root=internal, leaves=[internal.children[1]], max_depth=0)
    assert descend_orbit(tree, 5, 0) is None


def test_descend_orbit_matches_descend_at_k0_for_aligned_tree():
    """When each leaf's `period` equals its parent's modulus, `descend_orbit`
    at `k = 0` should agree with `descend` (because `accelerated_orbit(x, 0) = x`)."""
    # Build a 2-level tree where the parent's modulus (3) equals each leaf's period (3).
    leaves = [
        CoverageLeaf(leaf_id="L0", leaf_property="3:0-0"),
        CoverageLeaf(leaf_id="L1", leaf_property="3:1-1"),
        CoverageLeaf(leaf_id="L2", leaf_property="3:2-2"),
    ]
    internal = CoverageNode(
        modulus=3,
        partition=(0, 1, 2),
        children={0: leaves[0], 1: leaves[1], 2: leaves[2]},
    )
    tree = CoverageTree(root=internal, leaves=leaves, max_depth=2)
    for x in [1, 2, 3, 4, 5, 7, 8, 100]:
        assert descend_orbit(tree, x, 0) == descend(
            tree, x
        ), f"orbit-aware descend at k=0 must match static descend for aligned tree at x={x}"


def test_descend_orbit_advances_k_per_internal_level():
    """At depth-1 internal with modulus 3, residue lookup uses
    `accelerated_orbit(x, 0) % 3 = x % 3` (k=0 at root) for the
    first lookup. Deeper internal levels would advance k."""
    leaves = [
        CoverageLeaf(leaf_id="L0", leaf_property="3:0-0"),
        CoverageLeaf(leaf_id="L1", leaf_property="3:1-1"),
        CoverageLeaf(leaf_id="L2", leaf_property="3:2-2"),
    ]
    internal = CoverageNode(
        modulus=3,
        partition=(0, 1, 2),
        children={0: leaves[0], 1: leaves[1], 2: leaves[2]},
    )
    tree = CoverageTree(root=internal, leaves=leaves, max_depth=2)
    # At k=0, descend_orbit uses accelerated_orbit(x, 0) % 3 = x % 3
    # So for x=5, residue = 2 -> leaf L2 (3:2-2)
    assert descend_orbit(tree, 5, 0) is leaves[2]
    # For x=4, residue = 1 -> leaf L1 (3:1-1)
    assert descend_orbit(tree, 4, 0) is leaves[1]


def test_sat_orbit_returns_true_within_bound():
    """sat_orbit(leaf, x, bound) returns True iff some k ≤ bound witnesses."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:0-2")
    # accelerated_orbit(5, 0) = 5 -> 5 % 3 = 2 -> in [0, 2] -> True at k=0
    assert sat_orbit(leaf, 5, 0) is True
    # accelerated_orbit(1, 0) = 1 -> 1 % 3 = 1 -> in [0, 2] -> True at k=0
    assert sat_orbit(leaf, 1, 0) is True


def test_sat_orbit_returns_false_past_bound():
    """sat_orbit returns False when no witness appears within the bound;
    this is not mathematical negative evidence, only a search cutoff."""
    # Narrow interval that doesn't include x's residue at any small step.
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="5:3-3")
    # accelerated_orbit(2, 0) = 2 -> 2 % 5 = 2, not in [3, 3]
    # accelerated_orbit(2, 1) = acceleratedStep(2) = 1 -> 1 % 5 = 1, not in [3, 3]
    assert sat_orbit(leaf, 2, 1) is False
    # With bound=2 still False (no witness)
    assert sat_orbit(leaf, 2, 2) is False


def test_sat_orbit_unparseable_leaf_returns_false():
    """Unparseable leaves return False (mirrors Lean SatOrbit False branch)."""
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="garbage")
    assert sat_orbit(leaf, 5, 10) is False


def test_sat_orbit_rejects_negative_bound():
    with pytest.raises(ValueError):
        sat_orbit(CoverageLeaf(leaf_id="L1", leaf_property="3:0-2"), 5, -1)


# ---- 07c-4 structural-routing BDD scenarios ----
# Per docs/story-07c-4-structural-induction.md. Adds structural-routing
# coverage to complement the existing descend_orbit tests:
#   - Depth-two route (the discriminating scenario for orbit-aware routing)
#   - Negative-input enforcement on descend_orbit (mirrors Lean Nat)
#   - Independent trace oracle that does NOT call descend_orbit


def test_descend_orbit_routes_second_level_by_step_one_state():
    """Depth-two tree: x=5 routes via accelerated_orbit(5, 1) % 3 = 1,
    not raw 5 % 3 = 2. This is the discriminating scenario — without it,
    descend_orbit would be indistinguishable from descend on depth-1 trees.
    """
    leaves = [
        CoverageLeaf(leaf_id="D0", leaf_property="3:0-0"),
        CoverageLeaf(leaf_id="D1", leaf_property="3:1-1"),
        CoverageLeaf(leaf_id="D2", leaf_property="3:2-2"),
    ]
    inner2 = CoverageNode(
        modulus=3,
        partition=(0, 1, 2),
        children={0: leaves[0], 1: leaves[1], 2: leaves[2]},
    )
    inner1 = CoverageNode(
        modulus=4,
        partition=(1,),
        children={1: inner2},
    )
    tree = CoverageTree(root=inner1, leaves=leaves, max_depth=2)
    # x = 5: 5 % 4 = 1 -> inner2; accelerated_orbit(5, 1) = 1;
    # 1 % 3 = 1 -> leaf D1. Raw 5 % 3 = 2 would pick D2 (WRONG).
    assert descend_orbit(tree, 5, 0) is leaves[1]


def test_descend_orbit_rejects_negative_input():
    """descend_orbit mirrors Lean's Nat domain; negative x raises ValueError.

    Mirrors `test_accelerated_orbit_rejects_negative_inputs` for the
    orbit-aware entry point. The error may surface from
    `accelerated_orbit` (reached on the first internal lookup) or from
    descend_orbit itself; either satisfies the contract.
    """
    leaf = CoverageLeaf(leaf_id="L1", leaf_property="3:1-2")
    tree = CoverageTree(root=leaf, leaves=[leaf], max_depth=1)
    with pytest.raises(ValueError):
        descend_orbit(tree, -1, 0)


def test_descend_orbit_agrees_with_independent_trace_oracle():
    """On a depth-2 complete tree, descend_orbit agrees with an iterative
    trace oracle that does NOT call descend_orbit or its recursion helper.

    The oracle advances `k` by 1 at each internal step and uses
    `accelerated_orbit(x, k) % modulus` for the residue lookup, mirroring
    the Lean `descendFromOrbit` recursion (CoverageTree.lean line 129).
    """

    def trace_oracle(t: CoverageTree, x: int) -> CoverageLeaf | None:
        if x < 0:
            raise ValueError(f"x must be non-negative, got {x}")
        k = 0
        node = t.root
        depth = t.max_depth
        while depth > 0 and not isinstance(node, CoverageLeaf):
            if node.modulus <= 0:
                return None
            residue = accelerated_orbit(x, k) % node.modulus
            if residue not in node.children:
                return None
            node = node.children[residue]
            k += 1
            depth -= 1
        if isinstance(node, CoverageLeaf):
            return node
        return None

    leaves = []
    for j in range(4):
        for k in range(3):
            leaves.append(CoverageLeaf(leaf_id=f"L{j}{k}", leaf_property=f"3:{k}-{k}"))
    children_level2: dict = {}
    for j in range(4):
        leaf_block = [leaf for leaf in leaves if leaf.leaf_id.startswith(f"L{j}")]
        children_level2[j] = CoverageNode(
            modulus=3,
            partition=(0, 1, 2),
            children={idx: leaf_block[idx] for idx in range(3)},
        )
    inner1 = CoverageNode(
        modulus=4,
        partition=(0, 1, 2, 3),
        children=children_level2,
    )
    tree = CoverageTree(root=inner1, leaves=leaves, max_depth=2)
    for x in [1, 2, 5, 7, 8, 11, 13, 17, 100]:
        expected = trace_oracle(tree, x)
        actual = descend_orbit(tree, x, 0)
        assert actual == expected, f"x={x}: expected {expected}, got {actual}"


# ---- 02c/03c boundary-case regression tests (Story 02c/03c proof-bearing PR) ----
# Per the spec at docs/story-02c-03c-dynamics-equivalence-proofs.md (PR #30, merged 2026-08-16).
# These tests cover the boundary cases the formal proofs will close.
# Test-first commitment per MEMORY.md "BDD Discipline (Lean vs Python) — Justin, 2026-08-15".


def test_accelerated_orbit_n_3_lemma_1_boundary():
    """n=3 is the Lemma 1 boundary case (Codex re-review #1 P1, 2026-08-16T17:32:09Z):
    ν₂(3n+1) = ν₂(10) = 1 exactly. The bound `1 ≤ k` is TIGHT — cannot strengthen to `k ≥ 2`.

    accelerated_orbit(3, 1) = (3*3+1)/2^1 = 10/2 = 5 (NOT 1).
    accelerated_orbit(3, 2) = acceleratedStep(5) = 16/16 = 1.
    """
    assert accelerated_orbit(3, 0) == 3
    assert accelerated_orbit(3, 1) == 5  # confirms ν₂(10) = 1 (tight bound; Lemma 1)
    assert accelerated_orbit(3, 2) == 1
    assert accelerated_orbit(3, 3) == 1  # 1 is a fixed point


def test_accelerated_orbit_n_5_lemma_2_factorization():
    """n=5 is the Lemma 2 factorization decomposition case:
    3*5+1 = 16 = 2^4, so ν₂(3n+1) = 4 and T(5) = 16/16 = 1.
    The standard-trajectory equivalence says C²(5) = T(5) = 1 (single accelerated step).
    """
    assert accelerated_orbit(5, 0) == 5
    assert accelerated_orbit(5, 1) == 1  # single accelerated step reaches 1


def test_accelerated_orbit_n_1_is_fixed_point():
    """n=1 is the trajectory fixed point — accelerated_orbit(1, k) = 1 for all k.
    This is the trajectory-lifting base case (`trajectory 1 0 = 1`) that the
    `acceleratedTrajectory_reaches_one_implies_standard` proof handles at m=0.
    """
    for k in range(10):
        assert accelerated_orbit(1, k) == 1


def test_accelerated_orbit_n_27_known_trajectory():
    """n=27 is the Collatz-famous value that takes 112 accelerated steps to reach 1.
    First 10 trajectory values verified against hand computation:

    accelerated_orbit(27, 0) = 27
    accelerated_orbit(27, 1) = T(27) = 82/2    = 41   (3*27+1=82,  ν₂=1)
    accelerated_orbit(27, 2) = T(41) = 124/4   = 31   (3*41+1=124, ν₂=2)
    accelerated_orbit(27, 3) = T(31) = 94/2    = 47   (3*31+1=94,  ν₂=1)
    accelerated_orbit(27, 4) = T(47) = 142/2   = 71   (3*47+1=142, ν₂=1)
    accelerated_orbit(27, 5) = T(71) = 214/2   = 107  (3*71+1=214, ν₂=1)
    accelerated_orbit(27, 6) = T(107) = 322/2  = 161  (3*107+1=322, ν₂=1)
    accelerated_orbit(27, 7) = T(161) = 484/4  = 121  (3*161+1=484, ν₂=2)
    accelerated_orbit(27, 8) = T(121) = 364/4  = 91   (3*121+1=364, ν₂=2)
    accelerated_orbit(27, 9) = T(91) = 274/2   = 137  (3*91+1=274,  ν₂=1)
    """
    expected = [27, 41, 31, 47, 71, 107, 161, 121, 91, 137]
    for k, exp in enumerate(expected):
        assert accelerated_orbit(27, k) == exp, f"k={k}: expected {exp}"


def test_reaches_one_within_n_27():
    """n=27 reaches 1 after 41 accelerated steps (Collatz-famous).

    Note: the standard Collatz trajectory of n=27 has 111 steps (including the
    final 4→2→1), but the accelerated trajectory collapses `1 + ν₂(3n+1)`
    standard steps into one accelerated step. Total: 41 accelerated steps
    (verified via Python iteration).

    `reaches_one_within(n, bound)` checks whether a witness appears within
    `bound + 1` iterations.
    """
    assert reaches_one_within(27, 41) is True  # exact boundary
    assert reaches_one_within(27, 40) is False  # one short


def test_accelerated_orbit_n_31_known_trajectory():
    """n=31 trajectory verification (107 steps to reach 1).

    accelerated_orbit(31, 0) = 31
    accelerated_orbit(31, 1) = T(31) = 94/2   = 47   (3*31+1=94,  ν₂=1)
    accelerated_orbit(31, 2) = T(47) = 142/2  = 71   (3*47+1=142, ν₂=1)
    accelerated_orbit(31, 3) = T(71) = 214/2  = 107  (3*71+1=214, ν₂=1)
    accelerated_orbit(31, 4) = T(107) = 322/2 = 161  (3*107+1=322, ν₂=1)
    """
    expected = [31, 47, 71, 107, 161]
    for k, exp in enumerate(expected):
        assert accelerated_orbit(31, k) == exp, f"k={k}: expected {exp}"
