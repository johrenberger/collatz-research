"""Coverage-tree model and checker (Story 07, M4 Finite coverage).

A `CoverageTree` is a rooted tree whose internal nodes carry a residue
partition (residues in `[0, m)`, non-bool ints, no duplicates; coverage
of `[0, m)` is a tree-level concept distinct from partition validity)
and one child per residue class. Leaves carry a `leaf_property` symbol.

Checks (per `check_tree`, ordered):

1. `acyclic` — depth ≤ `max_depth` and no node is revisited through its
   ancestry (tracked by `id()` along the parent → child path).
2. `leaves_consistent` — the top-level `leaves` field is a one-to-one
   match with leaves reachable from `root`, and `leaf_id` is unique.
   (Codex review P1.1: arbitrary/missing/duplicate descriptors
   otherwise pass `check_tree`.)
3. `disjoint` — every internal node's partition is partition-valid.
4. `has_child_for_each_declared_residue` — at every internal node,
   every residue class declared in the partition has a child.
   Code-named this way (not `is_complete`) because partition-completeness
   is NOT full coverage of `[0, m)`; the latter depends on a
   `rootDomain` predicate introduced in the Story 07 follow-up
   (Codex review naming note).

External interchange (`from_dict`) is fail-closed: malformed input maps
to `CoverageTreeError(ERR_INVALID_NODE, ...)` rather than leaking
`TypeError` / `ValueError` / `KeyError` (Codex review P2).

Exporters + the Python checker iterate children in sorted-by-residue
order, so round-trips and external checks are deterministic.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

# Stable error categories; uppercase. Mirrors the partitions.py style.
ERR_NOT_CHILD_TOTAL = "TREE_NOT_CHILD_TOTAL"
ERR_NOT_DISJOINT = "TREE_NOT_DISJOINT"
ERR_HAS_CYCLE = "TREE_HAS_CYCLE"
ERR_LEAVES_MISMATCH = "TREE_LEAVES_MISMATCH"
ERR_LEAF_ID_EMPTY = "TREE_LEAF_ID_EMPTY"
ERR_INVALID_NODE = "TREE_INVALID_NODE"

EXPECTED_SCHEMA = "collatz-research/coverage-tree@0.1.0"


class CoverageTreeError(Exception):
    """Raised when a coverage tree fails a check."""

    def __init__(self, category: str, message: str):
        self.category = category
        self.message = message
        super().__init__(f"{category}: {message}")


@dataclass(frozen=True)
class CoverageLeaf:
    """A leaf in a coverage tree."""

    leaf_id: str
    leaf_property: str


@dataclass
class CoverageNode:
    """An internal node: residue partition + one child per residue."""

    modulus: int
    partition: tuple[int, ...]
    children: dict[int, CoverageNode | CoverageLeaf] = field(default_factory=dict)


@dataclass
class CoverageTree:
    """Rooted coverage tree with a depth bound.

    `leaves` is the top-level leaf descriptor list; `check_tree`
    enforces a one-to-one correspondence with leaves reachable from
    `root` (Codex review P1.1 — see `leaves_consistent`).
    """

    root: CoverageNode
    leaves: tuple[CoverageLeaf, ...]
    max_depth: int
    schema_version: str = "collatz-research/coverage-tree@0.1.0"


# ---- JSONL I/O (deterministic; sorted by residue; fail-closed) ----


def to_dict(tree: CoverageTree) -> dict[str, Any]:
    """Serialize a tree to a JSONL-ready dict, children sorted by residue."""

    def node_d(n: CoverageNode) -> dict[str, Any]:
        return {
            "kind": "internal",
            "modulus": n.modulus,
            "partition": list(n.partition),
            "children": {
                str(r): (
                    {
                        "kind": "leaf",
                        "leaf_id": c.leaf_id,
                        "leaf_property": c.leaf_property,
                    }
                    if isinstance(c, CoverageLeaf)
                    else node_d(c)
                )
                for r, c in sorted(n.children.items())
            },
        }

    return {
        "schema": tree.schema_version,
        "max_depth": tree.max_depth,
        "root": node_d(tree.root),
        "leaves": [
            {"leaf_id": lf.leaf_id, "leaf_property": lf.leaf_property} for lf in tree.leaves
        ],
    }


def from_dict(d: dict[str, Any]) -> CoverageTree:
    """Deserialize a tree from a dict. Fail-closed (Codex P2).

    Maps malformed input — wrong schema, missing fields, malformed
    values — to `CoverageTreeError(ERR_INVALID_NODE, ...)` rather than
    leaking `TypeError` / `ValueError` / `KeyError`.
    """
    if not isinstance(d, dict):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"expected JSON object, got {type(d).__name__}",
        )
    schema = d.get("schema")
    if schema != EXPECTED_SCHEMA:
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"unsupported schema: {schema!r}; expected {EXPECTED_SCHEMA!r}",
        )

    try:
        root = _node_from_dict(d["root"])
        leaves_data = d["leaves"]
        max_depth_raw = d["max_depth"]
    except (TypeError, ValueError, KeyError) as exc:
        raise CoverageTreeError(ERR_INVALID_NODE, f"malformed tree dict: {exc}") from exc

    if not isinstance(leaves_data, list):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"leaves must be list, got {type(leaves_data).__name__}",
        )
    if not isinstance(max_depth_raw, int) or isinstance(max_depth_raw, bool):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"max_depth must be int, got {type(max_depth_raw).__name__}",
        )

    try:
        leaves = tuple(
            CoverageLeaf(
                leaf_id=leaf["leaf_id"],
                leaf_property=leaf["leaf_property"],
            )
            for leaf in leaves_data
        )
    except (TypeError, KeyError) as exc:
        raise CoverageTreeError(ERR_INVALID_NODE, f"malformed leaf entry: {exc}") from exc

    return CoverageTree(
        root=root,
        leaves=leaves,
        max_depth=max_depth_raw,
        schema_version=schema,
    )


def _node_from_dict(n: Any) -> CoverageNode:
    """Internal: parse a single CoverageNode dict; fail-closed."""
    if not isinstance(n, dict):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"expected node object, got {type(n).__name__}",
        )
    try:
        kind = n["kind"]
        modulus = n["modulus"]
        partition = n["partition"]
        children_data = n["children"]
    except (KeyError, TypeError) as exc:
        raise CoverageTreeError(ERR_INVALID_NODE, f"node missing required field: {exc}") from exc

    if kind != "internal":
        raise CoverageTreeError(ERR_INVALID_NODE, f"expected internal node, got {kind!r}")
    if not isinstance(modulus, int) or isinstance(modulus, bool):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"modulus must be int, got {type(modulus).__name__}",
        )
    if not isinstance(partition, list | tuple):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"partition must be list/tuple, got {type(partition).__name__}",
        )
    if not isinstance(children_data, dict):
        raise CoverageTreeError(
            ERR_INVALID_NODE,
            f"children must be object, got {type(children_data).__name__}",
        )

    children: dict[int, CoverageNode | CoverageLeaf] = {}
    for r_str, c_d in children_data.items():
        try:
            r = int(r_str)
        except (TypeError, ValueError) as exc:
            raise CoverageTreeError(
                ERR_INVALID_NODE,
                f"child key {r_str!r} is not an int-convertible residue",
            ) from exc
        kind_c = c_d.get("kind") if isinstance(c_d, dict) else None
        if kind_c == "leaf":
            leaf_id = c_d.get("leaf_id")
            leaf_property = c_d.get("leaf_property")
            if not isinstance(leaf_id, str) or not isinstance(leaf_property, str):
                raise CoverageTreeError(
                    ERR_INVALID_NODE,
                    (
                        f"leaf fields must be str; got "
                        f"{type(leaf_id).__name__}/{type(leaf_property).__name__}"
                    ),
                )
            children[r] = CoverageLeaf(leaf_id=leaf_id, leaf_property=leaf_property)
        else:
            children[r] = _node_from_dict(c_d)

    return CoverageNode(
        modulus=modulus,
        partition=tuple(partition),
        children=children,
    )


# ---- Tree walks ----


def deterministic_children(
    n: CoverageNode,
) -> list[tuple[int, CoverageNode | CoverageLeaf]]:
    """Sorted-by-residue deterministic iteration order."""
    return [(r, n.children[r]) for r in sorted(n.children.keys())]


def reachable_leaves(root: CoverageNode) -> tuple[CoverageLeaf, ...]:
    """Walk the tree deterministically and return every leaf reachable
    from `root`. Prerequisite for `leaves_consistent` (Codex P1.1).
    """
    out: list[CoverageLeaf] = []

    def walk(n: CoverageNode) -> None:
        for _r, c in deterministic_children(n):
            if isinstance(c, CoverageLeaf):
                out.append(c)
            else:
                walk(c)

    walk(root)
    return tuple(out)


# ---- Checkers ----


def _is_disjoint_partition(modulus: int, partition: tuple[int, ...]) -> bool:
    """Partition is internally consistent: residues are non-bool ints in
    `[0, m)` with no duplicates. Does NOT check coverage of `[0, m)` —
    coverage is a separate invariant scoped under the Story 07 rootDomain
    follow-up.
    """
    for r in partition:
        if not isinstance(r, int) or isinstance(r, bool):
            return False
        if r < 0 or r >= modulus:
            return False
    return len(set(partition)) == len(partition)


def is_disjoint(tree: CoverageTree) -> bool:
    """`True` iff every internal node's partition is internally consistent."""

    def node_ok(n: CoverageNode) -> bool:
        if not _is_disjoint_partition(n.modulus, n.partition):
            return False
        return all(node_ok(c) if isinstance(c, CoverageNode) else True for c in n.children.values())

    return node_ok(tree.root)


def has_child_for_each_declared_residue(tree: CoverageTree) -> bool:
    """`True` iff at every internal node, every residue class declared in
    the partition has a child.

    Renamed from `is_complete` per Codex review naming note: this is
    **partition-completeness** (every declared residue → child), NOT
    full `[0, m)` coverage. Full root-domain coverage is a Story 07
    follow-up and depends on the tree's `rootDomain` predicate, which
    the Lean layer introduces in the next story.
    """

    def node_ok(n: CoverageNode) -> bool:
        if set(n.children.keys()) != set(n.partition):
            return False
        return all(node_ok(c) if isinstance(c, CoverageNode) else True for c in n.children.values())

    return node_ok(tree.root)


def leaves_consistent(tree: CoverageTree) -> bool:
    """`True` iff (Codex P1.1):
    - The set of leaves reachable from `root` equals `set(tree.leaves)`.
    - All `leaf_id` values across `tree.leaves` are unique.

    Catches arbitrary, missing, duplicate, and unreachable (but listed)
    descriptors in `CoverageTree.leaves`.
    """
    reachable = set(reachable_leaves(tree.root))
    top = set(tree.leaves)
    if reachable != top:
        return False
    if len({leaf.leaf_id for leaf in tree.leaves}) != len(tree.leaves):
        return False
    return True


def has_no_cycles(tree: CoverageTree) -> bool:
    """`True` iff depth ≤ `max_depth` at every node and no node is
    revisited through its parent → child ancestry. The cycle test is
    tracked by Python `id()` along the current descent path, so distinct
    subtrees with identical shape are not flagged.
    """

    def node_ok(n: CoverageNode, depth: int, path_ids: frozenset[int]) -> bool:
        if depth > tree.max_depth:
            return False
        if id(n) in path_ids:
            return False
        path_ids = path_ids | {id(n)}
        for c in n.children.values():
            if isinstance(c, CoverageNode):
                if not node_ok(c, depth + 1, path_ids):
                    return False
            else:
                if depth + 1 > tree.max_depth:
                    return False
        return True

    return node_ok(tree.root, 0, frozenset())


def leaf_id_non_empty(tree: CoverageTree) -> bool:
    """`True` iff every leaf in `tree.leaves` has a non-empty `leaf_id`.

    Mirrors the `hconsistent` hypothesis in the Lean
    `CoverageTree.lean` (Story 07b / round-4) so that any tree that
    passes `check_tree` carries the assumption needed by the
    `coverage_tree_soundness` proof body. Without this check, a tree
    with empty `leaf_id` entries would silently pass structural
    validation but fail to discharge the `verified` predicate in
    Lean — which requires `l.leafId ≠ ""`. Adding this check makes
    Python `check_tree` a faithful mirror of the Lean-side
    assumptions.
    """
    return all(leaf.leaf_id != "" for leaf in tree.leaves)


# ---- 07c-1 semantic leafProperty predicate (mirrors Lean) ----


def lean_interval(leaf: CoverageLeaf) -> tuple[int, int, int] | None:
    """Parse `leaf.leaf_property` as `"<period>:<lo>-<hi>"`.

    Returns `None` on any deviation (missing separators, non-numeric
    parts, etc.). Mirrors Lean's `leanInterval` (Story 07c / round-5,
    07c-1). Strict unsigned-decimal parser: rejects negative numbers
    (e.g. `"-1"`), leading signs, decimals, and empty parts. Mirrors
    Lean `String.toNat?` semantics.
    """
    try:
        s = leaf.leaf_property
    except AttributeError:
        return None
    parts = s.split(":", 1)
    if len(parts) != 2:
        return None
    period_str, range_str = parts
    if not period_str or not range_str:
        return None
    lo_hi = range_str.split("-", 1)
    if len(lo_hi) != 2:
        return None
    lo_str, hi_str = lo_hi
    if not lo_str or not hi_str:
        return None
    # Strict ASCII digits only. `str.isdigit()` accepts Unicode decimal
    # characters (e.g. Arabic-Indic ٠١٢٣, full-width ０１２３) that Lean
    # `String.toNat?` rejects, so this would diverge from Lean semantics.
    ascii_digits = set("0123456789")
    if not (
        period_str
        and all(c in ascii_digits for c in period_str)
        and lo_str
        and all(c in ascii_digits for c in lo_str)
        and hi_str
        and all(c in ascii_digits for c in hi_str)
    ):
        return None
    return (int(period_str), int(lo_str), int(hi_str))


def sat(leaf: CoverageLeaf, x: int) -> bool:
    """Static predicate: `x` is in the leaf's declared interval.

    A leaf declares a `(period, lo, hi)` tuple via `lean_interval`;
    `x` is in the interval iff `x % period ∈ [lo, hi]`. Returns
    `False` if the leaf's `leaf_property` doesn't parse. Mirrors
    Lean's `Sat`. For `period = 0`, mirrors Lean `Nat.mod n 0 = n`,
    i.e. `lo ≤ x ∧ x ≤ hi` (avoids Python's `ZeroDivisionError`).
    """
    interval = lean_interval(leaf)
    if interval is None:
        return False
    period, lo, hi = interval
    if period == 0:
        # Lean: Nat.mod n 0 = n by convention. Mirror that.
        return lo <= x <= hi
    return lo <= x % period <= hi


def accelerated_orbit(n: int, k: int) -> int:
    """Python mirror of Lean `accelerated_orbit`.

    `accelerated_orbit n 0 = n`;
    `accelerated_orbit n (k+1) = acceleratedStep (accelerated_orbit n k)`.
    Mirrors the Lean definition in `CoverageTree.lean` over natural inputs.
    Single step uses `acceleratedStep n = (3n+1)/2^ν₂(3n+1)`.
    """
    if n < 0:
        raise ValueError("n must be a natural number")
    if k < 0:
        raise ValueError("k must be a natural number")
    if k == 0:
        return n
    prev = accelerated_orbit(n, k - 1)
    val = 3 * prev + 1
    while val % 2 == 0:
        val //= 2
    return val


def reaches_one_within(n: int, bound: int) -> bool:
    """Bounded, untrusted exploration for reaching one.

    Lean's `ReachesOne n := ∃ k, accelerated_orbit n k = 1` is unbounded.
    This helper checks only whether a witness appears within the explicit
    step bound; `False` is not mathematical negative evidence.
    """
    if n < 0:
        raise ValueError("n must be a natural number")
    if bound < 0:
        raise ValueError("bound must be a natural number")
    cur = n
    for _ in range(bound + 1):
        if cur == 1:
            return True
        cur = accelerated_orbit(cur, 1)
    return False


def well_formed(leaf: CoverageLeaf) -> bool:
    """Static property of a leaf: its declared interval is structurally
    valid. The interval is a residue range modulo `period`: we need
    `period > 0`, `lo ≤ hi`, and `hi < period` (which also forces
    `lo < period`). Mirrors Lean's `WellFormed`. Returns `False` if
    the leaf's `leaf_property` doesn't parse.
    """
    interval = lean_interval(leaf)
    if interval is None:
        return False
    period, lo, hi = interval
    return period > 0 and lo <= hi and hi < period


def sat_orbit(leaf: CoverageLeaf, x: int, bound: int) -> bool:
    """Orbit-aware semantic predicate: `x`'s accelerated orbit reaches
    the leaf's declared interval at some step `k ≤ bound`.

    This is a bounded, untrusted exploration helper mirroring Lean's
    `SatOrbit`. Lean's `SatOrbit` is `∃ k, lo ≤ accelerated_orbit x k
    % period ∧ accelerated_orbit x k % period ≤ hi` (unbounded).
    Returning `False` here means no witness was found within `bound`,
    not mathematical negative evidence.

    Mirrors `Lean/CollatzResearch/CoverageTree.lean` `SatOrbit`
    (Story 07c / round-5, 07c-3).
    """
    if bound < 0:
        raise ValueError("bound must be a natural number")
    interval = lean_interval(leaf)
    if interval is None:
        return False
    period, lo, hi = interval
    if period == 0:
        # Lean: Nat.mod n 0 = n by convention. Mirror that.
        return any(lo <= accelerated_orbit(x, k) <= hi for k in range(bound + 1))
    for k in range(bound + 1):
        if lo <= accelerated_orbit(x, k) % period <= hi:
            return True
    return False


# ---- Descend (mirrors Lean's leaf-first `descendFrom`) ----


def _descend_from(depth: int, node: CoverageNode, x: int) -> CoverageLeaf | None:
    """Internal helper for `descend`. Leaf-first semantics:

    - Leaf: always reachable (returns the leaf regardless of remaining depth).
    - Internal at depth 0: returns None (depth exhausted).
    - Internal at depth > 0: follows `x % modulus` to the matching child
      and recurses with `depth - 1`.

    Mirrors `Lean/CollatzResearch/CoverageTree.lean` `descendFrom`
    (Story 07b / round-4 regression examples).
    """
    if isinstance(node, CoverageLeaf):
        return node
    # node is CoverageNode (internal)
    if depth == 0:
        return None
    r = x % node.modulus
    child = node.children.get(r)
    if child is None:
        return None
    return _descend_from(depth - 1, child, x)


def descend(tree: CoverageTree, x: int) -> CoverageLeaf | None:
    """Walk the tree from root following `x % modulus` at each internal
    node. Leaf-first: a leaf is reachable regardless of remaining
    depth; depth-0 internal returns None.

    Mirrors Lean's `descend` (Story 07b / round-4 regression).
    """
    return _descend_from(tree.max_depth, tree.root, x)


def _descend_from_orbit(
    depth: int, node: CoverageNode, x: int, k: int
) -> CoverageLeaf | None:
    """Internal helper for `descend_orbit`. Leaf-first semantics:

    - Leaf: always reachable (returns the leaf regardless of remaining depth).
    - Internal at depth 0: returns None (depth exhausted).
    - Internal at depth > 0: follows `accelerated_orbit(x, k) % modulus`
      to the matching child and recurses with `depth - 1` and `k + 1`.

    Mirrors `Lean/CollatzResearch/CoverageTree.lean` `descendFromOrbit`
    (Story 07c / round-5, 07c-3).
    """
    if isinstance(node, CoverageLeaf):
        return node
    # node is CoverageNode (internal)
    if depth == 0:
        return None
    r = accelerated_orbit(x, k) % node.modulus
    child = node.children.get(r)
    if child is None:
        return None
    return _descend_from_orbit(depth - 1, child, x, k + 1)


def descend_orbit(tree: CoverageTree, x: int, k: int) -> CoverageLeaf | None:
    """Orbit-aware descent: at each internal level, the residue lookup
    uses `accelerated_orbit(x, k) % modulus` (with `k` advancing by 1
    per internal step), instead of `x % modulus`. Leaf-first: a leaf
    is reachable regardless of remaining depth; depth-0 internal
    returns None.

    Mirrors Lean's `descendOrbit` (Story 07c / round-5, 07c-3). For
    `k = 0` and trees where each leaf's `period` equals its parent's
    modulus, `descend_orbit(tree, x, 0)` agrees with
    `descend(tree, x)`.
    """
    return _descend_from_orbit(tree.max_depth, tree.root, x, k)


def check_tree(tree: CoverageTree) -> None:
    """Run acyclic → leaves-consistent → disjoint → child-total → leaf-id checks.

    Order rationale:
    - `acyclic` first: a real ancestry cycle makes downstream recursion
      unsafe.
    - `leaves_consistent` next: structural coherence; walks the tree
      cheaply to cross-check the top-level field.
    - `disjoint` and `child_total` last: same internal structure, runs
      only after structural checks pass.
    - `leaf_id_non_empty` last: depends on the descriptor list
      being structurally sound (covered by `leaves_consistent`); this
      check validates the descriptor fields that the Lean
      `coverage_tree_soundness` proof body's `verified` predicate
      depends on.
    """
    if not has_no_cycles(tree):
        raise CoverageTreeError(ERR_HAS_CYCLE, "tree revisits a node or exceeds max_depth")
    if not leaves_consistent(tree):
        raise CoverageTreeError(
            ERR_LEAVES_MISMATCH,
            (
                "tree.leaves does not match leaves reachable from root "
                "(missing, extra, unreachable-but-listed, or duplicate leaf_id)"
            ),
        )
    if not is_disjoint(tree):
        raise CoverageTreeError(ERR_NOT_DISJOINT, "tree has overlapping or out-of-range residues")
    if not has_child_for_each_declared_residue(tree):
        raise CoverageTreeError(
            ERR_NOT_CHILD_TOTAL,
            "tree is missing children for some residues declared in the partition",
        )
    if not leaf_id_non_empty(tree):
        raise CoverageTreeError(
            ERR_LEAF_ID_EMPTY,
            (
                "tree.leaves contains a leaf with empty leaf_id "
                "(required by the Lean coverage_tree_soundness "
                "proof body's `verified` predicate)"
            ),
        )


# ---- Sample demonstrator ----


def sample_tree() -> CoverageTree:
    """Depth-2 demonstrator: modulus 4 root → odd residues (1, 3) →
    modulus 3 each → all residues (1, 2) → 4 leaves total.

    The root partition is intentionally non-covering (only odd residues
    at modulus 4) so the demonstrator exercises the deliberate
    distinction between partition-completeness (`has_child_for_each_...`)
    and the still-followup root-domain coverage property.
    """
    leaves = (
        CoverageLeaf(leaf_id="leaf_1_2", leaf_property="L(1,2)"),
        CoverageLeaf(leaf_id="leaf_2_2", leaf_property="L(2,2)"),
        CoverageLeaf(leaf_id="leaf_4_2", leaf_property="L(4,2)"),
        CoverageLeaf(leaf_id="leaf_5_2", leaf_property="L(5,2)"),
    )
    inner1 = CoverageNode(
        modulus=3,
        partition=(1, 2),
        children={1: leaves[0], 2: leaves[1]},
    )
    inner2 = CoverageNode(
        modulus=3,
        partition=(1, 2),
        children={1: leaves[2], 2: leaves[3]},
    )
    root = CoverageNode(modulus=4, partition=(1, 3), children={1: inner1, 3: inner2})
    return CoverageTree(root=root, leaves=leaves, max_depth=2)
