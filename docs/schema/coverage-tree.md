# Coverage-tree JSONL schema (Story 07)

Each tree is a single JSON object on one line of JSONL.

Schema version: `collatz-research/coverage-tree@0.1.0`.

## Required keys

- `schema` — must equal `"collatz-research/coverage-tree@0.1.0"`.
- `max_depth` — non-negative integer bound on root-to-leaf path length.
- `root` — internal node (see below).
- `leaves` — list of leaf descriptors.

## Internal node (`{"kind": "internal", ...}`)

- `modulus` — non-negative integer `m` (≥ 1).
- `partition` — list of integer residues in `[0, m)`; covers ℤ/mℤ
  disjoint (delegated to `partitions.is_partition`).
- `children` — map from residue (as string) to child. The key set must
  equal `partition` (so the tree is complete at this node).

## Leaf (`{"kind": "leaf", ...}`)

- `leaf_id` — unique string identifier.
- `leaf_property` — symbolic conclusion the leaf verifies.

## Determinism

Exporters and the Python checker iterate children in sorted-by-residue
order so that `to_dict(tree)` is a deterministic function of `tree`.
Round-trip equality (`to_dict(from_dict(d)) == d`) holds for any
well-formed input.
