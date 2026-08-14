# Story 07c / round-5 (07c-3) — Proof rewrite: orbit-aware descent preserves the semantic invariant

_Generated 2026-08-14. Branch `story-07c-3-proof-rewrite` off `a7ab82f` (PR #17 merge)._

## Motivation

PR #15 (round-4) landed `coverage_tree_soundness` at `preparatory` with the
structural conclusion

```
∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l
```

PR #16 (07c-1) added the semantic `Sat` predicate (static, on raw `x`)
and `WellFormed`. PR #17 (07c-2) added `accelerated_orbit` / `ReachesOne`
as definitions and **removed** the vacuous `ReachesOne x` claim from the
soundness theorem.

For promotion to `formally established`, the existing PR #17 P0 review
asks for **a semantic transition invariant that descent preserves**,
*before* deriving a convergence conclusion. This story delivers that
invariant.

## What 07c-3 adds

1. **Orbit-aware descent.** A new `descendFromOrbit` / `descendOrbit`
   pair that, at each internal level, looks up the child by
   `accelerated_orbit x k % m` (where `k` is the depth index), instead
   of `x % m`. The structural recursion is unchanged.

2. **Orbit-aware semantic predicate.** A new `SatOrbit` predicate:

   ```
   SatOrbit t x l := ∃ k,
     lo ≤ accelerated_orbit x k % period ∧
     accelerated_orbit x k % period ≤ hi
   ```

   where `(period, lo, hi)` is parsed from `l.leafProperty` via
   `leanInterval`. This is the orbit-aware analogue of `Sat` (07c-1).

3. **New soundness theorem.** `coverage_tree_soundness_orbit` states
   that, under the existing `ValidTree` + `IsComplete` hypotheses
   (plus a structural alignment hypothesis — see below), orbit-aware
   descent lands at a leaf `l` that satisfies `SatOrbit t x l` AND
   the structural `verified` predicate.

4. **Python mirror.** `descend_orbit(tree, x, k)` and
   `sat_orbit(leaf, x, bound)` in `tree.py`, with bounded-search
   semantics for `sat_orbit` and differential tests against the Lean
   definitions.

5. **Tests.** New pytest cases covering:
   - depth-0 / depth-1 / depth-`maxDepth` boundary cases,
   - `descend_orbit` agrees with `descend` at `k = 0` for trees where
     the parent's modulus matches the leaf's period,
   - `sat_orbit` returns `False` past the bound, and `True` only when
     a witness orbit step actually lands in `[lo, hi]`.

## Structural alignment hypothesis

`SatOrbit t x l` references `l`'s own `period`, but `descendOrbit` only
routes by the parent's modulus. These coincide when, for every leaf `l`
at depth `d`, `l.period` equals the modulus of its parent internal
node. Without this alignment, `descendOrbit t x 0 = some l` does not
imply `SatOrbit t x l`.

For 07c-3 we add the alignment as an explicit hypothesis on the
theorem (`OrbitAlignedTree t`), leaving the proof that well-formed
trees satisfy it for follow-up work. `OrbitAlignedTree` is defined as
a structural predicate paralleling `IsCompleteAux`, and it captures:

- A leaf is aligned iff its declared `period > 0`.
- An internal node is aligned iff every child subtree is aligned.

The full proof that `ValidTree t ∧ IsComplete t ⇒ OrbitAlignedTree t`
requires additional structural work and is admitted via `sorry` in
this story.

## Claim level

**Preparatory.** Definitions + Python mirror + tests are landed; the
main theorem is stated with `sorry`. Promotion to `formally
established` requires:

- Closing the `sorry` on `coverage_tree_soundness_orbit`,
- A proof that well-formed trees are orbit-aligned (or a refined
  tree model that builds the alignment in),
- The follow-up derivation of `ReachesOne x` (07c-4 or later), which
  requires either (a) all leaves to declare `(1, 0, 0)` so the orbit
  bound is trivial, or (b) a separate descent-based proof that every
  positive integer's accelerated orbit reaches 1.

## Imports / footprint

No new Mathlib imports. The orbit-aware definitions reuse `acceleratedStep`
(defined in `Basic.lean`) and the existing `leanInterval` parser. This
keeps the local `lake build CollatzResearch.CoverageTree` invocation
inside its current dependency surface; CI cold-cache cost should match
PR #17 (~2 min warm, ~3 min cold).

## Test plan

1. **Local narrow Lean build.** `lake build CollatzResearch.CoverageTree`
   must succeed (no new imports means no new transitive dependencies).
2. **Python pytest.** New tests run alongside the existing
   `test_coverage_tree.py` suite. Bounded search cases assert
   `sat_orbit` matches `sat` at `k = 0`.
3. **CI gate.** Push branch → wait for `Lean CI` (warm cache expected)
   and `Python CI` → fix from CI logs.

## Non-goals

- No derivation of `ReachesOne x` in this story.
- No changes to `Basic.lean` / `Dynamics.lean` / `Equivalence.lean`.
- No changes to the existing static `Sat` / `WellFormed` / `descend`.
- No changes to `coverage_tree_soundness` (the structural theorem from
  PR #15 / 07c-2 stays untouched).

## Follow-ups

- 07c-4 (or later): close the `coverage_tree_soundness_orbit` sorry,
  prove `OrbitAlignedTree` for well-formed trees, and add the
  `ReachesOne x` derivation as a separate `coverage_tree_convergence`
  theorem.
