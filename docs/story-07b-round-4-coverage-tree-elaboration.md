# Story 07b / round-4 — Substantive CoverageTree elaboration

**Branch:** `story-07b-round-4-coverage-tree-elaboration` (from `b2cde0f`)
**Milestone:** M4 Finite coverage (release-blocker for the formal soundness theorem)
**Status:** substantive elaboration landed (commit `ed80287`); CI green (Lean CI `31652436030`, Python CI `31652436022`); claim level demoted to `preparatory` per Codex re-review (review `4922136689` on PR #15, submitted 2026-08-12T23:55:53Z)
**Owner:** Justin
**Carry-over from:** PR #14 (round-3 closure, Codex request-changes, P0 + P1)

## Context

PR #14 (round-3, branch `story-07b-coverage-tree-soundness` at `a94bfab`)
closed the `coverage_tree_soundness` sorry via the `hconsistent` hypothesis
(every leaf in `t.leaves` has non-empty `leafId`). Codex reviewed
request-changes (submitted 2026-08-12T22:43:39Z) with two criticisms:

- **P0** — *the result is not a finite-coverage theorem.* With
  `rootDomain _ = Set.univ` and `satisfies x l := l.leafId ≠ ""`
  (the `x` binder is dead), the statement reduces to a global
  string-non-emptiness claim about `t.leaves`. It engages with none of
  `t`'s partition / child structure or any input's path. The proof
  mechanics are valid; the *statement* is semantically empty with
  respect to finite coverage.

- **P1** — *`hconsistent` is untrusted.* Python `check_tree` does not
  enforce `leaf_id_non_empty`, and the Lean `t : CoverageTree` is a
  Lean-native record without provenance to a checker artifact. Compare
  Story 06b's `check_certificate_sound` whose `LeanAccepts` rides on
  the JSONL importer. Without an analogous import path, `hconsistent`
  is a free-floating hypothesis.

The structurally-distinct placeholder pattern (PR #13 Codex P1 fix)
ensured the proof body required real work, not `rfl`. It did not ensure
the *statement* engaged with finite-coverage semantics. PR #14 is
therefore not the M4 closure — `coverage_tree_soundness` must be
substantively re-elaborated.

## Acceptance criteria (BDD)

1. **`CoverageTree` carries internal-node structure.** Add `CoverageNode`
   (modulus, partition, children) to the Lean module.
   `CoverageTree.root : CoverageNode`. The `leaves : List CoverageLeaf`
   descriptor list is preserved (Python alignment — already in
   `python/collatz_research/tree.py`).

2. **`descend` is defined.** A recursive function
   `descend : CoverageTree → Nat → Option CoverageLeaf` that, starting
   from root, follows `x.modulus` at each internal node and recurses
   into the matching child. Returns `none` if at any step the residue
   has no matching child.

3. **`rootDomain` is a coverage predicate, not `Set.univ`.** Define
   `rootDomain t : Set Nat := { x | ∃ l, descend t x = some l }`. The
   theorem's quantifier over `x` becomes non-trivial: only inputs
   whose path actually terminates are covered.

4. **`satisfies` is `x`-indexed.** Define `satisfies t x l : Prop :=
   descend t x = some l`. The `x` binder is now genuinely used.

5. **`verified` engages with the tree.** Define `verified t l : Prop`
   so that it depends on `t` (e.g., `l ∈ t.leaves ∧ l.leafProperty ≠ ""`,
   plus a marker for a checker-validated tree — see (9) for the
   import bridge).

6. **`IsComplete` traces the partition cascade.** Define
   `IsComplete t := ∀ x, x ∈ rootDomain t → ∃ l, descend t x = some l ∧
   verified t l`. The hypothesis says: every `x` whose path terminates
   reaches a verified leaf.

7. **`coverage_tree_soundness` is provable without `sorry`.** The proof
   should use the partition invariants and the cascade structure, not
   reduce to a string-non-emptiness check. Sketch:
   ```lean
   theorem coverage_tree_soundness (t : CoverageTree)
       (hv : ValidTree t) (hc : IsComplete t) :
       ∀ x, x ∈ rootDomain t →
         ∃ l, l ∈ t.leaves ∧ verified t l ∧ satisfies t x l := by
     intro x hx
     obtain ⟨l, hdesc, hv'⟩ := hc x hx
     exact ⟨l, hv'.1, hv'.2, hdesc⟩
   ```
   Shape depends on the elaborated definitions.

8. **Python `check_tree` enforces `leaf_id_non_empty`.** Mirror the
   hypothesis in the checker. Any tree that passes `check_tree` carries
   the assumption needed by the Lean proof. New check category
   `ERR_LEAF_ID_EMPTY`. Mutation test in `tests/test_coverage_tree.py`.

9. **Lean import bridge from a Python `check_tree` artifact.** Define a
   Lean parser for the JSONL schema (or a hand-written minimal importer
   covering the v1.0 schema) and a `LeanAccepts` predicate analogous to
   Story 06b. Documents the trust boundary. Absent the bridge,
   `verified t l` is checked at construction time but cannot be
   discharged from a checker artifact. **Optional for this round** —
   see *Risks*.

## Implementation outline

a. **Structural rewrite of `CoverageTree`.**
   ```lean
   structure CoverageNode where
     modulus : Nat
     partition : List Nat  -- residues; ordered, distinct, in [0, m)
     children : List (Nat × CoverageTree)  -- or indexed map
   structure CoverageTree where
     root : CoverageNode
     leaves : List CoverageLeaf
     maxDepth : Nat
   ```

b. **Partition invariants.** `ValidPartition : CoverageNode → Prop`
   (residues in `[0, m)`, sorted, distinct). `ValidTree :
   CoverageTree → Prop` (root valid, all subtrees valid, depth ≤
   `max_depth`).

c. **Redefine placeholders** per (3)–(6) above.

d. **Prove `coverage_tree_soundness`** under `ValidTree t` and
   `IsComplete t`.

e. **Python `check_tree` `leaf_id_non_empty`.** New category
   `ERR_LEAF_ID_EMPTY`. Validation in `check_tree` after
   `leaves_consistent`. Test in `tests/test_coverage_tree.py`.

f. **Import bridge (deferred if too costly).** Lean importer for the
   v1.0 JSONL schema, proof of
   `imported_implies_Valid`, replace `verified t l` with a
   checker-discharged predicate. If unaffordable, document the trust
   gap.

## Test plan

1. **Local Lean validation.** `lake build CollatzResearch.CoverageTree`
   succeeds with **zero `sorry` warnings** in `CoverageTree.lean`.

2. **Round-trip descent test.** Construct a tree with `max_depth = 2`,
   modulus 3, partition `[1, 2]` at root; verify `descend t 1` returns
   the leaf under residue 1, `descend t 2` returns the leaf under
   residue 2, `descend t 0 = none`.

3. **`ValidPartition` mutation tests.** Out-of-range, negative, and
   duplicate residues all raise matching categories.

4. **Python `leaf_id_non_empty` mutation tests.** Empty `leaf_id`
   raises `ERR_LEAF_ID_EMPTY`.

5. **Differential.** Python `reachable_leaves` set equals Lean
   `descend`-derived set (modulo ordering).

6. **Existing tests stay green.** `tests/test_coverage_tree.py`
   continues to pass.

## Dependencies

- Story 07 (PR #13, merge commit `b2cde0f`) ✓ merged
- PR #14 (round-3) is **not** merged — Codex request-changes. This
  round supersedes it.
- Story 06b `check_certificate_sound` import pattern (for the optional
  import bridge in (9)).

## Non-goals

- No universal Collatz proof claim from coverage trees.
- No replacement of the residue-cascade semantics; the cascade is the
  fixed story.
- No new Lean-side package dependencies beyond `Mathlib` and what is
  already used.
- No replacement of `descend` with a different definition.
- Import bridge (9) is optional; if too costly, ship without it and
  document the gap.

## Risks

- **Import bridge complexity.** A Lean-side JSONL parser covering the
  v1.0 schema is non-trivial (~150 lines + non-trivial proofs). If too
  costly, ship without it and M4 stays partial pending a later story.
- **`descend` termination.** Recursion on a finite tree is
  well-founded; Lean requires explicit decreasing argument. Easy via
  tree-height induction.
- **Cycle safety.** Bounded by `max_depth` and `ValidTree`.

## Acceptance command

```bash
lake build CollatzResearch.CoverageTree  # zero sorry
make python-ci                            # corpus + mutation tests green
```

## Carry-over notes

- **PR #14** (`story-07b-coverage-tree-soundness` at `a94bfab`) is the
  round-3 closure branch and remains open with Codex
  request-changes. Recommend closing without merge once round-4 lands.

- **`coverage_tree_soundness` claim level.** Demoted to `preparatory`
  per Codex re-review (review `4922136689` on PR #15 commit `ed80287`,
  submitted 2026-08-12T23:55:53Z). The substantive proof establishes
  structural *reachability* of a nonempty leaf descriptor over positive
  naturals: `rootDomain` is independent of `descend` (`n > 0`);
  `IsCompleteAux` is a structural invariant
  (`HasAllResidues` + verified leaves) with no `descend` in the
  definition; the proof uses strong induction on remaining depth and
  consumes both `ValidTree` and `IsComplete` hypotheses (no longer
  a projection). The theorem does **not** formalize the declared
  `leafProperty` for the reached input, nor relate the tree to
  Collatz/Syracuse dynamics. Promoting back to `formally established`
  requires (a) a semantic `leafProperty`-indexed predicate, and (b) a
  proof that `descend` lands a witness satisfying it. M4 Finite
  coverage stays open.
