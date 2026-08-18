# Story 07c-2 — `coverage_tree_soundness_full` promotion (preparatory → formally established)

Status: **spec draft, awaiting Codex review at spec stage.** Companion-theorem approach per Justin's recommendation 2026-08-18T00:16 GMT+2.

## Context

M4 Finite coverage requires closing the `coverage_tree_soundness` ↔ Collatz trajectory gap. The current `coverage_tree_soundness` (CoverageTree.lean:281) proves tree descent succeeds:

```lean
theorem coverage_tree_soundness (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    � l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l
```

Its docstring explicitly defers `ReachesOne x`: *"this theorem intentionally does not conclude `ReachesOne x`; that would require a proof connecting tree descent to the Collatz trajectory."*

PR #31 (merged 2026-08-17T22:11:12Z at `08319d5`) closed the 5 Dynamics/Equivalence/Certificate admissions in 02c/03c, landing in master:

1. `Basic.lean::acceleratedStep_odd_of_odd` (relocated from Certificate.lean)
2. `Dynamics.lean::standardStep_positive`
3. `Dynamics.lean::acceleratedStep_positive_of_odd`
4. `Dynamics.lean::acceleratedStep_equiv_standardStep`
5. `Equivalence.lean::acceleratedTrajectory_reaches_one_implies_standard`

These 5 lemmas establish the bridge between `acceleratedStep` (odd-only) and `standardStep` (Collatz map), and show that `accelerated_orbit` reaching 1 implies `standardTrajectory` reaching 1. **They do NOT directly prove `ReachesOne x` for arbitrary `x`** — they establish properties that are *prerequisites* to that proof.

## Claim

**Claim level target:** formally established.

Add a new companion theorem in `CoverageTree.lean`:

```lean
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descend t x = some l ∧
         ReachesOne x
```

No new `sorry` / `admit` / `axiom`. The existing `coverage_tree_soundness` is left **untouched** (preserves the formally established result + Codex-reviewed docstring that explicitly defers `ReachesOne`).

`coverage_tree_soundness_orbit` (CoverageTree.lean:344, currently `sorry`) is **OUT OF SCOPE** — separate workstream per MEMORY.md.

## Proof strategy (DRAFT — needs Codex review)

The key gap: `descend t x` uses `x % m` for residue lookup, while `accelerated_orbit x k` uses `acceleratedStep` for iteration. These are different operations. Bridging them requires one of:

### Option A — Tree-modulus bridge
Show that the tree's moduli are chosen so that `x % m` at level `k` equals `accelerated_orbit x k % m` for some specific `k`. This requires the tree to encode the Collatz map's residue structure at each level.

**Lemma needed (new):** `tree_residue_alignment : ∀ (t : CoverageTree), ValidTree t → IsComplete t → ∀ x (i : Nat) (child : CoverageNode), (i, child) ∈ tree.children → ∃ k, accelerated_orbit x k % m = i`

This is essentially the orbit-alignment condition that `coverage_tree_soundness_orbit` already requires (via `OrbitAlignedTree`). So Option A is closely related to closing `coverage_tree_soundness_orbit`'s sorry — but that sorry is out of scope.

### Option B — Use `coverage_tree_soundness_orbit` as a stepping stone
Prove `coverage_tree_soundness_full` by:
1. Apply `coverage_tree_soundness` to get `descend t x = some l`
2. Show `descendOrbit t x 0 = descend t x` (descent functions coincide for `k=0`)
3. Conclude `ReachesOne x` from `SatOrbit t x l`

This requires closing part of `coverage_tree_soundness_orbit`'s sorry (specifically the `SatOrbit` witness construction), which is out of scope.

### Option C — Direct `ReachesOne x` witness
Prove `ReachesOne x` independently using only the 5 closed lemmas + tree structure:

```lean
-- After coverage_tree_soundness gives us descend t x = some l and verified t l:
have hReaches : ReachesOne x := by
  -- The leaf's leafProperty gives us an interval [lo, hi] modulo the leaf's period
  -- combined with ValidTree ∧ IsComplete, this means the tree correctly encodes
  -- the Collatz trajectory reaching 1 within the leaf's interval.
  ...
```

This is the cleanest if doable, but requires proving the Collatz theorem essentially — which is the whole project. Not feasible without additional infrastructure.

### Preliminary assessment
Option C is infeasible without additional lemmas (essentially requires the Collatz theorem). Option B requires closing `coverage_tree_soundness_orbit` (out of scope). Option A is the most direct but introduces a new lemma that overlaps with `OrbitAlignedTree`.

**Open question for Codex review:** Which of these options (or which variant) is the intended proof strategy for 07c-2? The 5 closed lemmas provide prerequisites, but the actual bridge from `descend` to `ReachesOne x` requires additional structure that isn't in the closed lemmas.

## Lemma inventory (5 closed, from PR #31)

All available in master as of `08319d5`:

| # | Location | Statement (informal) | Used by Option |
|---|---|---|---|
| 1 | `Basic.lean` | `Odd (acceleratedStep n)` when `Odd n` | A, B |
| 2 | `Dynamics.lean` | `standardStep n > 0` for all `n` | A, B |
| 3 | `Dynamics.lean` | `acceleratedStep n > 0` when `Odd n` | A, B |
| 4 | `Dynamics.lean` | `acceleratedStep n` equiv. `standardStep n` (under odd condition) | A, B |
| 5 | `Equivalence.lean` | `accelerated_orbit` reaches 1 → `standardTrajectory` reaches 1 | A, B |

None of these directly prove `ReachesOne x` — they establish prerequisites. The actual "x reaches 1" claim requires the Collatz theorem, which is the project's open problem.

## Implementation outline (tentative)

1. **Spec-doc-stage Codex review** (THIS DOC) — validate proof strategy before implementation.
2. On Codex approval: implement `coverage_tree_soundness_full` on branch `story-07c-2-promotion` (already created from master `08319d5`).
3. Push to PR.
4. CI validates the Lean build (sole Lean gate per project BDD discipline — no local `lake`).
5. Codex review of the actual code (Phase B).
6. Merge on CI green + Codex sign-off.

Per-file discipline: `CoverageTree.lean` only.

## Out of scope (explicit)

- `coverage_tree_soundness_orbit` sorry at CoverageTree.lean:344 — separate workstream.
- New `sorry` / `admit` / `axiom` — forbidden by 07c-2 promotion criteria.
- `coverage_tree_soundness` modification — preserved untouched.
- The actual Collatz theorem (accelerated_orbit reaches 1 for all `x > 0`) — this is M4's deeper goal; 07c-2 is the tree-soundness bridge only.

## Risks

- **R1 (HIGH):** The proof strategy (A/B/C above) may not work without additional infrastructure (orbit alignment, Collatz theorem fragment, etc.). Spec-stage Codex review is meant to catch this.
- **R2 (MEDIUM):** New lemmas needed beyond the 5 closed ones — these would require their own spec/Codex review cycle, extending the timeline.
- **R3 (LOW):** v4.33.0 Mathlib API drift could affect new lemmas (we just debugged 4 such issues on PR #31). Mitigation: CI is the validation gate; iterate on failure.

## Codex review handoff template

```
## Story 07c-2 — coverage_tree_soundness_full promotion

**Claim:** Add companion theorem `coverage_tree_soundness_full`
strengthening `coverage_tree_soundness` to also conclude `ReachesOne x`,
using only the 5 closed lemmas from PR #31. No new sorry/admit/axiom.

**Files:** CoverageTree.lean (companion theorem only);
            docs/story-07c-2-promotion.md (this doc).
**Base:** master at 08319d5 (PR #31 merged 2026-08-17T22:11:12Z).

**Specific review questions:**
1. Which of Options A/B/C is the intended proof strategy? Or is there
   a different strategy we haven't enumerated?
2. Does the spec correctly identify the 5 closed lemmas as
   prerequisites (not direct proofs) for ReachesOne x?
3. Are there additional lemmas that should be closed in a prerequisite
   PR (e.g., orbit alignment) before this promotion?
4. Is the out-of-scope boundary for coverage_tree_soundness_orbit
   correct (separate workstream)?

**Evidence the reviewer will need:**
- CoverageTree.lean: full file (especially lines 270-360)
- PR #31 commits: ba12572, b237d44, 7516f32, 06a2388 (the 4 fixups
  that bridged v4.33.0 API drift)
- The 5 closed lemmas: Basic.lean::acceleratedStep_odd_of_odd,
  Dynamics.lean::{standardStep_positive, acceleratedStep_positive_of_odd,
  acceleratedStep_equiv_standardStep},
  Equivalence.lean::acceleratedTrajectory_reaches_one_implies_standard

**Lean validation gate:** GitHub Lean CI on the PR. No local lake.
**Per-stop rule:** standard pause at 2nd failure on same logical edit.
```

## Implementation log

(populated as commits land on `story-07c-2-promotion`)

- _no commits yet_ — awaiting Codex spec-stage approval.

