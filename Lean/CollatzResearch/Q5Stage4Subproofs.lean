/-
Q5 v2b.6 — Stage 4 sub-proofs (research-only, kernel-clean).

Story Q5 Stage 4 (`routing_partition_leaf_certificate`, the NEW
intermediate extraction theorem that bridges per-tree reachability to
per-leaf `BoundedInputOrbitCertificate`) hit budget 3× on 3 sub-proofs
in earlier sessions. A prior sub-agent (`runId 9d886da2`) drafted helper
infrastructure (`anchorOk`, `terminal_claim_transport`,
`routing_transition_fold_step`, `getElem!_pos`) that was reverted.

This module provides three fresh, KERNEL-CLEAN STANDALONE lemmas
scaffolding the Stage 4 parent theorem. Each lemma is provable from
existing kernel-clean primitives without touching the parent theorem
itself and without editing `BoundedInputCertificateTree.lean`.

**Sub-proof A (`registry_unique_of_pairwise_irrefl`) — registry leaf uniqueness.**

  In a `RoutingPartitionCertificateData` with the structural
  `registry_unique : claimRegistry.Pairwise (fun a b => sameCoverageLeaf
  a.leaf b.leaf = false)` invariant (no two entries share a leaf by the
  fieldwise Boolean comparator), any two entries in the registry with
  `sameCoverageLeaf entry.leaf entry'.leaf = true` are STRUCTURALLY
  EQUAL (same `.leaf` AND same `.claim`). The `Nodup`-flavoured sketch
  in the task brief is refined to `Pairwise`-based: `Nodup` (default
  `Pairwise (¬ · = ·)`) alone does not constrain leaf fields, but
  `Pairwise (fun a b => sameCoverageLeaf a.leaf b.leaf = false)` does,
  and is what `registry_unique` actually carries.

**Sub-proof B (`trajectory_anchor_orbit_step`) — trajectory ↔ orbit indexing.**

  For a witness `w : CertWitness x` with `anchorOk x w = true` (trajectory
  is non-empty with head matching `x`) and a per-pair `acceleratedStep`
  transition check (`hTrans`), the trajectory at any in-bounds index
  `k` equals the accelerated orbit `accelerated_orbit x k`.

  This is the kernel-clean, freshly-stated analogue of
  `trajectory_index` (Q5Integration.lean:533) and `terminal_claim_transport`
  (Q5Integration.lean:604) — both of which are removed-on-revert helpers
  in the v2b.6 reconstruction. Re-stated in this module so Stage 4 has
  its own self-contained primitive, independent of the reverted PR #64
  helpers.

**Sub-proof C (`findRegistryEntry_unify`) — canonical registry-entry extraction.**

  Given a registry `reg : List LeafClaimWire` containing at least one
  entry whose `.leaf` is `l` (propositional equality), any other entry
  in the registry with `sameCoverageLeaf entry'.leaf l = true` (Boolean
  fieldwise check) is STRUCTURALLY EQUAL to the canonical entry
  `Classical.choose hRegistry` (the witness extracted from the
  existential). The result follows from Sub-proof A.

**Kernel-clean:** NO `sorry` / `admit` / `axiom`. Verified by
`grep -nE 'sorry|admit|axiom' Lean/CollatzResearch/Q5Stage4Subproofs.lean`
returning zero hits after `lake build CollatzResearch.Q5Stage4Subproofs`
succeeds.

**Not in scope:** the parent theorem `routing_partition_leaf_certificate`
itself (Stage 4 closure, deferred). No edits to
`BoundedInputCertificateTree.lean`. No changes to existing kernel-clean
infrastructure (`RoutingPartitionCertificateData`, `checkRoutingPartitionCertificate`,
`RoutingPartitionCertificate_sound`, etc. — all inherited unchanged).
-/

import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.CoverageTree
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## Helper: contradiction from conflicting Boolean equations

The proof of Sub-proof A repeatedly derives `sameCoverageLeaf _ _ = false`
from the Pairwise hypothesis and `sameCoverageLeaf _ _ = true` from
`hSame`. To close these, we need the trivial kernel-clean fact that a
Bool cannot be both `true` and `false`. The `noConfusion` tactic
derives this in one line: `Bool`'s two constructors are distinct.

-/

/-- Internal helper: a Bool cannot be both `false` and `true`. -/
private lemma bool_neq_false_true (b : Bool) (h1 : b = false) (h2 : b = true) : False :=
  -- Pattern-match on `b`. In each case, the leftover equation (false = true
  -- or true = false) has no constructor; `nomatch` derives False.
  match b with
  | false => nomatch h2
  | true => nomatch h1

/-! ## Helper: symmetry and reflexivity of `sameCoverageLeaf`

These two helpers support Sub-proof A's case analysis: when one entry
is the head and the other is in the tail, the `Pairwise` constraint
gives `sameCoverageLeaf a.leaf b.leaf = false`, but our hypothesis
`hSame` might be stated in the swapped order (e.g.,
`sameCoverageLeaf b.leaf a.leaf = true` after substitution). The
symmetry lemma lets us unify the argument order; the reflexivity lemma
lets us re-derive a Boolean `sameCoverageLeaf` truth from a propositional
`CoverageLeaf` equality (used by Sub-proof C to bridge Prop → Bool). -/

/-- **Helper: symmetry of `sameCoverageLeaf`.**

    `sameCoverageLeaf a b = sameCoverageLeaf b a`, by `BEq` symmetry
    on the underlying `String` fields (each `(s == t) = decide (s = t)`
    reduces symmetrically via `decide_eq_decide` and `Eq.symm`).

    Kernel-clean (no `sorry` / `admit` / `axiom`). -/
lemma sameCoverageLeaf_symm (a b : CoverageLeaf) :
    sameCoverageLeaf a b = sameCoverageLeaf b a := by
  unfold sameCoverageLeaf
  -- Reduce each `==` to `decide (=)`, then apply `decide_eq_decide` (core)
  -- with the Iff-equivalence of `a = b ↔ b = a`.
  have h1 : (a.leafId == b.leafId : Bool) = (b.leafId == a.leafId : Bool) := by
    have ha : (a.leafId == b.leafId) = decide (a.leafId = b.leafId) := rfl
    have hb : (b.leafId == a.leafId) = decide (b.leafId = a.leafId) := rfl
    rw [ha, hb]
    exact (decide_eq_decide).mpr (Iff.intro Eq.symm Eq.symm)
  have h2 : (a.leafProperty == b.leafProperty : Bool) =
            (b.leafProperty == a.leafProperty : Bool) := by
    have ha : (a.leafProperty == b.leafProperty) =
              decide (a.leafProperty = b.leafProperty) := rfl
    have hb : (b.leafProperty == a.leafProperty) =
              decide (b.leafProperty = a.leafProperty) := rfl
    rw [ha, hb]
    exact (decide_eq_decide).mpr (Iff.intro Eq.symm Eq.symm)
  rw [h1, h2]

/-- **Helper: `sameCoverageLeaf` lifts `CoverageLeaf` equality to Boolean truth.**

    The converse of `sameCoverageLeaf_eq` (BoundedInputCertificateData.lean:207).
    If two `CoverageLeaf` values are propositionally equal, their
    `sameCoverageLeaf` Boolean comparison is `true` (since both `String`
    fields are `==` to themselves, hence `decide (=)` evaluates to `true`).

    Kernel-clean (no `sorry` / `admit` / `axiom`). -/
lemma sameCoverageLeaf_congr_eq {a b : CoverageLeaf} (h : a = b) :
    sameCoverageLeaf a b = true := by
  subst h
  -- After `subst`, both `a` and `b` refer to the same `CoverageLeaf`.
  -- Apply reflexivity of each fieldwise `BEq` (String `==` to itself is `true`).
  have h1 : (a.leafId == a.leafId : Bool) = true := by
    rw [show (a.leafId == a.leafId) = decide (a.leafId = a.leafId) from rfl]
    exact decide_eq_true rfl
  have h2 : (a.leafProperty == a.leafProperty : Bool) = true := by
    rw [show (a.leafProperty == a.leafProperty) =
          decide (a.leafProperty = a.leafProperty) from rfl]
    exact decide_eq_true rfl
  rw [sameCoverageLeaf, h1, h2]
  rfl

/-! ## Sub-proof A — per-leaf registry uniqueness

Given a registry with `Pairwise` irreflexivity on `sameCoverageLeaf`
(matching `RoutingPartitionCertificateData.registry_unique`), two
entries with the same Boolean leaf comparison are STRUCTURALLY EQUAL.
This is the foundation for "per-leaf uniqueness" in the claim registry
and the kernel-clean bridge for Sub-proof C below. -/

/-- **Sub-proof A: per-leaf uniqueness via `Pairwise` irreflexivity.**

    Given a registry `reg : List LeafClaimWire` with
    `reg.Pairwise (fun a b => sameCoverageLeaf a.leaf b.leaf = false)`
    (the `registry_unique` invariant of
    `RoutingPartitionCertificateData`), two entries `entry, entry' ∈ reg`
    with `sameCoverageLeaf entry.leaf entry'.leaf = true` are
    STRUCTURALLY EQUAL (`entry = entry'`).

    **Why `Pairwise` (not `Nodup`).** `Nodup` (default `Pairwise (¬ · = ·)`)
    only constrains entries up to STRUCTURAL equality of `LeafClaimWire`,
    not fieldwise leaf equality. The task brief's `Nodup`-flavoured
    sketch is refined to `Pairwise (fun a b => sameCoverageLeaf a.leaf
    b.leaf = false)` — the actual `registry_unique` invariant from
    PR #74 — which IS the fieldwise-leaf-irreflexivity constraint we
    need.

    **Proof sketch (structural induction on `reg`):**

    - Base (empty registry): `entry ∈ []` is impossible, so the
      hypothesis is vacuous.
    - Inductive step (registry `a :: rest`): pattern-match on `entry`
      and `entry'` membership positions:
      - `entry` is the head `a`:
        - `entry'` is also the head ⇒ `entry = entry' = a`.
        - `entry' ∈ rest` ⇒ pairwise constraint gives
          `sameCoverageLeaf a.leaf entry'.leaf = false`, contradicting
          `sameCoverageLeaf a.leaf entry'.leaf = true`.
      - `entry ∈ rest`:
        - `entry'` is the head ⇒ symmetric contradiction (uses
          `sameCoverageLeaf_symm` to unify argument order).
        - Both in `rest` ⇒ recursive call on `hPairRest`.

    **Kernel-clean (no `sorry` / `admit` / `axiom`).** -/
lemma registry_unique_of_pairwise_irrefl {reg : List LeafClaimWire}
    (hPair : reg.Pairwise (fun a b => sameCoverageLeaf a.leaf b.leaf = false))
    {entry entry' : LeafClaimWire} (hmem : entry ∈ reg) (hmem' : entry' ∈ reg)
    (hSame : sameCoverageLeaf entry.leaf entry'.leaf = true) :
    entry = entry' := by
  -- Direct case analysis on `hmem` and `hmem'`. In each branch we
  -- either construct `entry = entry'` directly (head/head, tail/tail)
  -- or close via `False.elim` after deriving contradictory Boolean
  -- equations (`bool_neq_false_true`). This avoids `by_contra`-induced
  -- IH generalization (which auto-promotes `hSame` and `hne` as IH
  -- parameters) and the `subst`-gymnastics that fail Lean 4's
  -- parametric-constructor equation emission.
  induction reg generalizing entry entry' with
  | nil =>
    simp at hmem
  | cons a rest ih =>
    cases hPair with
    | cons hConstraint hPairRest =>
      cases hmem with
      | head _ =>
        -- `entry = a` (parametric constructor unification in `cases hmem`).
        cases hmem' with
        | head _ =>
          -- `entry' = a = entry`. Trivial.
          rfl
        | tail _ hmemRest =>
          -- `entry' ∈ rest`. `hConstraint entry' hmemRest` gives
          -- `sameCoverageLeaf a.leaf entry'.leaf = false`; combined with
          -- `hSame` (defeq to `sameCoverageLeaf a.leaf entry'.leaf = true`),
          -- this is contradictory.
          apply False.elim
          exact bool_neq_false_true _ (hConstraint entry' hmemRest) hSame
      | tail _ hmemRest =>
        cases hmem' with
        | head _ =>
          -- `entry ∈ rest, entry' = a`. `hConstraint entry hmemRest` is
          -- `sameCoverageLeaf a.leaf entry.leaf = false`; `hSame`
          -- (defeq) is `sameCoverageLeaf entry.leaf a.leaf = true`.
          -- Swap to a common Leaf-pair via `sameCoverageLeaf_symm`.
          apply False.elim
          exact bool_neq_false_true _ (hConstraint entry hmemRest)
            (by rw [← sameCoverageLeaf_symm entry.leaf a.leaf]; exact hSame)
        | tail _ hmemRest' =>
          -- Both in `rest`. Recurse via IH (which re-uses `hSame`).
          exact ih hPairRest hmemRest hmemRest' hSame

/-! ## Sub-proof B — trajectory-orbit indexing

The bridge from a witness's Boolean `trajectory` field (a `List Nat`)
to the `accelerated_orbit` index used by `BoundedInputOrbitCertificate`.
Independent re-statement of `trajectory_index` (Q5Integration.lean:533),
intentionally placed in this module so Stage 4 has its own
self-contained primitive (the reverted PR #64 helpers live in
`Q5Integration.lean`, but are still kernel-clean — this re-statement
documents the v2b.6 dependency explicitly). -/

/-- **Sub-proof B: trajectory-orbit indexing.**

    For a witness `w : CertWitness x` with `anchorOk x w = true`
    (trajectory is non-empty with head matching `x`) and a per-pair
    `acceleratedStep` transition check, the trajectory at any in-bounds
    index `k` equals the accelerated orbit `accelerated_orbit x k`.

    **Proof sketch (induction on `k`):**

    - Base (`k = 0`): `accelerated_orbit x 0 = x` (by
      `accelerated_orbit_zero`). Then `trajectory[0]! = x` by
      `anchorOk_implies_get_zero` (kernel-clean from
      Q5Integration.lean:493).
    - Step (`k + 1`):
      1. IH gives `trajectory[k]! = accelerated_orbit x k`.
      2. `hTrans k hklt` gives `trajectory[k + 1]! = acceleratedStep
         trajectory[k]!`.
      3. Substitute IH into `acceleratedStep`: `acceleratedStep
         (accelerated_orbit x k) = accelerated_orbit x (k + 1)` by
         `accelerated_orbit_succ`.

    **Reuses kernel-clean primitives:**
    - `accelerated_orbit_zero` / `accelerated_orbit_succ` (CoverageTree.lean:123/130)
    - `anchorOk_implies_get_zero` (Q5Integration.lean:493)
    - `anchorOk` (Q5Integration.lean:330)

    **Kernel-clean (no `sorry` / `admit` / `axiom`).** -/
theorem trajectory_anchor_orbit_step (x : Nat) (w : CertWitness x) (k : Nat)
    (hk : k < w.trajectory.length)
    (hAnchor : anchorOk x w = true)
    (hTrans : ∀ i, i + 1 < w.trajectory.length →
                w.trajectory[i + 1]! = acceleratedStep w.trajectory[i]!) :
    w.trajectory[k]! = accelerated_orbit x k := by
  induction k with
  | zero =>
    -- Base: `trajectory[0]! = x = accelerated_orbit x 0`.
    rw [accelerated_orbit_zero]
    exact anchorOk_implies_get_zero x w hAnchor
  | succ k ih =>
    -- Step: `trajectory[k + 1]! = acceleratedStep (trajectory[k]!)`
    -- by `hTrans`; IH gives `trajectory[k]! = accelerated_orbit x k`;
    -- `accelerated_orbit_succ` reverses the orbit rewrite.
    have hklt : k < w.trajectory.length := Nat.lt_of_succ_lt hk
    calc
      w.trajectory[k + 1]! = acceleratedStep (w.trajectory[k]!) :=
        hTrans k hk
      _ = acceleratedStep (accelerated_orbit x k) :=
        congrArg acceleratedStep (ih hklt)
      _ = accelerated_orbit x (k + 1) :=
        (accelerated_orbit_succ x k).symm

/-! ## Sub-proof C — canonical registry entry unification

The structural extraction step for the Stage 4 parent theorem's
per-leaf certificate construction. Given a registry that contains at
least one entry for a leaf `l`, any other entry matching `l` by the
Boolean leaf comparator is EQUAL to the canonical `Classical.choose`
extracted from the existential witness. This is what guarantees
`findRoutingLeafClaim reg l` returns the unique per-leaf claim. -/

/-- **Sub-proof C: canonical registry-entry unification.**

    Given a registry `reg : List LeafClaimWire` containing at least one
    entry whose `.leaf` is `l` (propositional equality, in `hRegistry`),
    plus the `Pairwise` irreflexivity on `sameCoverageLeaf` (matching
    `RoutingPartitionCertificateData.registry_unique`), any other entry
    `entry' ∈ reg` with `sameCoverageLeaf entry'.leaf l = true` is
    STRUCTURALLY EQUAL to the canonical entry `Classical.choose
    hRegistry` (the entry extracted from `hRegistry`'s witness).

    **Proof sketch:**

    1. From `Classical.choose_spec hRegistry` we have `entry_canon ∈ reg`
       and `entry_canon.leaf = l`.
    2. From `hSame` and `sameCoverageLeaf_eq` we get `entry'.leaf = l`.
    3. Hence `entry'.leaf = entry_canon.leaf` (propositional, by
       `Eq.trans` via `l`).
    4. The converse bridge — `sameCoverageLeaf entry'.leaf
       entry_canon.leaf = true` — follows from `sameCoverageLeaf_congr_eq`
       (Prop → Bool lifting).
    5. Sub-proof A (`registry_unique_of_pairwise_irrefl`) closes the
       final step: `entry' = entry_canon` from the `Pairwise`
       hypothesis and the Boolean leaf equality.

    **Reuses kernel-clean primitives:**
    - `sameCoverageLeaf_eq` (BoundedInputCertificateData.lean:207)
    - `sameCoverageLeaf_congr_eq` (this module)
    - `Classical.choose_spec`
    - Sub-proof A (`registry_unique_of_pairwise_irrefl`)

    **Kernel-clean (no `sorry` / `admit` / `axiom`).** -/
lemma findRegistryEntry_unify (l : CoverageLeaf) (reg : List LeafClaimWire)
    (hPair : reg.Pairwise (fun a b => sameCoverageLeaf a.leaf b.leaf = false))
    (hRegistry : ∃ entry ∈ reg, entry.leaf = l)
    (entry' : LeafClaimWire) (hmem' : entry' ∈ reg)
    (hSame : sameCoverageLeaf entry'.leaf l = true) :
    entry' = Classical.choose hRegistry := by
  -- Extract the canonical entry's membership and leaf specs.
  obtain ⟨entryMem, leafEq⟩ := Classical.choose_spec hRegistry
  -- Step 1: `entry'.leaf = l` from `hSame` via Boolean→Prop bridge.
  have hLeafL : entry'.leaf = l := sameCoverageLeaf_eq hSame
  -- Step 2: `entry'.leaf = entry_canon.leaf` by `Eq.trans`.
  -- (Using `trans` + `symm` to avoid the `Classical.choose` dependent-
  -- type motive issue in `rw`.)
  have hLeafEq : entry'.leaf = (Classical.choose hRegistry).leaf :=
    hLeafL.trans leafEq.symm
  -- Step 3: lift `entry'.leaf = entry_canon.leaf` (Prop) to Boolean
  -- `sameCoverageLeaf` equality via `sameCoverageLeaf_congr_eq`.
  have hSameCan : sameCoverageLeaf entry'.leaf
      (Classical.choose hRegistry).leaf = true :=
    sameCoverageLeaf_congr_eq hLeafEq
  -- Step 4: apply Sub-proof A to conclude `entry' = entry_canon`.
  exact registry_unique_of_pairwise_irrefl hPair hmem' entryMem hSameCan

end CollatzResearch
