/-
Q5 v2b.4 — `BoundedInputCertificateTree`: thin per-tree wrapper
over `RoutingPartitionCertificateData`.

Story Q5 / Stage 2 of Option B staged implementation of Option C
(per-tree verifier with per-leaf certificate projection).

## Stage 2 scope

This module is the **v2b.4 thin wrapper** per
`docs/story-q5-pr4-v2b-proof-decomposition.md` § 6 + the design doc
at `.openclaw/followups/story-q5-option-c-spec.md`. It introduces:

1. `BoundedInputCertificateTree` — a single-field structure wrapping
   the kernel-clean `RoutingPartitionCertificateData` (PR #74). The
   "bounded-input" nature comes from `certData.wire.N` (the canonical
   input bound).
2. `checkBoundedCertificateTree` — a one-line delegation to
   `checkRoutingPartitionCertificate` (PR #74, kernel-clean).

## Why this design

Per GPT-5.6 Terra reviewer round 3 (Q1–Q4, subagent `9464f91e-...`):

- **Q1 (single-field wrapper):** `certData : RoutingPartitionCertificateData`.
  No `perLeafData`, no `checkPerLeaf` — the verifier recomputes
  acceptance (matches routing-partition's recomputation pattern; no
  stored check proofs).
- **Q2 (`Bool` return):** `checkBoundedCertificateTree : Bool` —
  delegates to `checkRoutingPartitionCertificate : Bool`.
- **Q4 (existing wire):** Use existing `RoutingPartitionCertificateWire`.
  No new wire types. The thin wrapper means no wire-format changes.

## Kernel-clean upstream

- `RoutingPartitionCertificateData` — `BoundedInputCertificateData.lean:281`
  (kernel-clean, PR #74).
- `checkRoutingPartitionCertificate` — `BoundedInputCertificateData.lean:362`
  (kernel-clean, PR #74).
- `RoutingPartitionCertificate_sound` — `Q5RoutingPartition.lean`
  (kernel-clean, PR #74 — directly inherited by Stage 3 v2b.5).

## Trust boundary

- **No unproven declarations introduced.**
- **Delegation is kernel-clean by construction** — delegates to
  existing kernel-clean code; the new code is a thin type-level
  adapter only.
- Per `formal-math-codex-escalate`: this is a bounded one-piece Stage 2
  implementation. Expected outcome: kernel-clean on first push.
- Per `collatz-pr-review-gate`: a GPT-5.6 Terra reviewer round will
  verify the design + delegation before Stage 3 proceeds.

## Tracking

- PR #84 (Stage 1 spec merge — closed): https://github.com/johrenberger/collatz-research/pull/84
- PR #74 (RoutingPartitionCertificate_sound, kernel-clean upstream)
- Issue #82 (Lemmas 5+6 follow-up)
- Design doc: `.openclaw/followups/story-q5-option-c-spec.md`
- Disposition doc: `.openclaw/followups/story-2-arch-disposition.md`
-/

import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.Q5RoutingPartition
import CollatzResearch.Q5Stage4Subproofs

namespace CollatzResearch

/-- Per-tree wrapper that exposes the kernel-clean
    `RoutingPartitionCertificateData` (PR #74) in the bounded-input
    context. The "bounded-input" nature comes from
    `certData.wire.N` (the canonical input bound).

    The verifier `checkBoundedCertificateTree` delegates to
    `checkRoutingPartitionCertificate` (no duplicate verifier logic,
    no new surface area).

    **Why single-field (per reviewer round 3 Q1):** No `checkPerLeaf`
    field — the verifier recomputes acceptance from the wire data +
    structural invariants, matching the routing-partition
    recomputation pattern. Storing `checkPerLeaf` would make the
    verifier a `decide` over already-supplied proofs (not real
    validation), which is not the design intent.

    See `.openclaw/followups/story-q5-option-c-spec.md` §
    "Type signatures" for the full design rationale. -/
structure BoundedInputCertificateTree (t : CoverageTree) where
  certData : RoutingPartitionCertificateData

/-- Per-tree verifier. Delegates to `checkRoutingPartitionCertificate`
    (PR #74, kernel-clean) — no duplicate logic, no new surface area.

    Returns `Bool` matching the routing-partition signature (per
    reviewer round 3 Q2). Per-leaf diagnostics are available
    separately via `checkRoutingPartitionCertificate_accepts_slot`
    (PR #74) if needed; not exposed here. -/
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool :=
  checkRoutingPartitionCertificate t tree.certData

/-- **Lemma 5 (v2b.5 — per-tree reachability, kernel-clean by delegation).**
    If `checkBoundedCertificateTree t tree = true` and every entry in
    `tree.certData.wire.claimRegistry` is known to reach 1, then every
    canonical input `x ∈ {1, …, N}` (where `N = tree.certData.wire.N`)
    reaches 1.

    The proof directly delegates to `RoutingPartitionCertificate_sound`
    (PR #74, kernel-clean in main). No novel soundness work — the
    thin-wrapper structure means the per-tree reachability is exactly
    the routing-partition reachability.

    Per reviewer round 4 F confirmation: this theorem is a one-line
    exact delegation.

    See `.openclaw/followouts/story-q5-option-c-spec.md` §
    "checkBoundedCertificateTree_sound" for the full design rationale. -/
theorem checkBoundedCertificateTree_sound
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y) :
    ∀ (x : Nat), 0 < x → x ≤ tree.certData.wire.N → ReachesOne x := by
  exact RoutingPartitionCertificate_sound t tree.certData hcheck hClaimReachesOne

/-- **Stage 4 v2b.6 — per-leaf `BoundedInputOrbitCertificate` projection.**

    The def is `noncomputable` because the construction uses
    `Classical.choose` to extract a witness from the `hRegistry`
    existential. The certificate itself is a kernel-clean `Type`
    (not a `Prop`); the only non-computational step is the
    existential extraction, which is unavoidable when the input
    signature supplies a per-leaf registry witness as a `Prop`.

    Given the per-tree check acceptance, the per-registry
    reachability assumption, and a per-leaf registry witness
    (`hRegistry`), construct the constructive per-leaf certificate
    `BoundedInputOrbitCertificate t l tree.certData.wire.N`.

    This is the centerpiece of META § 3.2 (constructive per-leaf
    availability): the per-tree `checkBoundedCertificateTree_sound`
    (v2b.5) certifies `ReachesOne x` for any `x ∈ {1, …, N}`; this
    theorem refines that to the per-leaf certificate
    `BoundedInputOrbitCertificate`, which carries the witness `k`
    that the orbit hits the claim.

    **Signature (reviewer-mandated, do NOT change):** the
    `hRegistry` hypothesis parameterizes the theorem by the
    per-leaf availability bridge supplied by the caller (PR #86
    round 4 P0/P1 reviewer-mandated signature).

    **Proof strategy (research-only sub-proofs, kernel-clean):**

    1. **`claim_reaches_one`** — direct: the claim is
       `entry_canon.claim` extracted from `hRegistry`; reachability
       follows from `hClaimReachesOne entry_canon hmem_canon`.

    2. **`orbit_hits_claim`** — extracts the per-slot Boolean
       check via `checkRoutingPartitionCertificate_accepts_slot`,
       decomposes via `checkRoutingPartitionWitness_accepts`,
       bridges the registry entry to `entry_canon` via
       Sub-proof A (`registry_unique_of_pairwise_irrefl`), and
       uses Sub-proof B (`trajectory_anchor_orbit_step`) for
       the trajectory ↔ `accelerated_orbit` indexing.

    **Sub-proofs used (from `Q5Stage4Subproofs`):**
    - A: `registry_unique_of_pairwise_irrefl` — per-leaf
      registry uniqueness.
    - B: `trajectory_anchor_orbit_step` — trajectory ↔ orbit
      indexing.
    - Helpers: `sameCoverageLeaf_eq` (PR #88 bridge),
      `sameCoverageLeaf_congr_eq` (Prop → Bool lifting),
      `bool_neq_false_true` (Booleans are mutually exclusive).

    **Kernel-clean:** no `sorry` / `admit` / `axiom`. The proof
    is constructive — every step is decidable, no `Classical`
    choice is used in the proof steps (the registry uniqueness
    is structural, not choice-based). -/
noncomputable def routing_partition_leaf_certificate
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N := by
  -- Extract canonical registry entry for leaf `l` (reviewer's hRegistry).
  -- Use `Classical.choose` rather than `obtain` because the goal is a
  -- `Type` (`BoundedInputOrbitCertificate ...`) and `Exists.casesOn`
  -- can only eliminate into `Prop`. This is the sole non-computational
  -- step in the proof; the rest is constructive.
  let hex := hRegistry l hl hver
  let entry_canon := hex.choose
  have hmem_canon : entry_canon ∈ tree.certData.wire.claimRegistry :=
    hex.choose_spec.1
  have leafEq : entry_canon.leaf = l := hex.choose_spec.2
  -- Lift Prop equality (entry.leaf = l) to Boolean (sameCoverageLeaf = true).
  have hSameLC : sameCoverageLeaf entry_canon.leaf l = true :=
    sameCoverageLeaf_congr_eq leafEq
  -- The Pairwise hypothesis from the data invariant (kernel-clean
  -- in main, PR #74).
  have hPair : tree.certData.wire.claimRegistry.Pairwise
      (fun a b => sameCoverageLeaf a.leaf b.leaf = false) :=
    tree.certData.registry_unique
  -- Build the per-leaf certificate. Field order in the structure
  -- (Q5Integration.lean:152): `claim`, `orbit_hits_claim`,
  -- `claim_reaches_one`. Use named placeholders to avoid relying on
  -- the position of `..` expansion.
  refine { claim := entry_canon.claim,
           orbit_hits_claim := ?_,
           claim_reaches_one := ?_ }
  · -- orbit_hits_claim.
    intros x hx hN hdesc
    -- The Fin-indexed slot for input `x`: i = ⟨x - 1, x - 1 < N ⟩.
    let i : Fin tree.certData.wire.N := ⟨x - 1, by omega⟩
    -- Prove `i.val + 1 = x` immediately (needed throughout the proof to
    -- convert `↑i + 1` to `x` in various hypotheses). `rfl` unfolds the
    -- `let` binding; `omega` closes the arithmetic.
    have hi : i.val + 1 = x := by
      have hival : i.val = x - 1 := rfl
      rw [hival]; omega
    -- The witness at slot `i` (with canonical input i.val + 1 = x).
    let w := (tree.certData.routingWitness i).val
    -- Per-slot check passes (by slot-extraction of the global check).
    have hslot := checkRoutingPartitionCertificate_accepts_slot
      t tree.certData hcheck i
    -- Decompose the Boolean check into its constituents.
    rcases checkRoutingPartitionWitness_accepts t (i.val + 1)
        tree.certData.wire.claimRegistry w hslot with
      ⟨claim', hfind, hd, rest, htraj, hhead, hroutes, hterminal, hfold⟩
    -- Extract the registry entry backing the `findRoutingLeafClaim` lookup.
    rcases findRoutingLeafClaim_some tree.certData.wire.claimRegistry
        w.leaf claim' hfind with
      ⟨entry', hentry', hclaim'_eq, hSameW'⟩
    -- Bridge `l = w.leaf` (Prop) via the orbit-aware routing invariants:
    -- `hroutes : routesToRoutingLeaf t x w.leaf = true` and
    -- `hdesc : descendOrbit t x 0 = some l`, where by definition
    -- `routesToRoutingLeaf t x w.leaf = sameCoverageLeaf (descendOrbit t x 0) w.leaf`.
    have hSameLW : sameCoverageLeaf l w.leaf = true := by
      unfold routesToRoutingLeaf at hroutes
      -- `hroutes` references `descendOrbit t (↑i + 1) 0`, but `hdesc`
      -- is `descendOrbit t x 0 = some l`. Use `hi : ↑i + 1 = x` to convert.
      rw [hi] at hroutes
      rw [hdesc] at hroutes
      exact hroutes
    have hLeafLW : l = w.leaf := sameCoverageLeaf_eq hSameLW
    -- Prop transitivity: entry_canon.leaf = w.leaf (via `leafEq`).
    have hLeafECW : entry_canon.leaf = w.leaf := leafEq.trans hLeafLW
    -- Boolean→Prop: entry'.leaf = w.leaf (via PR #88 bridge).
    have hLeafEW : entry'.leaf = w.leaf := sameCoverageLeaf_eq hSameW'
    -- Sub-proof A: entry_canon and entry' both in registry, with
    -- their leaves both propositionally equal to w.leaf, so they
    -- are STRUCTURALLY EQUAL.
    have hEq : entry_canon = entry' := by
      apply registry_unique_of_pairwise_irrefl hPair
      · exact hmem_canon
      · exact hentry'
      · have hEC_E' : entry_canon.leaf = entry'.leaf :=
          hLeafECW.trans hLeafEW.symm
        exact sameCoverageLeaf_congr_eq hEC_E'
    -- The witness-extracted claim is the same as entry_canon.claim.
    -- Chain: rewrite `entry_canon` to `entry'` via `hEq`, then
    -- use `hclaim'_eq.symm : claim' = entry'.claim`.
    have hClaim' : claim' = entry_canon.claim := by
      rw [hEq]
      exact hclaim'_eq.symm
    -- Build a `CertWitness (i.val + 1)` from the routing witness.
    let checked : CertWitness (i.val + 1) :=
      { l := w.leaf, trajectory := w.trajectory }
    -- `anchorOk`: trajectory is `hd :: rest` (non-empty) with `hd = i.val + 1`.
    have hAnchor : anchorOk (i.val + 1) checked = true := by
      simp [anchorOk, checked, htraj, hhead]
    -- The transition fold extracted to per-index form.
    have hTrans : ∀ j, j + 1 < checked.trajectory.length →
        checked.trajectory[j + 1]! = acceleratedStep checked.trajectory[j]! := by
      intro j hj
      dsimp [checked] at hj ⊢
      rw [htraj] at hj ⊢
      exact routing_transition_fold_step (hd :: rest) hfold j hj
    -- The terminal-claim position: `checked.trajectory[length - 1]!`.
    have hk : checked.trajectory.length - 1 < checked.trajectory.length := by
      simp [checked, htraj]
    -- Terminal claim: `claim'.Holds (trajectory[length - 1]!)`.
    -- Derived from the Boolean `hterminal` via `of_decide_eq_true`.
    have hne : hd :: rest ≠ [] := List.cons_ne_nil hd rest
    have hLast : claim'.Holds
        (checked.trajectory[checked.trajectory.length - 1]!) := by
      -- Unfold `checked.trajectory` to `w.trajectory` (definitional),
      -- then apply `htraj` to get `hd :: rest`. This lets the subsequent
      -- rewrites (`getElem!_pos`, `List.getLast_eq_getElem`) match.
      change claim'.Holds (w.trajectory[w.trajectory.length - 1]!)
      rw [htraj]
      have hidx : (hd :: rest).length - 1 < (hd :: rest).length := by
        rw [List.length_cons]; omega
      rw [getElem!_pos (hd :: rest) ((hd :: rest).length - 1) hidx]
      rw [← List.getLast_eq_getElem hne]
      have hterm' : decide (claim'.Holds ((hd :: rest).getLast hne)) = true := by
        rw [List.getLast?_eq_some_getLast hne] at hterminal
        exact hterminal
      exact of_decide_eq_true hterm'
    -- Sub-proof B: trajectory[length-1]! = accelerated_orbit (i.val+1) (length-1).
    have hOrbit : checked.trajectory[checked.trajectory.length - 1]! =
        accelerated_orbit (i.val + 1) (checked.trajectory.length - 1) :=
      trajectory_anchor_orbit_step (i.val + 1) checked
        (checked.trajectory.length - 1) hk hAnchor hTrans
    -- Compose: claim'.Holds (accelerated_orbit (i.val + 1) (length - 1)).
    have hClaimHolds : claim'.Holds
        (accelerated_orbit (i.val + 1) (checked.trajectory.length - 1)) := by
      rw [← hOrbit]
      exact hLast
    -- Convert `claim'` to `entry_canon.claim` via `hClaim'`.
    have hFinal : entry_canon.claim.Holds
        (accelerated_orbit (i.val + 1) (checked.trajectory.length - 1)) := by
      rw [← hClaim']
      exact hClaimHolds
    -- Convert (i.val + 1) to x: since i = ⟨x - 1, _⟩, i.val = x - 1, and
    -- 0 < x implies 1 ≤ x implies (x - 1) + 1 = x. First prove `i.val = x - 1`
    -- by `rfl` (which unfolds the `let` binding and `Fin.val` projection),
    -- then rewrite and let `omega` close the arithmetic.
    have hival : i.val = x - 1 := rfl
    have hi : i.val + 1 = x := by
      rw [hival]
      omega
    -- Witness the existence of k: k = length - 1. Use `Eq.mp` (`▸`)
    -- to substitute `x` for `i.val + 1` in `hFinal`'s `accelerated_orbit`
    -- argument, then close.
    refine ⟨checked.trajectory.length - 1, ?_⟩
    exact hi ▸ hFinal
  · -- claim_reaches_one: directly from hClaimReachesOne.
    intros y hy
    exact hClaimReachesOne entry_canon hmem_canon y hy

end CollatzResearch
