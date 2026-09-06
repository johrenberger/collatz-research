/-
Q5 PR #4 v2b soundness helpers + per-leaf packaging theorem
(Story #2 — per-leaf packaging theorem).

This module re-attempts Lemmas 5 + 6 from
`docs/story-q5-pr4-v2b-proof-decomposition.md` that Codex review
`PRR_kwDOTuMD788AAAABL71GQA` (2026-09-02) removed from
`Q5Integration.lean` with the [P0] finding:

> Do not extend the budget for this path. Remove the admitted
> theorem/proof skeleton from the Lean module (retain the
> decomposition in the planning document if useful) and land only
> fully checked helper lemmas. The soundness theorem and
> constructive availability theorem must remain absent until proved.

The v2b.2 Codex P0 fix restructured Lemmas 3 + 4 to take the
per-pair `acceleratedStep` check directly as a hypothesis (bypassing
`transitionOk_implies_step` which had 2 `sorry`s for `List.length_zip`
and `List.get_zip`). Lemmas 1, 2, 3, 4 all land kernel-clean. This
module closes the missing bridge (`transitionOk_implies_step`) with
Mathlib v4.33.0's `List.length_zip` + `List.getElem_zip` (both
already used successfully in
`Q5RoutingPartition.routing_transition_fold_step`) and re-introduces
the v2b.4 soundness + v2b.5 per-leaf availability theorems
kernel-cleanly.

## Trust boundary (Q5 v5 spec § 3)

```
Python serialized evidence → (PR #63 parser)
                            → BoundedInputCertificateWire
                            → decodeBoundedInputCertificateData (PR #62)
                            → BoundedInputCertificateData
                            → checkBoundedCertificate (PR #62)
                            → Bool verifier (PR #4 soundness — v2b, THIS FILE)
                            → BoundedInputOrbitCertificate (Q5Integration.lean)
                            → coverage_tree_soundness_orbit_cert_bounded (Q5Integration.lean)
                            → ∀ x, 0 < x → x ≤ N → ReachesOne x
```

## Lessons applied (Q3 v4 + Q4 v3 + Q5 v2b.2 + META)

- **Q3 v4 + Q4 v3 (`: Type` sort):** `BoundedInputOrbitCertificate` is
  `: Type`-valued. The conclusion is `BoundedInputOrbitCertificate`,
  NOT `ReachesOne` directly. Lean 4 elaboration rejects `Type`-valued
  fields in `: Prop` structures.
- **Q4 v3 (Pattern 2.10 conditional companion theorem):**
  `checkBoundedCertificate_sound` takes `hv + hic + hver + hcr` as
  explicit hypotheses (no default, no `by sorry`) per PR #51 P1
  discipline. The conditional companion theorem stays hypothesis-bearing
  until the full per-leaf hypothesis dataset is supplied.
- **Q5 v2b.2 (P0 fix):** `transitionOk_implies_step` uses Mathlib v4.33.0
  `List.length_zip` + `List.getElem_zip` directly (no `sorry`). The
  `transitionOk` predicate's fold is unfolded; the per-pair check is
  extracted via `foldl_and_extract` (already kernel-checked in
  `Q5Integration.lean`).
- **META § 3.2 (per-leaf availability):**
  `per_leaf_available_bounded_of_check` takes the per-leaf `dataPerLeaf`
  + per-leaf `check = true` evidence as explicit inputs, mirroring
  Q4 v3's `hCert`. The bound `N` is taken from
  `(dataPerLeaf l hl hver).wire.N` (not a free parameter), which lines
  up with `checkBoundedCertificate_sound`'s return type and avoids the
  prior free-`N` parameter that would force a coercion through
  `BoundedInputOrbitCertificate`'s bound.
- **META § 3.3 (avoid universal acceptance):** the bounded companion
  theorem stays conditional on `hv + hic + hcr`. No `∀ t` universal
  claim.

## Deprecation note

The v2a hypothesis-eliminator form `per_leaf_available_bounded_of_hCert`
(Q5Integration.lean) remains in place as the existing surface;
`per_leaf_available_bounded_of_check` (this file) is the v2b
constructive replacement. No backward-compat alias is added (no
existing caller needs one).

Story Q5 / PR #4 v2b.4 + v2b.5 — `checkBoundedCertificate_sound`
(Lemma 5) + `per_leaf_available_bounded_of_check` (Lemma 6),
both kernel-checked. Closes the v2b Codex P0 finding by landing the
previously admitted theorems with closed proofs.
-/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## v2b.1 — transitionOk → per-pair step (Mathlib v4.33.0 bridge)

The v2b.2 Codex P0 fix refactored Lemmas 3 + 4 to take the per-pair
`acceleratedStep` check directly as a hypothesis (bypassing the
`transitionOk`-fold bridge that needed 2 `sorry`s). This module
closes that bridge anyway using Mathlib v4.33.0's
`List.length_zip` + `List.getElem_zip` + `List.getElem_tail` (all
already used successfully in
`Q5RoutingPartition.routing_transition_fold_step`).

The proof parallels `routing_transition_fold_step` exactly, with the
`CertWitness` trajectory in place of the routing witness trajectory. -/

/-- **transitionOk_implies_step.** If `transitionOk w = true`, then for
    any index `i` with `i + 1 < trajectory.length`,
    `(w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!)`.

    Mirrors `routing_transition_fold_step` in `Q5RoutingPartition.lean`
    (uses `foldl_and_extract` from `Q5Integration.lean` to lift the
    fold-`true` to per-element truth, then `List.length_zip` +
    `List.getElem_zip` + `List.getElem_tail` to project the indexed
    element out of the zipped pair list).

    Kernel-clean (no `sorry` / `admit` / `axiom`). -/
theorem transitionOk_implies_step (x : Nat) (w : CertWitness x)
    (hTrans : transitionOk w = true)
    (i : Nat) (hi : i + 1 < (w.trajectory).length) :
    (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) := by
  unfold transitionOk at hTrans
  -- Bound: `i < zip xs xs.tail.length` follows from `i + 1 < xs.length`
  -- and the `List.length_zip` / `List.length_tail` identities.
  have hzip : i < (List.zip (w.trajectory) (w.trajectory).tail).length := by
    simp only [List.length_zip, List.length_tail]
    have hlt : i < (w.trajectory).length := Nat.lt_of_succ_lt hi
    -- `min xs.length (xs.length - 1) = xs.length - 1` for `0 < xs.length`
    -- (and the min is in fact `xs.length - 1`, which is `≥ i` from `hi`).
    omega
  -- Lift the per-pair check from the fold to the indexed element.
  -- `hpair` has type `((...).snd == acceleratedStep (...).fst) = true`
  -- (Bool eq form). `simpa using hpair` discharges the Eq form
  -- `(...).snd = acceleratedStep (...).fst` by rewriting with `beq_iff_eq`.
  have hpair := foldl_and_extract (List.zip (w.trajectory) (w.trajectory).tail)
    (fun pair => pair.snd == acceleratedStep pair.fst) hTrans
    (List.zip (w.trajectory) (w.trajectory).tail)[i]
    (List.getElem_mem hzip)
  -- Project the zipped pair's snd/fst to the trajectory values via
  -- `List.getElem_zip`, then `List.getElem_tail` rewrites the tail
  -- index to the parent.
  have hpair' : (List.zip (w.trajectory) (w.trajectory).tail)[i].snd =
      acceleratedStep (List.zip (w.trajectory) (w.trajectory).tail)[i].fst := by
    simpa using hpair
  rw [List.getElem_zip] at hpair'
  rw [List.getElem_tail] at hpair'
  -- Rewrite to the original list's indexed access and conclude.
  simpa only [getElem!_pos (w.trajectory) (i + 1) hi,
    getElem!_pos (w.trajectory) i (Nat.lt_of_succ_lt hi)] using hpair'

/-- Per-witness per-pair `acceleratedStep` check (kernel-clean form of
    `transitionOk = true` plus the `i + 1 < length` premise).

    Convenience wrapper for the curry-friendly form used by
    `checkBoundedCertificate_sound`. -/
theorem transitionOk_implies_step_forall (x : Nat) (w : CertWitness x)
    (hTrans : transitionOk w = true) :
    ∀ i, i + 1 < (w.trajectory).length →
      (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) := by
  intro i hi
  exact transitionOk_implies_step x w hTrans i hi

/-! ## v2b.4 — Lemma 5: checkBoundedCertificate_sound (kernel-clean)

Main soundness theorem. Connects `checkBoundedCertificate t l d = true`
(plus explicit `hv + hic + hver + hcr` hypotheses) to
`BoundedInputOrbitCertificate t l d.wire.N`.

**No `sorry` / `admit` / `axiom` — fully kernel-checked.**

**Proof decomposition:**
1. `checkBoundedCertificate t l d = true` unfolds to the
   `List.foldl` over `List.finRange d.wire.N` with the per-witness
   `checkCertWitness` predicate.
2. `foldl_and_extract` (Lemma 1, Q5Integration.lean) lifts to
   `∀ i : Fin N, checkCertWitness (i.val + 1) claim t l (d.certWitness i) = true`.
3. Per `i : Fin N`: `checkCertWitness_decompose` (Lemma 2,
   Q5Integration.lean) gives the 5 conjuncts (anchor, leaf, routing,
   terminal claim, transition).
4. `transitionOk_implies_step_forall` (this file) lifts
   `transitionOk = true` to the per-pair form required by
   `terminal_claim_transport`.
5. `terminal_claim_transport` (Lemma 4, Q5Integration.lean) gives
   `claim.Holds (accelerated_orbit x (length - 1))` for
   `x = i.val + 1`.
6. Construct `BoundedInputOrbitCertificate t l N` with
   `claim = d.wire.claim`, `claim_reaches_one = hcr`, and
   `orbit_hits_claim` assembled from steps 2–5.

For the `orbit_hits_claim` part, the input `x : Nat` with
`0 < x ≤ N` maps to `i = ⟨x - 1, _⟩ : Fin N` (canonical-input
identity `i.val + 1 = x`); `descendOrbit t x 0 = some l` is the
external hypothesis supplied to the structure (per PR #51 P1
discipline; the witness's `routingOk` derives it internally but the
structure accepts the explicit hypothesis). -/

/-- **Lemma 5 (soundness assembly, kernel-clean).** Connects
    `checkBoundedCertificate t l d = true` (plus explicit
    `hv + hic + hver + hcr` hypotheses) to
    `BoundedInputOrbitCertificate t l d.wire.N`.

    Built from Lemmas 1, 2, 4 (already kernel-checked in
    `Q5Integration.lean`) + the new `transitionOk_implies_step` bridge
    (kernel-clean). NO `sorry` / `admit` / `axiom`.

    The `hv + hic + hver` hypotheses aren't used in the per-witness
    composition itself (the per-witness check uses only
    `routingOk + terminalClaimOk + transitionOk + anchorOk`); they're
    preserved as parameters for future composition with
    `coverage_tree_soundness_orbit_cert_bounded` (which uses
    `descend_orbit_complete`) and to keep the PR #51 P1 discipline
    (explicit hypothesis preservation throughout). -/
noncomputable def checkBoundedCertificate_sound
    (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData)
    (hv : ValidTree t)
    (hic : IsComplete t)
    (hver : verified t l)
    (hcr : ∀ y, d.wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificate t l d = true)
    : BoundedInputOrbitCertificate t l d.wire.N := by
  -- Step 1: Per-witness check extraction via `foldl_and_extract`.
  -- `checkBoundedCertificate` is a fold over `List.finRange d.wire.N`
  -- with predicate
  --   `(fun i => checkCertWitness (i.val + 1) d.wire.claim t l (d.certWitness i))`.
  have hExtracted (i : Fin d.wire.N) :
      checkCertWitness (i.val + 1) d.wire.claim t l (d.certWitness i) = true := by
    have hfoldTrue : (List.foldl (fun acc i =>
        let x : Nat := i.val + 1
        acc && checkCertWitness x d.wire.claim t l (d.certWitness i))
        true (List.finRange d.wire.N)) = true := by
      simpa [checkBoundedCertificate] using hcheck
    exact foldl_and_extract (List.finRange d.wire.N)
      (fun i => let x : Nat := i.val + 1
                checkCertWitness x d.wire.claim t l (d.certWitness i))
      hfoldTrue i (List.mem_finRange i)
  -- Step 2: Construct the certificate.
  refine { claim := d.wire.claim, claim_reaches_one := hcr, orbit_hits_claim := ?_ }
  intro x hx hN hdesc
  -- `i : Fin d.wire.N` with `i.val + 1 = x`. `x - 1 < d.wire.N` from
  -- `x ≤ N ∧ 0 < x`.
  have hxpos : x - 1 < d.wire.N := by omega
  let i : Fin d.wire.N := ⟨x - 1, hxpos⟩
  have hiVal : i.val + 1 = x := by simp [i, Nat.sub_add_cancel hx]
  -- OPTION B (structural rewrite per formal-math-codex-escalate):
  -- Bind the witness to a non-dependent `w : CertWitness (i.val + 1)` so
  -- the per-witness work uses `w.trajectory` directly. The existing
  -- kernel-checked `anchorOk_implies_get_zero` in Q5Integration.lean uses
  -- this exact pattern with non-dependent `w : CertWitness x`. Working
  -- directly with the dependent `(d.certWitness i).trajectory` tripped
  -- Lean's simplifier on the nil branch (4th CI failure); the non-dependent
  -- `w.trajectory` mirrors the proven `anchorOk_implies_get_zero` pattern.
  let w : CertWitness (i.val + 1) := d.certWitness i
  -- Per-witness check via `hExtracted` (canonical-input identity).
  -- `hExtracted i : checkCertWitness (i.val + 1) d.wire.claim t l (d.certWitness i) = true`;
  -- `w = d.certWitness i` definitionally, so no rewrite needed.
  have hwcheck : checkCertWitness (i.val + 1) d.wire.claim t l w = true :=
    hExtracted i
  -- Decompose the per-witness check (Lemma 2). Right-associative
  -- `A ∧ B ∧ C ∧ D ∧ E` is `A ∧ (B ∧ (C ∧ (D ∧ E)))`; destructure
  -- nested.
  have hwdecomp := (checkCertWitness_decompose (i.val + 1) d.wire.claim t l w).mp hwcheck
  have ⟨hAnchor, hrest1⟩ := hwdecomp
  have ⟨hLeaf, hrest2⟩ := hrest1
  have ⟨hRouting, hrest3⟩ := hrest2
  have ⟨hTerminal, hTransition⟩ := hrest3
  -- Trajectory is non-empty (from `anchorOk = true`). Mirror
  -- `anchorOk_implies_get_zero` exactly: `unfold anchorOk at hAnchor`,
  -- then `cases` on the (non-dependent) `w.trajectory`. The nil branch
  -- discharges via `simp [htr] at hAnchor` (the `match` reduces to
  -- `false`, contradicting `hAnchor : true`).
  have hne : 0 < w.trajectory.length := by
    unfold anchorOk at hAnchor
    cases htr : w.trajectory with
    | nil => simp [htr] at hAnchor
    | cons hd tl => simp
  -- Mathlib v4.33.0 `List.getLast_eq_getElem` takes `xs ≠ []` (Ne proof,
  -- not `0 < xs.length`); convert via `List.length_pos_iff_ne_nil`.
  have hne' : w.trajectory ≠ [] := List.length_pos_iff_ne_nil.mp hne
  -- `length - 1 < length` for the indexed access in `terminal_claim_transport`.
  have hidx : w.trajectory.length - 1 < w.trajectory.length := by omega
  -- Convert `terminalClaimOk` (uses `getLast?`) to the indexed form
  -- `(trajectory)[length - 1]!` required by `terminal_claim_transport`.
  have hLast : d.wire.claim.Holds (w.trajectory[w.trajectory.length - 1]!) := by
    rw [getElem!_pos w.trajectory (w.trajectory.length - 1) hidx]
    rw [← List.getLast_eq_getElem hne']
    have hterm' : decide (d.wire.claim.Holds (w.trajectory.getLast hne')) = true := by
      simpa [List.getLast?_eq_some_getLast hne', terminalClaimOk] using hTerminal
    exact of_decide_eq_true hterm'
  -- Per-pair check via `transitionOk_implies_step`. Pass `i.val + 1` so
  -- the elaborator matches `CertWitness (i.val + 1)` with `w`.
  have hPerPair : ∀ j, j + 1 < w.trajectory.length →
      w.trajectory[j + 1]! = acceleratedStep (w.trajectory[j]!) := by
    intro j hj
    exact transitionOk_implies_step (i.val + 1) w hTransition j hj
  -- Apply Lemma 4 (`terminal_claim_transport`).
  have hReaches : d.wire.claim.Holds
      (accelerated_orbit (i.val + 1) (w.trajectory.length - 1)) :=
    terminal_claim_transport (i.val + 1) w d.wire.claim
      hAnchor hPerPair hLast
  -- Final: assemble `k = length - 1`, then `i.val + 1 = x` via `congrArg`
  -- (avoids the dependent-type motive failure of `rw [hiVal]`).
  let k : Nat := w.trajectory.length - 1
  have hEq : accelerated_orbit (i.val + 1) k = accelerated_orbit x k :=
    congrArg (fun n => accelerated_orbit n k) hiVal
  exact ⟨k, hEq ▸ hReaches⟩

/-! ## v2b.5 — Lemma 6: per_leaf_available_bounded_of_check (kernel-clean)

Constructive per-leaf availability form. Takes per-leaf
`BoundedInputCertificateData` evidence + per-leaf `check = true`
evidence, returns per-leaf `BoundedInputOrbitCertificate` (one call
per leaf; the bound is the per-leaf data's `wire.N`).

Supersedes the v2a hypothesis-eliminator form
`per_leaf_available_bounded_of_hCert` (Q5Integration.lean, retained
as the existing surface; deprecation handled at the call-site level).

**Proof.** Apply `checkBoundedCertificate_sound` (Lemma 5) to the
per-leaf data + per-leaf check evidence + per-leaf reachability
hypothesis. -/

/-- **Lemma 6 (constructive per-leaf availability, kernel-clean).**
    Given per-leaf `BoundedInputCertificateData` (one per verified leaf
    in `t.leaves`) + per-leaf `checkBoundedCertificate = true` evidence
    + the per-leaf `hv + hic + hcr` structural hypotheses, returns the
    per-leaf `BoundedInputOrbitCertificate t l (dataPerLeaf l hl hver).wire.N`.

    Built from `checkBoundedCertificate_sound` (this file, Lemma 5).
    NO `sorry` / `admit` / `axiom`.

    `noncomputable def` because it returns `BoundedInputOrbitCertificate`
    (`: Type`-valued); see `checkBoundedCertificate_sound` for the
    rationale.

    The bound is taken from the per-leaf data's `wire.N` (matching
    `checkBoundedCertificate_sound`'s return type), not as a free
    parameter (avoids the coercion-through-`BoundedInputOrbitCertificate`
    that a free-`N` signature would force). -/
noncomputable def per_leaf_available_bounded_of_check
    (t : CoverageTree)
    (dataPerLeaf : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData)
    (checkPerLeaf : ∀ l ∈ t.leaves, verified t l →
      checkBoundedCertificate t l (dataPerLeaf l (hl : l ∈ t.leaves) (hver : verified t l)) = true)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l →
      ∀ y, (dataPerLeaf l (hl : l ∈ t.leaves) (hver : verified t l)).wire.claim.Holds y → ReachesOne y)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l (dataPerLeaf l hl hver).wire.N :=
  checkBoundedCertificate_sound t l (dataPerLeaf l hl hver) hv hic hver
    (hcr l hl hver) (checkPerLeaf l hl hver)

end CollatzResearch
