/-
Q5 PR #4 v2b.1 — `transitionOk` bridge lemmas (kernel-clean).

Story #2 (per-leaf packaging theorem) — **Option C partial close** per
`formal-math-codex-escalate`: ship the v2b.1 transitionOk bridge
lemmas alone, defer Lemmas 5 + 6 (soundness assembly + constructive
per-leaf availability) to a follow-up story after a Lean-expert pass.

## Why partial close (not full closure)

The full closure attempted Lemmas 5 (`checkBoundedCertificate_sound`)
+ 6 (`per_leaf_available_bounded_of_check`) in PR #81; six
consecutive Lean CI runs failed with structurally-materially-different
LOCAL signatures per `formal-math-classify-failure` (Mathlib v4.33.0
surface mismatches + Lean 4 dependent-type elaboration friction).
Six failed iterations crosses the LEAN_PATTERNS.md "stop guessing"
threshold (≥2 attempts on the same logical proof step), and the
multi-LOCAL pattern signals an unstable mental model of Lean 4 v4.33.0
surface interactions rather than a hard problem. Per
`formal-math-codex-escalate`, the disciplined move is partial close
plus HUMAN_GATE escalation; Option C ships the kernel-clean
bridge alone (independently useful, no failure modes), with
Lemmas 5 + 6 deferred.

## What this module contains

Two kernel-clean lemmas closing the missing bridge between
`transitionOk w = true` (the per-witness transition-fold Boolean check)
and the per-pair `acceleratedStep` step relation required by
`terminal_claim_transport` (Q5Integration.lean). Both lemmas are
pure `List`/`Bool` reasoning; no `sorry` / `admit` / `axiom`.

## Trust boundary (unchanged from prior v2b attempts)

```
Python serialized evidence → (PR #63 parser)
                            → BoundedInputCertificateWire
                            → decodeBoundedInputCertificateData (PR #62)
                            → BoundedInputCertificateData
                            → checkBoundedCertificate (PR #62)
                            → Bool verifier (PR #4 soundness — deferred)
                            → BoundedInputOrbitCertificate (Q5Integration.lean)
                            → coverage_tree_soundness_orbit_cert_bounded
                              (Q5Integration.lean)
                            → ∀ x, 0 < x → x ≤ N → ReachesOne x
```

The Lemmas 5 + 6 step is deferred; the `transitionOk` → per-pair
`acceleratedStep` bridge (this module) is independently kernel-clean
and closes the v2b.1 piece of the v2b P0 finding.

## Reachability evidence tier (ADR 0009)

This module is data-side: it turns the verifier's `transitionOk = true`
fold into per-pair `acceleratedStep` facts. Those facts are the per-step
hypotheses that the symbolic transport (`trajectory_index`,
`terminal_claim_transport`) consumes on the reachability path. No orbit
equation is evaluated here, and `native_decide` is not used.

The reachability conclusion that these facts feed is kernel-checkable only
under the ADR 0009 terminal-value-1 tier: the claim's `Holds` must reduce
to `y = 1`. See `docs/adr/0009-reachability-evidence-tier.md` and
`docs/trust-model.md`.

## Lessons applied (Q4 v3 + Q5 v2b.2 + META)

- **Q4 v3 (`: Type` sort):** no `: Type`-valued structures introduced.
- **Q5 v2b.2 (Mathlib v4.33.0 bridge):** uses `List.length_zip` +
  `List.getElem_zip` + `List.getElem_tail` directly (the prior v2b.2
  P0 fix's worry that this would need `sorry`s resolved once those
  Mathlib lemmas are accessed cleanly).
- **META § 3.2 (per-leaf availability):** Lemmas 5 + 6 deferred to a
  separate story, with explicit re-scoping deferred as a
  HUMAN_GATE decision (not silently dropped).

Story Q5 / PR #4 v2b.1 — `transitionOk_implies_step` +
`transitionOk_implies_step_forall` (this file). Both kernel-clean
(no `sorry` / `admit` / `axiom`). Closes the v2b.1 piece of the v2b
P0 finding; Lemmas 5 + 6 deferred.
-/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## v2b.1 — transitionOk → per-pair step (Mathlib v4.33.0 bridge)

The Q5 v2b.2 Codex P0 fix refactored Lemmas 3 + 4 (in `Q5Integration.lean`)
to take the per-pair `acceleratedStep` check directly as a hypothesis,
bypassing the `transitionOk`-fold bridge that previously needed 2
`sorry`s for `List.length_zip` and `List.getElem_zip`. This module
closes that bridge using Mathlib v4.33.0's `List.length_zip` +
`List.getElem_zip` + `List.getElem_tail` directly — all three are used
successfully in `Q5RoutingPartition.routing_transition_fold_step`
(also v4.33.0-pinned), so the underlying lemmas exist in the pinned
Mathlib.

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

    Convenience wrapper for the curry-friendly form used by any future
    v2b.4 (soundness assembly) re-attempt.

    **Evidence tier (ADR 0009).** Data-side bridge: it produces the
    per-step `acceleratedStep` facts that the symbolic transport consumes
    on the reachability path. It evaluates no orbit equation, and the
    reachability conclusion it supports is kernel-checkable only under
    the terminal-value-1 tier.

    Kernel-clean (no `sorry` / `admit` / `axiom`). -/
theorem transitionOk_implies_step_forall (x : Nat) (w : CertWitness x)
    (hTrans : transitionOk w = true) :
    ∀ i, i + 1 < (w.trajectory).length →
      (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) := by
  intro i hi
  exact transitionOk_implies_step x w hTrans i hi

/-- **WP-CF-1 — the terminal-value-1 instance.** An accepted witness whose
    claim is a terminal-value-1 claim yields `ReachesOne x` with **no
    reachability hypothesis** and **no `native_decide`**.

    This is the theorem that makes the ADR 0009 evidence tier consequential.
    The tier admits a reachability witness exactly when the certificate's
    terminal value is 1, and this theorem closes that case.

    **What is assumed.** `hclaim : ∀ y, claim.Holds y → y = 1` says the
    claim is a terminal-value-1 claim: the only orbit state it admits is
    `1` itself. `FiniteOrbitClaim.singleton 1` is the canonical instance
    (see `checkCertWitness_singleton_one_reaches_one` below). No
    hypothesis asserts that anything reaches 1.

    **The two witnesses, kept apart.** They are distinct facts and this
    proof does not conflate them:

    - The **source's** orbit equality `accelerated_orbit x k = 1` is
      established at the witness index the certificate supplies — `k =
      length - 1` for a trajectory witness — by rewriting
      (`trajectory_index` inside `terminal_claim_transport`). The orbit
      is never evaluated at any index.
    - The **claimed terminal value** `1` has its own zero-step
      reachability witness, `ReachesOne 1` at `k := 0`, closed by
      `accelerated_orbit_zero 1`.

    The composition `orbit_predecessor_reaches_one` then yields
    `ReachesOne x` with source witness index `(length - 1) + 0`.

    **Trust boundary.** Unchanged. No orbit equation is evaluated, no
    `native_decide` appears in the proof, and the admission budget is
    untouched. The acceptance hypothesis `hcheck` is a data-side
    Boolean check; what this theorem adds is that its *reachability*
    consequence is kernel-checked. -/
theorem checkCertWitness_terminal_value_one_reaches_one
    (x : Nat) (claim : FiniteOrbitClaim) (t : CoverageTree) (l : CoverageLeaf)
    (w : CertWitness x)
    (hcheck : checkCertWitness x claim t l w = true)
    (hclaim : ∀ y, claim.Holds y → y = 1) :
    ReachesOne x := by
  -- Decompose acceptance into its five conjuncts.
  obtain ⟨hAnchor, _, _, hTerminal, hTransition⟩ :=
    (checkCertWitness_decompose x claim t l w).mp hcheck
  -- The per-step `acceleratedStep` relation, from the transition fold.
  have hTrans : ∀ i, i + 1 < (w.trajectory).length →
      (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) :=
    transitionOk_implies_step_forall x w hTransition
  -- The terminal value satisfies the claim.
  unfold terminalClaimOk at hTerminal
  cases hl : w.trajectory.getLast? with
  | none =>
      simp [hl] at hTerminal
  | some last =>
      have hlast : decide (claim.Holds last) = true := by
        simpa [hl] using hTerminal
      have hHolds : claim.Holds last := of_decide_eq_true hlast
      -- The trajectory is non-empty: its `getLast?` is `some last`.
      have hne : w.trajectory ≠ [] := by
        intro h
        rw [h] at hl
        simp at hl
      have hpos : 0 < w.trajectory.length := List.length_pos_iff.mpr hne
      -- Bridge the terminal value to the indexed form that
      -- `terminal_claim_transport` consumes.
      have hLast : claim.Holds (w.trajectory[w.trajectory.length - 1]!) := by
        have hidx : w.trajectory.length - 1 < w.trajectory.length := by
          omega
        rw [getElem!_pos w.trajectory (w.trajectory.length - 1) hidx]
        rw [← List.getLast_eq_getElem hne]
        have hget : w.trajectory.getLast hne = last := by
          rw [List.getLast?_eq_some_getLast hne] at hl
          exact Option.some.inj hl
        rw [hget]
        exact hHolds
      -- Transport the terminal claim to the source's orbit state.
      have hOrbitClaim :
          claim.Holds (accelerated_orbit x (w.trajectory.length - 1)) :=
        terminal_claim_transport x w claim hAnchor hTrans hLast
      -- The claim obligation: the only admitted state is 1, and 1 reaches
      -- 1 in zero steps.
      have hClaim : ∀ y, claim.Holds y → ReachesOne y := by
        intro y hy
        have hy1 : y = 1 := hclaim y hy
        subst hy1
        exact ⟨0, accelerated_orbit_zero 1⟩
      exact orbit_predecessor_reaches_one x (w.trajectory.length - 1)
        (accelerated_orbit x (w.trajectory.length - 1)) rfl
        (hClaim _ hOrbitClaim)

/-- **WP-CF-1, canonical instance.** The terminal-value-1 claim
    `FiniteOrbitClaim.singleton 1` yields reachability from an accepted
    witness with no reachability hypothesis.

    The claim obligation `∀ y, claim.Holds y → y = 1` holds by
    construction for this shape, so it is discharged here rather than
    assumed. -/
theorem checkCertWitness_singleton_one_reaches_one
    (x : Nat) (t : CoverageTree) (l : CoverageLeaf) (w : CertWitness x)
    (hcheck : checkCertWitness x (FiniteOrbitClaim.singleton 1) t l w = true) :
    ReachesOne x :=
  checkCertWitness_terminal_value_one_reaches_one x (FiniteOrbitClaim.singleton 1)
    t l w hcheck (by
      intro y hy
      simpa [FiniteOrbitClaim.Holds] using hy)

/-- **WP-CF-1 regression.** The theorem is not merely stated: it is used
    by a downstream derivation, so a change that broke it would fail this
    example at compile time.

    The source `x = 2` reaches 1 at the certificate's witness index
    `length - 1`, which for the canonical two-leaf even trajectory
    `[2, 7, 11, 17, 13, 5, 1]` is `k = 6` — not at `k := 0`; the
    `k := 0` witness belongs to the claimed terminal value `1`. -/
example (t : CoverageTree) (l : CoverageLeaf)
    (w : CertWitness 2)
    (hcheck : checkCertWitness 2 (FiniteOrbitClaim.singleton 1) t l w = true) :
    ReachesOne 2 :=
  checkCertWitness_singleton_one_reaches_one 2 t l w hcheck

end CollatzResearch
