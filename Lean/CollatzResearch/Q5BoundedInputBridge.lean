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

    Kernel-clean (no `sorry` / `admit` / `axiom`). -/
theorem transitionOk_implies_step_forall (x : Nat) (w : CertWitness x)
    (hTrans : transitionOk w = true) :
    ∀ i, i + 1 < (w.trajectory).length →
      (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) := by
  intro i hi
  exact transitionOk_implies_step x w hTrans i hi

end CollatzResearch
