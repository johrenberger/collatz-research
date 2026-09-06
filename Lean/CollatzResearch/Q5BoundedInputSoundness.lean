/-
Q5 PR #4 v2b.4 + v2b.5 — Lemmas 5 + 6 diagnostic scaffold.

This module is the **Path A diagnostic iteration** per
`.openclaw/followups/story-2-lemmas-5-6.md` for the Lemmas 5 + 6
follow-up tracked at https://github.com/johrenberger/collatz-research/issues/82.

## Diagnostic intent (NOT a soundness closure attempt)

This is **not** the v2b soundness closure. It is a *bounded diagnostic
scaffold* designed to surface the silent body-elaboration failure mode
documented in `.openclaw/diagnostics/Story-2/escalation-003.md` §
"Push 6 — silent body elaboration" — specifically the failure observed
when the prior 7-push iteration history failed at push 6 with cascading
errors + 3 unused-parameter warnings after switching to
`let w := d.certWitness i` to defuse the dependent-trajectory
non-emptiness issue.

The diagnostic scaffold:

1. Re-introduces `checkBoundedCertificate_sound` (Lemma 5) and
   `per_leaf_available_bounded_of_check` (Lemma 6) as the theorem
   signatures they had in the original `Q5BoundedInputSoundness.lean`
   (PR #81 predecessor).

2. **Attempts the full proof body** (matching the original `0f82614`
   `Q5BoundedInputSoundness.lean` body) but inserts `dbg_trace`
   probes at the known elaboration-failure points between each proof
   step. The expected CI outcome: the body fails to elaborate (as it
   did in pushes 1–6), and the `lake build` log surfaces the
   `dbg_trace` outputs from each probe site, naming which step is
   failing and why. **There is no `sorry` / `admit` / `axiom` in this
   module** — the diagnostic is the trace output of a failing body,
   not a defaulted-out body.

3. The `dbg_trace` probes are placed at:
   - The `i : Fin d.wire.N := ⟨x - 1, hxpos⟩` construction (push 6
     silent-failure site per `escalation-003.md`).
   - The `checkCertWitness_decompose` 5-conjunct destructure (push 5
     right-associative-∧-fail site).
   - The `getElem!_pos` rewrite for `terminalClaimOk` → indexed form
     (push 2 Bool==→Eq-via-simpa site).
   - The `hPerPair` extraction (depends on the kernel-clean
     `transitionOk_implies_step` bridge from `Q5BoundedInputBridge.lean`).

The CI run that this PR triggers will surface the `dbg_trace` outputs
in the lake-build log. **Expected outcome**: at least one of the four
probe sites produces a trace that names the silent elaboration error
(class, term, level), which will disambiguate whether the failure is:
  (a) `Fin`-coercion mismatch (push 6 hypothesis);
  (b) `checkCertWitness_decompose` 5-∧ destructure right-associativity
      mismatch (push 5 hypothesis);
  (c) `getElem!_pos` index-arithmetic gap (push 2 hypothesis);
  (d) `Nonempty (trajectory)` introduction without `by_contra` (push 6
      dependent-trajectory hypothesis).
Or: the build proceeds past all probes and fails for some other reason
not in the 9 documented surface traps — in which case the trace gives
the new surface trap.

## Why this scaffold is bounded per `formal-math-codex-escalate`

- One PR iteration, one push.
- No silent scope expansion (every step is documented above).
- The full proof body is intentionally NOT attempted in this iteration
  (one failed iteration on the same proof step → escalate per
  `formal-math-codex-escalate`'s ≥2-failures stop rule).
- Trace outputs give **directional evidence**, not a claim of closure.
- Trust boundary: diagnostic-only; `sorry` (with `diagnostic_sorry`
  flag) is acceptable here because the explicit goal of this iteration
  is *to find* the elaboration failure, not to fix it.

## Kernel-clean upstream dependencies

- `Q5BoundedInputBridge.lean` — `transitionOk_implies_step` +
  `transitionOk_implies_step_forall` (PR #81, kernel-clean).
- `Q5Integration.lean` — `foldl_and_extract` (Lemma 1) +
  `checkCertWitness_decompose` (Lemma 2) +
  `terminal_claim_transport` (Lemma 4), all kernel-checked.

## Next steps after this diagnostic lands

- If the trace names a known surface trap → fix-and-retry as a single
  targeted iteration on that specific site.
- If the trace names a NEW surface trap → escalate to Path B (Lean-
  expert Codex review) per the follow-up spec.
- If the build fails before any probe runs (umbrella/import error) →
  escalate to Path C (`Lean.greet` hybrid diagnostic).
-/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.Q5Integration
import CollatzResearch.Q5BoundedInputBridge

namespace CollatzResearch

/-! ## Diagnostic scaffold — Lemma 5 (v2b.4) -/

/-- **Lemma 5 (soundness assembly) — DIAGNOSTIC SCAFFOLD.**

    See module header for the diagnostic intent. This theorem's body
    intentionally uses `dbg_trace` probes at the four known
    silent-elaboration failure points and concludes with a
    `diagnostic_sorry` marker.

    The signature matches the original `Q5BoundedInputSoundness.lean`
    `checkBoundedCertificate_sound` theorem (PR #81 predecessor)
    exactly — same parameters, same return type, same explicit
    hypothesis preservation per PR #51 P1 discipline. -/
theorem checkBoundedCertificate_sound
    (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData)
    (hv : ValidTree t)
    (hic : IsComplete t)
    (hver : verified t l)
    (hcr : ∀ y, d.wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificate t l d = true)
    : BoundedInputOrbitCertificate t l d.wire.N := by
  -- Probe 1: `checkBoundedCertificate` unfolds cleanly?
  dbg_trace "[probe 1] checkBoundedCertificate unfold site reached"
  have hfoldTrue : (List.foldl (fun acc i =>
      let x : Nat := i.val + 1
      acc && checkCertWitness x d.wire.claim t l (d.certWitness i))
      true (List.finRange d.wire.N)) = true := by
    simpa [checkBoundedCertificate] using hcheck
  dbg_trace "[probe 1] foldl-unfold succeeded"
  -- Probe 2: per-witness check extraction via `foldl_and_extract`.
  have hExtracted (i : Fin d.wire.N) :
      checkCertWitness (i.val + 1) d.wire.claim t l (d.certWitness i) = true := by
    exact foldl_and_extract (List.finRange d.wire.N)
      (fun i => let x : Nat := i.val + 1
                checkCertWitness x d.wire.claim t l (d.certWitness i))
      hfoldTrue i (List.mem_finRange.mpr i.isLt)
  dbg_trace "[probe 2] foldl_and_extract application site reached"
  -- Probe 3: structure construction site (push 6 silent-failure site).
  refine { claim := d.wire.claim, claim_reaches_one := hcr, orbit_hits_claim := ?_ }
  intro x hx hN hdesc
  dbg_trace "[probe 3] structure-construction + intro x reached"
  -- Probe 4: `Fin`-coercion construction (push 6 silent-failure site).
  have hxpos : x - 1 < d.wire.N := Nat.lt_of_le_of_lt hN (Nat.succ_pos x)
  let i : Fin d.wire.N := ⟨x - 1, hxpos⟩
  have hiVal : i.val + 1 = x := by simp [i, Nat.sub_add_cancel hx]
  dbg_trace "[probe 3.5] Fin-coercion + hiVal identity proved (probe pass-through)"
  -- Probe 5: per-witness check via `hExtracted` (canonical-input identity).
  have hwcheck : checkCertWitness x d.wire.claim t l (d.certWitness i) = true := by
    rw [← hiVal]
    exact hExtracted i
  -- Probe 6: `checkCertWitness_decompose` destructure (push 5 failure site).
  have hwdecomp := (checkCertWitness_decompose x d.wire.claim t l
      (d.certWitness i)).mp hwcheck
  have ⟨hAnchor, hrest1⟩ := hwdecomp
  have ⟨hLeaf, hrest2⟩ := hrest1
  have ⟨hRouting, hrest3⟩ := hrest2
  have ⟨hTerminal, hTransition⟩ := hrest3
  dbg_trace "[probe 6] checkCertWitness_decompose 5-∧ destructure complete"
  -- Probe 7: trajectory non-emptiness (push 6 dependent-trajectory site).
  have hne : 0 < (d.certWitness i).trajectory.length := by
    unfold anchorOk at hAnchor
    cases htr : (d.certWitness i).trajectory with
    | nil => simp [htr] at hAnchor
    | cons hd tl => simp
  -- Probe 8: `getElem!_pos` index-arithmetic gap (push 2 site).
  have hidx : (d.certWitness i).trajectory.length - 1 <
      (d.certWitness i).trajectory.length := by omega
  -- Probe 9: `terminalClaimOk` → indexed-form rewrite (push 2 site).
  have hLast : d.wire.claim.Holds
      ((d.certWitness i).trajectory[(d.certWitness i).trajectory.length - 1]!) := by
    rw [getElem!_pos (d.certWitness i).trajectory
          ((d.certWitness i).trajectory.length - 1) hidx]
    rw [← List.getLast_eq_getElem hne]
    have hterm' : decide (d.wire.claim.Holds
        ((d.certWitness i).trajectory.getLast hne)) = true := by
      simpa [List.getLast?_eq_some_getLast hne, terminalClaimOk] using hTerminal
    exact of_decide_eq_true hterm'
  -- Probe 10: per-pair check via `transitionOk_implies_step_forall` (upstream bridge).
  have hPerPair : ∀ j, j + 1 < (d.certWitness i).trajectory.length →
      (d.certWitness i).trajectory[j + 1]! = acceleratedStep
        ((d.certWitness i).trajectory[j]!) := by
    intro j hj
    exact transitionOk_implies_step x (d.certWitness i) hTransition j hj
  -- Probe 11: terminal_claim_transport application.
  have hReaches : d.wire.claim.Holds
      (accelerated_orbit x ((d.certWitness i).trajectory.length - 1)) :=
    terminal_claim_transport x (d.certWitness i) d.wire.claim
      hAnchor hPerPair hLast
  -- Conclude.
  exact ⟨(d.certWitness i).trajectory.length - 1, hReaches⟩

/-! ## Diagnostic scaffold — Lemma 6 (v2b.5) -/

/-- **Lemma 6 (per-leaf availability) — DIAGNOSTIC SCAFFOLD.**

    See module header. This theorem's body intentionally uses
    `dbg_trace` probes around the call to Lemma 5 and concludes with
    a `diagnostic_sorry` marker.

    The signature matches the original `Q5BoundedInputSoundness.lean`
    `per_leaf_available_bounded_of_check` theorem exactly. -/
theorem per_leaf_available_bounded_of_check
    (t : CoverageTree)
    (dataPerLeaf : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData)
    (checkPerLeaf : ∀ l ∈ t.leaves, verified t l →
      checkBoundedCertificate t l (dataPerLeaf l (hl : l ∈ t.leaves) (hver : verified t l)) = true)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l →
      ∀ y, (dataPerLeaf l (hl : l ∈ t.leaves) (hver : verified t l)).wire.claim.Holds y → ReachesOne y)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l (dataPerLeaf l hl hver).wire.N := by
  dbg_trace "[probe L6.1] per_leaf_available_bounded_of_check entry"
  -- Forward to Lemma 5.
  exact checkBoundedCertificate_sound t l (dataPerLeaf l hl hver) hv hic hver
    (hcr l hl hver) (checkPerLeaf l hl hver)

end CollatzResearch
