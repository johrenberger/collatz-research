/-
Story 02c/03c — CI-side executable spec for the Equivalence helper lemmas.

These `example` blocks are compile-checked by `lake build` in GitHub CI,
not run locally. Per `docs/story-07c-4-structural-induction.md` and the
project-wide rule (MEMORY.md, "BDD Discipline (Lean vs Python)"), Lean
validation is CI-only; this module does not enter any local BDD gate.

The scenarios mirror the helper-lemmas' claims and the main lifting
theorem `acceleratedTrajectory_reaches_one_implies_standard`:
for specific inputs, both sides of the equality reduce to the same
value via `rfl` (or a small decidable call). The executable spec is
regression evidence for the lemma's claim; the proof's kernel check is
the formal verification. Added per Codex P2 review on PR #46 and #47:
n = 1, m = 0 (trivial) and n = 3, m = 2 (nontrivial odd trajectory)
cover the boundary and the inductive step.
-/

import CollatzResearch.Equivalence

namespace CollatzResearch

/-- Scenario: shift lemma base case `k = 0`. Both sides reduce
definitionally to `standardStep n`; closed by `rfl`. -/
example (n : Nat) : standardTrajectory n (0 + 1) = standardTrajectory (standardStep n) 0 := rfl

/-- Scenario: shift lemma at a specific numeric input `n = 5, k = 3`.
Both sides reduce to `2` via the standard Collatz trajectory
`5 → 16 → 8 → 4 → 2` (4 standard steps); closed by `rfl`. -/
example : standardTrajectory 5 (3 + 1) = standardTrajectory (standardStep 5) 3 := rfl

/-- Scenario: standardTrajectory_pow_div at x = 6, k = 1.
The closed witness is checked with the helper, not merely by trajectory reduction. -/
example : standardTrajectory 6 1 = 6 / 2 ^ 1 :=
  standardTrajectory_pow_div 6 1 (by decide)

/-- Scenario: standardTrajectory_pow_div at x = 8, k = 3.
The closed witness is checked with the helper, not merely by trajectory reduction. -/
example : standardTrajectory 8 3 = 8 / 2 ^ 3 :=
  standardTrajectory_pow_div 8 3 (by decide)

/-- Scenario: trajectory_succ_shift at n = 5, k = 3.
trajectory 5 4 = acceleratedStep³ 5 = 1 = trajectory (acceleratedStep 5) 3. -/
example : trajectory_succ_shift 5 3 := rfl

/-- Scenario: standardTrajectory_compose at n = 5, a = 2, b = 3.
standardTrajectory (standardTrajectory 5 2) 3 = standardTrajectory 8 3 = 1 = standardTrajectory 5 5. -/
example : standardTrajectory_compose 5 2 3 := rfl

/-- Scenario: acceleratedTrajectory_reaches_one_implies_standard at n = 1, m = 0.
trajectory 1 0 = 1, so standardTrajectory 1 0 = 1. Witness m' = 0. -/
example : acceleratedTrajectory_reaches_one_implies_standard 1 0 (by decide) rfl := ⟨0, rfl⟩

/-- Scenario: acceleratedTrajectory_reaches_one_implies_standard at n = 3, m = 2.
trajectory 3 2 = 1 (5 → 16 → 1), so standardTrajectory 3 7 = 1. Witness m' = 7. -/
example : acceleratedTrajectory_reaches_one_implies_standard 3 2 (by decide) (by decide) := ⟨7, rfl⟩

/-- Scenario: standardTrajectory_pow_div at x = 0, k = 0 (zero boundary).
`2^0 = 1` divides all `Nat` (including `0`), so `standardTrajectory 0 0 = 0 / 1 = 0`.
The closed witness is checked with the helper. -/
example : standardTrajectory 0 0 = 0 / 2 ^ 0 :=
  standardTrajectory_pow_div 0 0 (by decide)

end CollatzResearch