/-
Story 02c/03c — CI-side executable spec for the Equivalence helper lemmas.

These `example` blocks are compile-checked by `lake build` in GitHub CI,
not run locally. Per `docs/story-07c-4-structural-induction.md` and the
project-wide rule (MEMORY.md, "BDD Discipline (Lean vs Python)"), Lean
validation is CI-only; this module does not enter any local BDD gate.

The scenarios mirror the `standardTrajectory_succ_shift` lemma's claim:
for specific inputs, both sides of the shift equality reduce to the same
value via `rfl`. The executable spec is regression evidence for the
lemma's claim; the proof's kernel check is the formal verification.
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

end CollatzResearch