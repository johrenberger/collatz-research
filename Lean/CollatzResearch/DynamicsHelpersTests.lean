/-
Story 02c/03c — CI-side executable spec for the Dynamics helper lemmas.

These `example` blocks are compile-checked by `lake build` in GitHub CI,
not run locally. Per `docs/story-07c-4-structural-induction.md` and the
project-wide rule (MEMORY.md, "BDD Discipline (Lean vs Python)"), Lean
validation is CI-only; this module does not enter any local BDD gate.

The scenarios mirror the `standardStep_of_odd` lemma's claim: for
specific odd inputs, `standardStep n = 3 * n + 1`. The executable spec
is regression evidence for the lemma's claim; the proof's kernel check
is the formal verification.

This is a sibling test module to `EquivalenceHelpersTests.lean`
(PR #42, helper #1). Each helper-lemma PR introduces its own test
module to keep the diff scoped; cross-PR consolidation is a follow-up.
-/

import CollatzResearch.Dynamics

namespace CollatzResearch

/-- Scenario: standardStep_of_odd at n = 1. `1` is odd, so `standardStep 1 = 3 * 1 + 1 = 4`. -/
example : standardStep 1 = 3 * 1 + 1 :=
  standardStep_of_odd 1 (by decide)

/-- Scenario: standardStep_of_odd at n = 5. `5` is odd, so `standardStep 5 = 3 * 5 + 1 = 16`. -/
example : standardStep 5 = 3 * 5 + 1 :=
  standardStep_of_odd 5 (by decide)

end CollatzResearch
