/-
Story Q4 — CI-side executable spec for the bounded-orbit data layer
(`FiniteOrbitClaim` + `IsFiniteClaim : LeafClaim → Prop` +
`BoundedOrbitCertificate`).

Per project discipline (MEMORY.md, "BDD Discipline (Lean vs Python)"),
Lean validation is CI-only; this module does not enter any local BDD
gate. All `example` blocks + `def`s are compile-checked by `lake build`
in GitHub CI.

**Trust role of `native_decide`.** Used for closed propositional
equalities on closed `FiniteOrbitClaim` / `LeafClaim` values
(scenarios 1–10). Appropriate as executable-test evidence; does NOT
contribute to any formal-proof basis (PR #57 is a data-layer PR).

Scenarios:
1–6.    `FiniteOrbitClaim.Holds` for `.empty` / `.singleton n` /
        `.bounded K`.
7–10.   `IsFiniteClaim` for `LeafClaim.empty` / `.singleton _` /
        `.bounded _` / `.interval _ _ _`.
11.     Polymorphic `Holds.decidable` signature (names instance).
12.     Polymorphic `IsFiniteClaim.decidable` signature.
13.     `def boundedCertificateClaim` (Prop → Type elimination guard).
14–15.  Polymorphic obligation projections (`orbit_hits_claim`,
        `claim_reaches_one`; PR #58 contract regression, P2 #1).

Sibling test module to `LeafClaimTests.lean` and
`CoverageTreeOrbitTests.lean`.
-/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Scenario 1: `.empty.Holds 0 = False` (no orbit states claimed). -/
example : FiniteOrbitClaim.empty.Holds 0 = False := by
  native_decide

/-- Scenario 2: `.singleton 5 .Holds 5 = True` (exact match). -/
example : (FiniteOrbitClaim.singleton 5).Holds 5 = True := by
  native_decide

/-- Scenario 3: `.singleton 5 .Holds 4 = False` (no match). -/
example : (FiniteOrbitClaim.singleton 5).Holds 4 = False := by
  native_decide

/-- Scenario 4: `.bounded 10 .Holds 0 = True` (well below boundary). -/
example : (FiniteOrbitClaim.bounded 10).Holds 0 = True := by
  native_decide

/-- Scenario 5: `.bounded 10 .Holds 10 = True` (boundary inclusive). -/
example : (FiniteOrbitClaim.bounded 10).Holds 10 = True := by
  native_decide

/-- Scenario 6: `.bounded 10 .Holds 11 = False` (just past boundary). -/
example : (FiniteOrbitClaim.bounded 10).Holds 11 = False := by
  native_decide

/-- Scenario 7: `IsFiniteClaim LeafClaim.empty = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim LeafClaim.empty = True := by
  native_decide

/-- Scenario 8: `IsFiniteClaim (LeafClaim.singleton 5) = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.singleton 5) = True := by
  native_decide

/-- Scenario 9: `IsFiniteClaim (LeafClaim.bounded 10) = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.bounded 10) = True := by
  native_decide

/-- Scenario 10: `IsFiniteClaim (LeafClaim.interval 2 1 1) = False`
    (`.interval` is structurally excluded from `FiniteOrbitClaim`,
    so any `LeafClaim.interval _ _ _` is "not finite" by definition
    of `IsFiniteClaim`). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.interval 2 1 1) = False := by
  native_decide

/-- Scenario 11: polymorphic `Holds.decidable` signature (names
    instance). Mirrors PR #56 v4 polymorphic apply-the-theorem
    pattern. -/
example (c : FiniteOrbitClaim) (y : Nat) :
    Decidable (c.Holds y) :=
  FiniteOrbitClaim.Holds.decidable c y

/-- Scenario 12: polymorphic `IsFiniteClaim.decidable` signature
    (names instance). Mirrors scenario 11. -/
example (c : LeafClaim) :
    Decidable (FiniteOrbitClaim.IsFiniteClaim c) :=
  FiniteOrbitClaim.IsFiniteClaim.decidable c

/-- Scenario 13 (Q4 v3 / PR #57 — API-shape regression).

    `BoundedOrbitCertificate` is `: Type`-valued (proof-carrying
    data bundle), NOT `: Prop`. This `def` performs a `Prop → Type`
    elimination by projecting `c.claim : FiniteOrbitClaim` out of a
    `BoundedOrbitCertificate t l`. A future PR flipping the sort to
    `: Prop` will fail to typecheck this `def` (no dependent
    elimination from `Prop` into `Type`). Mirrors PR #54's
    `def certificateClaim`. -/
def boundedCertificateClaim {t : CoverageTree} {l : CoverageLeaf}
    (c : BoundedOrbitCertificate t l) : FiniteOrbitClaim :=
  c.claim

/-- Scenario 14 (PR #57 P2 #1, post-Codex review): polymorphic
    projection regression for `BoundedOrbitCertificate.orbit_hits_claim`.
    Names the obligation field directly to type-check the contract
    consumed by `coverage_tree_soundness_orbit_cert` (PR #58). Guards
    against signature drift in the Q4 certificate boundary. -/
example {t : CoverageTree} {l : CoverageLeaf}
    (c : BoundedOrbitCertificate t l) :
    ∀ x, descendOrbit t x 0 = some l →
      ∃ k, c.claim.Holds (accelerated_orbit x k) :=
  c.orbit_hits_claim

/-- Scenario 15 (PR #57 P2 #1, post-Codex review): polymorphic
    projection regression for `BoundedOrbitCertificate.claim_reaches_one`.
    Names the obligation field directly to type-check the contract
    consumed by `coverage_tree_soundness_orbit_cert` (PR #58). Guards
    against signature drift in the Q4 certificate boundary. -/
example {t : CoverageTree} {l : CoverageLeaf}
    (c : BoundedOrbitCertificate t l) :
    ∀ y, c.claim.Holds y → ReachesOne y :=
  c.claim_reaches_one

end CollatzResearch
