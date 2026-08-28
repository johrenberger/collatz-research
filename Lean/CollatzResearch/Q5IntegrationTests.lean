/-
Q5 PR #4 v1 — bounded-input integration tests.

Mirrors the test patterns from PR #57 (`FiniteOrbitClaimTests.lean`)
+ PR #58 (`CoverageTreeOrbitTests.lean`):

- API-shape regression: `boundedInputOrbitCertShape` (mirrors
  PR #57's `boundedCertificateClaim`) — defends the
  `BoundedInputOrbitCertificate` structure's shape against
  accidental changes to field order / types.
- Compile-check scenarios for `coverage_tree_soundness_orbit_cert_bounded`:
  - Type-only check that the bounded companion theorem closes
    for the `singleLeafTree` (the Q5 verifier test fixture) +
    bounded `N`.
  - Type-only check that `per_leaf_available_bounded` closes
    from the `hCert` hypothesis.
  - Polymorphic apply-the-theorem check (mirrors PR #58 scenario
    12).

v2 will add scenarios that exercise the verifier soundness
theorem (`checkBoundedCertificate_sound`) — once the
`checkBoundedCertificate = true → BoundedInputOrbitCertificate`
soundness proof is in place.

Story Q5 / PR #4 v1 (bounded-input integration tests — API-shape
regression + companion-theorem type checks; soundness-theorem
tests deferred to v2). -/

import CollatzResearch.CoverageTree
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## API-shape regression

Defends `BoundedInputOrbitCertificate`'s structure against accidental
changes. If any field is renamed, removed, or reordered, this
def-equality will fail to typecheck (kernel-decided). -/

/-- API-shape guard: `BoundedInputOrbitCertificate` has the three
    fields `(claim : FiniteOrbitClaim, orbit_hits_claim : ∀ x ≤ N
    → descendOrbit t x 0 = some l → ∃ k, claim.Holds
    (accelerated_orbit x k), claim_reaches_one : ∀ y,
    claim.Holds y → ReachesOne y)`. Mirrors PR #57's
    `boundedCertificateClaim` (def-equality closed by `rfl`). -/
example (t : CoverageTree) (l : CoverageLeaf) (N : Nat) :
    BoundedInputOrbitCertificate t l N =
      { claim : FiniteOrbitClaim
        orbit_hits_claim :
          ∀ x, x ≤ N → descendOrbit t x 0 = some l →
            ∃ k, claim.Holds (accelerated_orbit x k)
        claim_reaches_one :
          ∀ y, claim.Holds y → ReachesOne y } := rfl

/-! ## Compile-check scenarios for `coverage_tree_soundness_orbit_cert_bounded`

Type-only checks (proof values supplied as hypotheses, like PR #58's
parallel scenarios). The closed-form example in `Q5Integration.lean`
already exercises the theorem directly; these scenarios verify the
theorem type-checks against concrete tree + bounded `N`. -/

/-- Scenario 1: `coverage_tree_soundness_orbit_cert_bounded` closes
    for `singleLeafTree` (the Q5 verifier test fixture — single
    leaf, every input routes to it) + bounded `N = 3` + a
    `hCert` hypothesis per the Q4 v3 `hCert` pattern.

    `hv` and `hc` discharged via `native_decide` (the standard
    structural invariants for `singleLeafTree`).

    `hCert` is supplied as a hypothesis for v1 — the verifier
    soundness theorem (v2) will provide a constructive
    implementation. The type-check confirms the bounded companion
    theorem's signature is well-formed against concrete inputs. -/
example (N : Nat) (hN : N = 3 := rfl)
    (hv : ValidTree singleLeafTree := by native_decide)
    (hc : IsComplete singleLeafTree := by native_decide)
    (hCert : ∀ l ∈ singleLeafTree.leaves, verified singleLeafTree l →
      BoundedInputOrbitCertificate singleLeafTree l N)
    (x : Nat) (hx : 0 < x) (hN_x : x ≤ N) :
    ∃ l, l ∈ singleLeafTree.leaves ∧ verified singleLeafTree l ∧
         descendOrbit singleLeafTree x 0 = some l ∧
         ReachesOne x :=
  coverage_tree_soundness_orbit_cert_bounded singleLeafTree N hv hc hCert x hx hN_x

/-- Scenario 2: `per_leaf_available_bounded` closes for the same
    `singleLeafTree` + bounded `N`, taking the per-leaf certificate
    from `hCert`. The hypothesis-based v1 form.

    v2 will replace the hypothesis with a constructive derivation
    from the verifier soundness theorem. -/
example (N : Nat)
    (hCert : ∀ l ∈ singleLeafTree.leaves, verified singleLeafTree l →
      BoundedInputOrbitCertificate singleLeafTree l N)
    (l : CoverageLeaf)
    (hl : l ∈ singleLeafTree.leaves)
    (hver : verified singleLeafTree l) :
    BoundedInputOrbitCertificate singleLeafTree l N :=
  per_leaf_available_bounded singleLeafTree N hCert l hl hver

/-- Scenario 3 (polymorphic — mirrors PR #58 scenario 12): the
    bounded companion theorem's conclusion type-matches the
    `∃ l, l ∈ t.leaves ∧ verified t l ∧ descendOrbit t x 0 =
    some l ∧ ReachesOne x` shape for any tree + `N` + `x ≤ N`.

    Defends the theorem's signature against accidental changes. -/
example (t : CoverageTree) (N : Nat)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l →
      BoundedInputOrbitCertificate t l N)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    (∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         ReachesOne x) :=
  coverage_tree_soundness_orbit_cert_bounded t N hv hic hCert x hx hN

end CollatzResearch
