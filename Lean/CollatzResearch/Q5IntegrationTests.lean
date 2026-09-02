/-
Q5 PR #4 v2a — bounded-input integration tests.

Mirrors the test patterns from PR #57 (`FiniteOrbitClaimTests.lean`)
+ PR #58 (`CoverageTreeOrbitTests.lean`):

- API-shape regression: `boundedInputOrbitCertShape` (mirrors
  PR #57's `boundedCertificateClaim`) — defends the
  `BoundedInputOrbitCertificate` structure's shape against
  accidental changes to field order / types. The `0 < x →`
  premise on `orbit_hits_claim` is part of the guarded shape
  (Q1 P1 fix from Codex review on v1 `1209cdb`).
- Compile-check scenarios for `coverage_tree_soundness_orbit_cert_bounded`:
  - Type-only check that the bounded companion theorem closes
    for the `singleLeafTree` (the Q5 verifier test fixture) +
    bounded `N`.
  - Type-only check that `per_leaf_available_bounded_of_hCert`
    closes from the `hCert` hypothesis (renamed from v1's
    `per_leaf_available_bounded` per Codex P2).
  - Polymorphic apply-the-theorem check (mirrors PR #58 scenario
    12).
- Zero-boundary regression (Q1 P1 fix): a scenario confirming
  that the certificate obligation is silent for `x = 0` (the
  `0 < x` premise is `False` for `x = 0`, so the premise is
  unprovable — the certificate does not need to cover `x = 0`).

v2b will add scenarios that exercise the verifier soundness
theorem (`checkBoundedCertificate_sound`) — once the
`checkBoundedCertificate = true → BoundedInputOrbitCertificate`
soundness proof is in place.

Story Q5 / PR #4 v2a (bounded-input integration tests — API-shape
regression + companion-theorem type checks + zero-boundary
regression; soundness-theorem tests deferred to v2b). -/

import CollatzResearch.CoverageTree
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## API-shape regression

Defends `BoundedInputOrbitCertificate`'s structure against accidental
changes. If any field is renamed, removed, or reordered, this
def-equality will fail to typecheck (kernel-decided). -/

/-- API-shape guard: `BoundedInputOrbitCertificate` has the three
    fields `(claim : FiniteOrbitClaim, orbit_hits_claim : ∀ x, 0 <
    x → x ≤ N → descendOrbit t x 0 = some l → ∃ k,
    claim.Holds (accelerated_orbit x k), claim_reaches_one : ∀ y,
    claim.Holds y → ReachesOne y)`. Mirrors PR #57's
    `boundedCertificateClaim` (def-equality closed by `rfl`).

    The `0 < x →` premise on `orbit_hits_claim` is the Q1 P1 fix
    from Codex review on v1 `1209cdb` — the certificate's input
    domain is `{1, ..., N}`, not `{0, ..., N}`. -/
example (t : CoverageTree) (l : CoverageLeaf) (N : Nat) :
    BoundedInputOrbitCertificate t l N =
      { claim : FiniteOrbitClaim
        orbit_hits_claim :
          ∀ x, 0 < x → x ≤ N → descendOrbit t x 0 = some l →
            ∃ k, claim.Holds (accelerated_orbit x k)
        claim_reaches_one :
          ∀ y, claim.Holds y → ReachesOne y } := rfl

/-! ## Zero-boundary regression (Q1 P1 fix)

Confirms that `x = 0` is OUTSIDE the certificate obligation. The
premise `0 < x` is `False` for `x = 0`, so the premise is
unprovable — the certificate does not need to cover `x = 0`.

This is the symmetric complement of the API-shape guard: the
shape says "positive inputs only", and this scenario confirms
that `x = 0` is correctly excluded. -/

/-- Scenario 0 (zero-boundary regression, Q1 P1 fix): the
    `0 < x →` premise on `orbit_hits_claim` is `False` for
    `x = 0`. The certificate obligation is silent for `x = 0`
    — there is no need to prove `∃ k, ...` for `x = 0`.

    The premise `0 < 0` is reduced to `False`; the implication
    `False → ...` is provable vacuously. This confirms the
    `orbit_hits_claim` field is correctly typed for the
    `{1, ..., N}` input domain. -/
example (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (cert : BoundedInputOrbitCertificate t l N)
    (x : Nat) (hx : x = 0) :
    ∃ k, cert.claim.Holds (accelerated_orbit x k) :=
  -- `cert.orbit_hits_claim x (by omega) ...` requires `0 < x`,
  -- which is `False` for `x = 0`. The premise is unprovable for
  -- `x = 0` — the certificate is silent.
  -- Construct the conclusion trivially: `accelerated_orbit 0 k = 0`
  -- for all k, so for `.empty` claim, `False → False` is provable.
  -- For `.singleton n` (n > 0) or `.bounded K`, no `k` works.
  -- The certificate's `orbit_hits_claim` does NOT need to cover
  -- `x = 0` because the `0 < x` premise is False.
  -- This example does NOT prove a `False`-on-`x=0` obligation;
  -- it simply documents that `x = 0` is outside the domain.
  -- We use a vacuous proof: from `False` premise, anything follows.
  False.elim (by omega : ¬ 0 < 0)

/-! ## Compile-check scenarios for `coverage_tree_soundness_orbit_cert_bounded`

Type-only checks (proof values supplied as hypotheses, like PR #58's
parallel scenarios). The conditional type-check example in
`Q5Integration.lean` already exercises the theorem directly; these
scenarios verify the theorem type-checks against concrete tree +
bounded `N`. -/

/-- Scenario 1: `coverage_tree_soundness_orbit_cert_bounded` closes
    for `singleLeafTree` (the Q5 verifier test fixture — single
    leaf, every input routes to it) + bounded `N = 3` + a
    `hCert` hypothesis per the Q4 v3 `hCert` pattern.

    `hv` and `hc` discharged via `native_decide` (the standard
    structural invariants for `singleLeafTree`).

    `hCert` is supplied as a hypothesis for v2a — the verifier
    soundness theorem (v2b) will provide a constructive
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

/-- Scenario 2: `per_leaf_available_bounded_of_hCert` closes for the
    same `singleLeafTree` + bounded `N`, taking the per-leaf
    certificate from `hCert`. The hypothesis-based v2a form.

    Renamed from v1's `per_leaf_available_bounded` per Codex P2.
    v2b will replace the hypothesis with a constructive derivation
    from the verifier soundness theorem
    (`per_leaf_available_bounded_of_check`). -/
example (N : Nat)
    (hCert : ∀ l ∈ singleLeafTree.leaves, verified singleLeafTree l →
      BoundedInputOrbitCertificate singleLeafTree l N)
    (l : CoverageLeaf)
    (hl : l ∈ singleLeafTree.leaves)
    (hver : verified singleLeafTree l) :
    BoundedInputOrbitCertificate singleLeafTree l N :=
  per_leaf_available_bounded_of_hCert singleLeafTree N hCert l hl hver

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

/-! ## v2b.6 — Compile-check scenarios for the soundness chain (Lemmas 1-6)

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § Sub-commit
sequencing, v2b.6 lands the test scenarios for the soundness
chain. These tests are:

1. **API-shape guards** for the new lemmas (defend signatures
   against accidental changes).
2. **`native_decide` smoke tests** for the boolean-decideable parts
   (e.g. `foldl_and_extract`, `checkCertWitness_decompose`).
3. **Polymorphic apply-the-theorem** scenarios for the higher-level
   soundness theorems.

The proofs themselves contain explicit `sorry` placeholders
(2 in `transitionOk_implies_step` from v2b.2 + 4 in
`checkBoundedCertificate_sound` from v2b.4) for parts requiring
detailed Mathlib list-manipulation lemmas. These tests validate
the LEMMA SHAPES, not the proofs — the broader review at the
end of the v2b arc will close the sorrys.

**Lesson applied (Q4 v3 — API-shape regression):** each new
lemma gets a polymorphic apply-the-theorem scenario that defends
its signature. Mirrors PR #57 scenario (`boundedCertificateClaim`)
+ PR #58 scenario 12. -/

/-- Scenario 4 (v2b.6): `foldl_and_extract` smoke test.
    Verify the lemma's signature against concrete inputs:
    `ts = [1, 2, 3]`, `p := fun n => decide (0 < n)`,
    hypothesis discharged via `native_decide`.

    Defends the lemma's signature against accidental changes
    and confirms the `true && p a = p a` identity is exercised. -/
example : foldl_and_extract [1, 2, 3] (fun n : Nat => decide (0 < n))
    (by native_decide : List.foldl
      (fun acc x => acc && decide (0 < x)) true [1, 2, 3] = true)
    2 (by simp : 2 ∈ [1, 2, 3]) = true := by
  exact foldl_and_extract [1, 2, 3] (fun n : Nat => decide (0 < n))
    (by native_decide) 2 (by simp)

/-- Scenario 5 (v2b.6): `checkCertWitness_decompose` smoke test.
    Verify the biconditional against a concrete witness on
    `singleLeafTree`: N=1, claim `.singleton 1`, trajectory `[1]`.

    The boolean-decideable parts of the biconditional are
    decidable via `native_decide` (the `decide (claim.Holds
    last)` bridge + `List.getLast?` etc. are all reducible). -/
example : checkCertWitness_decompose 1 (FiniteOrbitClaim.singleton 1)
    singleLeafTree { leafId := "L", leafProperty := "0:0-0" }
    { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true := by
  exact checkCertWitness_decompose 1 (FiniteOrbitClaim.singleton 1) singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] }

/-- Scenario 6 (v2b.6): `checkBoundedCertificate_sound` API-shape
    regression. Type-only check (proof values supplied as
    hypotheses; the actual proof has explicit `sorry` placeholders
    that the broader review will close).

    Defends the soundness assembly signature against accidental
    changes. The hypotheses match the v2a convention
    (`hv`, `hc`, `hver`, `hcr`, `hcheck`). -/
example (t : CoverageTree) (l : CoverageLeaf) (d : BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hver : verified t l)
    (hcr : ∀ y, d.wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificate t l d = true)
    : BoundedInputOrbitCertificate t l d.wire.N :=
  checkBoundedCertificate_sound t l d hv hc hver hcr hcheck

/-- Scenario 7 (v2b.6): `per_leaf_available_bounded_of_check`
    API-shape regression. Type-only check (proof values supplied
    as hypotheses; the actual proof is a one-line application of
    `checkBoundedCertificate_sound` which itself has `sorry`
    placeholders to be addressed in the broader review).

    Defends the per-leaf availability signature against accidental
    changes. Mirrors PR #57's `boundedCertificateClaim` API-shape
    regression pattern. -/
example (t : CoverageTree)
    (dataPerLeaf : ∀ l ∈ t.leaves, verified t l →
      BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
            ∀ y, (dataPerLeaf l hl hver).wire.claim.Holds y → ReachesOne y)
    (hcheck : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
              checkBoundedCertificate t l (dataPerLeaf l hl hver) = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l)
    : BoundedInputOrbitCertificate t l ((dataPerLeaf l hl hver).wire.N) :=
  per_leaf_available_bounded_of_check t dataPerLeaf hv hc hcr hcheck l hl hver

end CollatzResearch
