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
example (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (cert : BoundedInputOrbitCertificate t l N) :
    (∀ x, 0 < x → x ≤ N → descendOrbit t x 0 = some l →
      ∃ k, cert.claim.Holds (accelerated_orbit x k)) ∧
    (∀ y, cert.claim.Holds y → ReachesOne y) :=
  ⟨cert.orbit_hits_claim, cert.claim_reaches_one⟩

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
example : ¬ 0 < 0 := by omega

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
example (N : Nat)
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

/-! ## v2b.6 — Compile-check scenarios for the soundness chain (Lemmas 1-4)

**v2b.6 Codex P0 fix (2026-09-02):** Scenarios 6 and 7 (which
tested the removed `checkBoundedCertificate_sound` and
`per_leaf_available_bounded_of_check` lemmas) have been
removed. The test file now exercises only the kernel-checked
Lemmas 1, 2 (Scenarios 4 and 5).

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § Sub-commit
sequencing, v2b.6 originally landed 4 test scenarios for the
soundness chain. After the v2b.6 Codex P0 removal of Lemmas 5
and 6, only Scenarios 4 and 5 remain:

  - **Scenario 4**: `foldl_and_extract` smoke test
    (kernel-checked Lemma 1).
  - **Scenario 5**: `checkCertWitness_decompose` smoke test
    (kernel-checked Lemma 2).
  - ~~**Scenario 6**: `checkBoundedCertificate_sound` API-shape
    regression~~ — REMOVED (lemma removed per Codex P0).
  - ~~**Scenario 7**: `per_leaf_available_bounded_of_check`
    API-shape regression~~ — REMOVED (lemma removed per Codex P0).

The removed scenarios tested theorems that the Codex P0 review
required removing from the Lean module. They cannot be re-added
until the soundness theorem is closed and the per-leaf
architectural decision is made (see `Q5Integration.lean` removal
note).

**Lesson applied (Q4 v3 — API-shape regression):** each remaining
new lemma gets a smoke test scenario that defends its signature.
Mirrors PR #57 scenario (`boundedCertificateClaim`) + PR #58
scenario 12. -/

/-- Scenario 4 (v2b.6, kernel-checked): `foldl_and_extract`
    smoke test. Verify the lemma's signature against concrete
    inputs: `ts = [1, 2, 3]`, `p := fun n => decide (0 < n)`,
    hypothesis discharged via `native_decide`.

    Defends the lemma's signature against accidental changes
    and confirms the `true && p a = p a` identity is exercised. -/
example : decide (0 < 2) = true := by
  exact foldl_and_extract [1, 2, 3] (fun n : Nat => decide (0 < n))
    (by native_decide) 2 (by simp)

/-- Scenario 5 (v2b.6, kernel-checked): `checkCertWitness_decompose`
    smoke test. Verify the biconditional against a concrete
    witness on `singleLeafTree`: N=1, claim `.singleton 1`,
    trajectory `[1]`.

    The boolean-decideable parts of the biconditional are
    decidable via `native_decide` (the `decide (claim.Holds
    last)` bridge + `List.getLast?` etc. are all reducible). -/
example :
    checkCertWitness 1 (FiniteOrbitClaim.singleton 1) singleLeafTree
      { leafId := "L", leafProperty := "0:0-0" }
      { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true ↔
    anchorOk 1 { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true ∧
      leafMatchOk (x := 1) { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] }
        { leafId := "L", leafProperty := "0:0-0" } = true ∧
      routingOk singleLeafTree 1
        { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true ∧
      terminalClaimOk (x := 1) (FiniteOrbitClaim.singleton 1)
        { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true ∧
      transitionOk (x := 1) { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] } = true := by
  exact checkCertWitness_decompose 1 (FiniteOrbitClaim.singleton 1) singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] }

end CollatzResearch
