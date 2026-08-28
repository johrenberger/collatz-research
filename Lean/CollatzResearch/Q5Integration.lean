/-
Q5 PR #4 — integration of the Lean verifier + bounded-input companion
theorem (Q5 v5 spec § 4.3.1a, § 4.3.2, § 4.4).

The Q5 4-PR split places:
- PR #61 (merged at `1fa90bd`): Q5 spec.
- PR #62 (merged at `5215fd1`): `BoundedInputCertificateWire` +
  `BoundedInputCertificateData` + `checkBoundedCertificate` Bool
  verifier. **In-memory wire model + structural validation.**
- PR #63 (merged at `18a948e`): Python external generator +
  hand-rolled JSON parser + parser-rejection tests.
  **Producer + parser-side boundary; producer is UNTRUSTED.**
- PR #4 (THIS FILE): integration.

## Trust boundary (Q5 v5 spec § 3)

```
Python serialized evidence → (PR #63 parser)
                            → BoundedInputCertificateWire
                            → decodeBoundedInputCertificateData (PR #62)
                            → BoundedInputCertificateData
                            → checkBoundedCertificate (PR #62)
                            → Bool verifier (PR #4 soundness — v2)
                            → BoundedInputOrbitCertificate (this PR)
                            → coverage_tree_soundness_orbit_cert_bounded (this PR)
                            → ∀ x ≤ N, ReachesOne x
```

Producer + parser are UNTRUSTED. Only the Lean verifier + soundness
theorem + companion theorem enter the TCB.

## v1 scope (this PR)

- `BoundedInputOrbitCertificate` structure (mirror of Q4 v3
  `BoundedOrbitCertificate` with explicit `N : Nat` input bound).
- `coverage_tree_soundness_orbit_cert_bounded` (parallel bounded
  companion theorem mirroring PR #58's unbounded
  `coverage_tree_soundness_orbit_cert`).
- `per_leaf_available_bounded` (per-leaf availability pattern;
  hypothesis-based for v1, taking the per-leaf certificates as
  input — to be wired to the verifier soundness theorem in v2).
- Closed-form example for `depthTwoTree` (the concrete tree scope
  per Q5 spec § 4.5).
- Tests in `Q5IntegrationTests.lean`.

## v2 scope (deferred)

- `checkBoundedCertificate_sound` (the verifier soundness theorem).
  Connects `checkBoundedCertificate = true` to
  `BoundedInputOrbitCertificate`. Substantial proof (extracts per-witness
  check from `List.foldl`, applies the trajectory-indexing lemma, etc.).
  Will be PR #4 v2 in a follow-up commit.

## Lessons applied (Q3 v4 + Q4 v3 + META)

- **Pattern 2.10** (conditional companion theorem pattern): explicit
  `hCert` hypothesis preserved on `coverage_tree_soundness_orbit_cert_bounded`.
- **Q4 lessons (`: Type` sort)**: `BoundedInputOrbitCertificate` is
  `: Type`-valued (data + proof fields). NO `Prop`-valued sort
  conflict.
- **META § 3.2** (per-leaf availability): `per_leaf_available_bounded`
  implements the per-leaf pattern explicitly.
- **META § 3.3** (avoid universal acceptance): the closed-form
  example is scoped to `depthTwoTree` + bounded `N`; the
  universal-`∀ t` claim stays conditional.

Story Q5 / PR #4 v1 (integration — bounded-input certificate type +
bounded companion theorem + per-leaf availability + closed-form example
for `depthTwoTree`; verifier soundness theorem deferred to v2). -/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## Bounded-input orbit-routing certificate (Q5 v5 spec § 4.3.2)

Mirror of Q4 v3 `BoundedOrbitCertificate` (PR #57) with an explicit
`N : Nat` bound on the input domain. The two structures coexist:

- `BoundedOrbitCertificate` (PR #57, master): formal type,
  hypothesis-bearing — the unconditional orbit-routing claim over
  all `x`.
- `BoundedInputOrbitCertificate` (Q5, NEW): constructible type with
  bounded quantifier — proves the orbit-routing claim for
  `1 ≤ x ≤ N`.

The bound `N` is the input domain cap: the certificate is meaningful
for inputs `x ∈ {1, ..., N}`. For `x ≤ 0` or `x > N`, the
certificate is silent (matches the Q5 v5 spec: bounded end-to-end,
no conversion to unbounded `BoundedOrbitCertificate`). -/

/-- Bounded-input orbit-routing certificate for a leaf `l` in tree
    `t`, with explicit `N : Nat` bound on the input domain.

    Two obligation fields, both `Prop`-valued (kernel-checked):
    1. `orbit_hits_claim : ∀ x, x ≤ N → descendOrbit t x 0 = some l →
       ∃ k, claim.Holds (accelerated_orbit x k)` — every input
       `x ≤ N` routed (orbit-aware) to `l` reaches a claim.Holds
       orbit state.
    2. `claim_reaches_one : ∀ y, claim.Holds y → ReachesOne y` —
       every claim-target state reaches 1.

    `: Type`-valued proof-carrying data bundle (NOT `: Prop`): the
    `claim : FiniteOrbitClaim` data field requires `Type`-valued
    sort per Q3 v4 lessons (Lean 4 elaboration rejects `Type`-valued
    fields in `: Prop` structures).

    Companion to `BoundedOrbitCertificate` (Q4 v3, PR #57). NO mutual
    exclusion — a leaf can carry both `BoundedOrbitCertificate t l`
    (Q4 v3, hypothesis-bearing) and `BoundedInputOrbitCertificate t
    l N` (Q5 NEW, bounded) as independent views of its semantic
    content. They conclude different leaf-level predicates (via the
    companion theorems) and certify the same routing relation
    (`descendOrbit`) under different input-domain scopes.

    Inserted after `BoundedOrbitCertificate` (Q4 v3, PR #57) so the
    two can be compared side-by-side.

    API-shape regression: `def boundedInputOrbitCertShape` at the
    end of `Q5IntegrationTests.lean` (mirrors PR #57's
    `boundedCertificateClaim`). -/
structure BoundedInputOrbitCertificate (t : CoverageTree) (l : CoverageLeaf)
    (N : Nat) : Type where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, x ≤ N → descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y

/-! ## Bounded-input companion theorem (Q5 v5 spec § 4.4)

Parallel of PR #58's `coverage_tree_soundness_orbit_cert` with the
additional `N : Nat` bound on the input domain. The conclusion is
`ReachesOne x` (NOT `OrbitLeafReachesOne t l`, which is the
unbounded Q4 v3 form): for `1 ≤ x ≤ N`, `x` reaches 1.

The proof mirrors PR #58:
1. Apply `descend_orbit_complete` (PR #29) for orbit-aware routing.
2. Apply `BoundedInputOrbitCertificate.orbit_hits_claim` to get a
   `k` with `claim.Holds (accelerated_orbit x k)`.
3. Apply `BoundedInputOrbitCertificate.claim_reaches_one` to get
   `ReachesOne (accelerated_orbit x k)`.
4. Apply `orbit_predecessor_reaches_one` (PR #56) to close:
   `ReachesOne (accelerated_orbit x k) → ReachesOne x`.

The `hN : x ≤ N` hypothesis is the only addition to the PR #58
statement. The `hCert` hypothesis uses `BoundedInputOrbitCertificate`
(the bounded type) rather than `BoundedOrbitCertificate` (the
unbounded type) — explicit per META § 3.3 (avoid universal
acceptance). -/

/-- Bounded-input parallel of `coverage_tree_soundness_orbit_cert`
    (PR #58, Q4 v3). For each positive input `x ≤ N` routed to a
    leaf with a `BoundedInputOrbitCertificate`, `ReachesOne x`.

    The bound `N` is the input domain cap; for `x > N`, the theorem
    is silent (matches Q5 v5 spec § 4.5: bounded end-to-end).

    **Proof status: structurally proved** (mirrors PR #58 proof;
    uses `descend_orbit_complete` + `orbit_predecessor_reaches_one`
    + the bounded certificate's `orbit_hits_claim` /
    `claim_reaches_one`). -/
theorem coverage_tree_soundness_orbit_cert_bounded
    (t : CoverageTree)
    (N : Nat)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l →
      BoundedInputOrbitCertificate t l N)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         ReachesOne x := by
  obtain ⟨l, hl, hver, hdesc, hroute⟩ := descend_orbit_complete t hv hic x hx
  obtain cert := hCert l hl hver
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x hN hdesc
  exact ⟨l, hl, hver, hdesc,
    orbit_predecessor_reaches_one x k (accelerated_orbit x k) rfl
      (cert.claim_reaches_one (accelerated_orbit x k) hk)⟩

/-! ## Per-leaf availability pattern (Q5 v5 spec § 4.4)

`per_leaf_available_bounded` is the per-leaf availability pattern
that connects per-leaf `BoundedInputCertificateData` to per-leaf
`BoundedInputOrbitCertificate`. For v1, this is stated with the
per-leaf certificate as a HYPOTHESIS (parallel to PR #58's `hCert`
pattern). The v2 soundness theorem
(`checkBoundedCertificate_sound`) will provide a constructive
implementation that closes `per_leaf_available_bounded` from
verifier evidence.

For PR #4 v1, the closed-form example (next) uses `hCert` directly.
The v2 soundness theorem will enable the dataset-to-certificate
construction. -/

/-- Per-leaf availability pattern: for each verified leaf `l`, the
    per-leaf certificate (`BoundedInputOrbitCertificate t l N`) is
    available.

    **v1 form**: takes the per-leaf certificate as a hypothesis
    (mirrors the Q4 v3 `coverage_tree_soundness_orbit_cert` `hCert`
    pattern). v2 will replace the hypothesis with constructive
    verifier-soundness-derivation. -/
theorem per_leaf_available_bounded
    (t : CoverageTree)
    (N : Nat)
    (hCert : ∀ l ∈ t.leaves, verified t l →
      BoundedInputOrbitCertificate t l N)
    (l : CoverageLeaf)
    (hl : l ∈ t.leaves)
    (hver : verified t l) :
    BoundedInputOrbitCertificate t l N :=
  hCert l hl hver

/-! ## Closed-form example for `depthTwoTree`

The concrete tree scope per Q5 v5 spec § 4.5. Composes the bounded
companion theorem with the per-leaf availability pattern.

For PR #4 v1, the example takes `hCert` as a hypothesis (per Q4 v3
pattern). v2 will provide a constructive example using the verifier
soundness theorem. -/

/-- Closed-form example for `depthTwoTree` + bounded input domain.

    Demonstrates the type-check that
    `coverage_tree_soundness_orbit_cert_bounded` closes for the
    concrete tree + a hypothetical per-leaf certificate dataset.

    `hv : ValidTree depthTwoTree` and `hc : IsComplete depthTwoTree`
    are discharged via `native_decide` (the standard depthTwoTree
    structural invariants; see `CoverageTreeOrbitTests.lean` for
    the underlying defs).

    `hCert` is the per-leaf certificate dataset (hypothesis for v1;
    will be constructed from the verifier soundness theorem in v2).

    The conclusion: for each positive `x ≤ N`, `x` reaches 1.
    Bounded end-to-end per Q5 v5 spec. -/
example (N : Nat)
    (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
      BoundedInputOrbitCertificate depthTwoTree l N)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree x 0 = some l ∧
         ReachesOne x :=
  coverage_tree_soundness_orbit_cert_bounded depthTwoTree N hv hc hCert x hx hN

end CollatzResearch
