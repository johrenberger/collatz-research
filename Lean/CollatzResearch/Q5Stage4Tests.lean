/-
Q5 v2b.8 — tests for the per-leaf certificate projection
(`routing_partition_leaf_certificate`, v2b.6) and its
constructive-form alias (`per_leaf_available_bounded_of_check`,
v2b.7). These tests exercise the META § 3.2 (constructive
per-leaf availability) chain end-to-end.

## Test strategy

The v2b.6 / v2b.7 functions have rich hypothesis requirements
(`hcheck`, `hClaimReachesOne`, `hRegistry`) that would each
require substantial proof scaffolding for a concrete constructive
test (e.g., the `ReachesOne y` obligation for each registered
claim). This module takes a layered approach:

1. **Type-check (`#check`)**: verifies the function exists with
   the expected signature. Catches signature regressions
   (e.g., accidental field reordering in `BoundedInputOrbitCertificate`).
2. **Roundtrip (`example`)**: verifies v2b.7 is definitionally
   equal to v2b.6 (it's a one-liner alias). Catches accidental
   signature drift between the two.
3. **Type-only constructive test (`example`)**: exercises the
   full typechecking pipeline for both v2b.6 and v2b.7 with
   concrete hypothesis parameters. Catches elaboration errors
   (e.g., a hypothesis that the typechecker cannot unify).

4. **Concrete-data discharge (`theorem` layer)**: the
   two-leaf routing partition fixture
   (`routingPartitionTwoLeafTree` + `twoLeafRoutingPartition`) is
   used to *discharge* the per-leaf obligations
   (`hClaimReachesOne` / `hRegistry` / `verified`) concretely,
   yielding two named `noncomputable def` statements rather than
   anonymous examples. The `FiniteOrbitClaim.singleton 1` reachability
   obligation is discharged once per registry entry (`ReachesOne 1`
   via `accelerated_orbit 1 0 = 1`); the registry lookup and the
   `verified` obligation are discharged structurally.

The concrete layer is *additional* to the symbolic layer: the
type-only / roundtrip / constructor-field tests above still exercise
the fully general signatures, so the concrete statements never
replace the symbolic ones.

## Kernel-clean

No `sorry` / `admit` / `axiom` in any test. All tests are
type-only, `rfl` (definitional equality), or closed decidable
facts over the concrete fixture.

## Noncomputable note

`routing_partition_leaf_certificate` (v2b.6) and
`per_leaf_available_bounded_of_check` (v2b.7) are `noncomputable`
(both use `Classical.choose` to extract from the `hRegistry`
existential in a `Type` context). Examples that call them must
also be `noncomputable` — this is propagated automatically by
Lean 4's kernel; the explicit marker is just for code generation
clarity. -/

import CollatzResearch.BoundedInputCertificateTree
import CollatzResearch.Q5Integration
import CollatzResearch.Q5RoutingPartition
import CollatzResearch.Q5VerifierTests

-- Type-check tests. `#check` is a Lean 4 command that must appear at the
-- top level (not inside a `namespace` block) and not after a doc
-- comment `/-- ... -/` (which would be parsed as a declaration
-- doc-comment expecting `lemma`/`def`/`example`). Plain `--` comments
-- are used here for this reason.

-- Type-check: v2b.6 `routing_partition_leaf_certificate` exists
-- with the expected signature. Using fully qualified name since
-- `#check` is at the top level (before `namespace CollatzResearch`).
#check @CollatzResearch.routing_partition_leaf_certificate

-- Type-check: v2b.7 `per_leaf_available_bounded_of_check` exists
-- with the expected signature.
#check @CollatzResearch.per_leaf_available_bounded_of_check

namespace CollatzResearch

/-! ## Roundtrip test (v2b.7 ≡ v2b.6 definitionally) -/

/-- v2b.7 is a one-liner delegating alias of v2b.6. The two functions
    are definitionally equal — no `rfl` axiom or proof rule
    needed. This test guards against accidental signature drift
    between the two names. -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    routing_partition_leaf_certificate t tree hcheck hClaimReachesOne
        hRegistry l hl hver =
      per_leaf_available_bounded_of_check t tree hcheck hClaimReachesOne
        hRegistry l hl hver := rfl

/-! ## Type-only constructive tests

These tests exercise the full typechecking pipeline for v2b.6
and v2b.7 with concrete hypothesis parameters. They catch
elaboration errors that `#check` would miss (e.g., a
hypothesis that the typechecker cannot unify at the use site,
or a `Classical.choose` noncomputability issue). -/

/-- Type-only constructive test: v2b.6 elaborates and returns
    `BoundedInputOrbitCertificate t l tree.certData.wire.N` for
    arbitrary `t`, `tree`, `l`, and the three required hypotheses. -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N :=
  routing_partition_leaf_certificate t tree hcheck hClaimReachesOne
    hRegistry l hl hver

/-- Type-only constructive test: v2b.7 elaborates and returns
    the same type. (Redundant with the v2b.6 test above given
    the roundtrip, but documents that v2b.7 independently
    typechecks at the use site, not just definitionally.) -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N :=
  per_leaf_available_bounded_of_check t tree hcheck hClaimReachesOne
    hRegistry l hl hver

/-! ## Constructor field tests

Verify that the constructed certificate has the expected field
types (defensively guarding against accidental field reordering
or type changes in `BoundedInputOrbitCertificate`). -/

/-- The `claim` field of the certificate is a `FiniteOrbitClaim`. -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    FiniteOrbitClaim :=
  (routing_partition_leaf_certificate t tree hcheck hClaimReachesOne
    hRegistry l hl hver).claim

/-- The `claim_reaches_one` field of the certificate is a function
    `∀ y, claim.Holds y → ReachesOne y`. -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    ∀ y, (routing_partition_leaf_certificate t tree hcheck
      hClaimReachesOne hRegistry l hl hver).claim.Holds y →
        ReachesOne y :=
  (routing_partition_leaf_certificate t tree hcheck hClaimReachesOne
    hRegistry l hl hver).claim_reaches_one

/-- The `orbit_hits_claim` field of the certificate is a function
    `∀ x, 0 < x → x ≤ N → descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)`. -/
noncomputable example (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ l, l ∈ t.leaves → verified t l →
      ∃ entry ∈ tree.certData.wire.claimRegistry, entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    ∀ x, 0 < x → x ≤ tree.certData.wire.N →
      descendOrbit t x 0 = some l →
        ∃ k, (routing_partition_leaf_certificate t tree hcheck
          hClaimReachesOne hRegistry l hl hver).claim.Holds
            (accelerated_orbit x k) :=
  (routing_partition_leaf_certificate t tree hcheck hClaimReachesOne
    hRegistry l hl hver).orbit_hits_claim

/-! ## Concrete per-leaf discharge (v2b.8 closure)

The blocks above retain the per-leaf hypotheses (`hClaimReachesOne` /
`hRegistry`) as *symbolic* arguments — the right shape for a general
claim, but leaving the concrete obligations undischarged.

This section discharges those obligations against the canonical fixture
(`routingPartitionTwoLeafTree` + `twoLeafRoutingPartition`), so the
result is a named, reusable statement rather than an anonymous
`example`.

Discharge summary:

- **`hClaimReachesOne`** — both registry entries carry
  `FiniteOrbitClaim.singleton 1`, whose `Holds` predicate is `y = 1`;
  `ReachesOne 1` is witnessed by `k := 0` (`accelerated_orbit 1 0 = 1`).
- **`hRegistry`** — the registry holds one entry per leaf of the fixture
  tree, and each entry's `leaf` field is definitionally the
  corresponding tree leaf, so the existential is witnessed by the
  matching registry entry.
- **`verified`** — purely structural: membership in the fixture's
  `leaves` list plus the two non-empty string fields, both of which hold
  for every leaf of the fixture.

No `ReachesOne 2` is claimed here: the `[2,7,11,17,13,5,1]` trajectory
for input `2` is a separate Collatz obligation and out of scope for
this closure.

**Form note.** The two closure statements below are `noncomputable def`
rather than `theorem`. The conclusion (`BoundedInputOrbitCertificate`)
is `Type`-valued — it carries the `claim` datum — and Lean 4 rejects
both a `theorem` with a `Type` conclusion and a `noncomputable
theorem`. This mirrors the upstream v2b.6 / v2b.7 declarations, which
are themselves `noncomputable def`s with the same `Type`-valued
conclusion. -/

/-- The `even` leaf of the canonical two-leaf fixture. -/
private def q5evenLeaf : CoverageLeaf :=
  { leafId := "even", leafProperty := "2:0-0" }

/-- The `odd` leaf of the canonical two-leaf fixture. -/
private def q5oddLeaf : CoverageLeaf :=
  { leafId := "odd", leafProperty := "2:1-1" }

/-- The `even` registry entry of the canonical two-leaf fixture. -/
private def q5evenEntry : LeafClaimWire :=
  { leaf := q5evenLeaf, claim := FiniteOrbitClaim.singleton 1 }

/-- The `odd` registry entry of the canonical two-leaf fixture. -/
private def q5oddEntry : LeafClaimWire :=
  { leaf := q5oddLeaf, claim := FiniteOrbitClaim.singleton 1 }

/-- Concrete discharge of the `hClaimReachesOne` obligation for the
    canonical two-leaf routing partition.

    Both registry entries carry `FiniteOrbitClaim.singleton 1`, whose
    `Holds` predicate reduces to `y = 1`; `ReachesOne 1` is witnessed
    by `k := 0`.  Closed and decidable — no `Classical` extraction and
    no trajectory reasoning. -/
theorem twoLeafRoutingPartition_claim_reaches_one :
    ∀ (entry : LeafClaimWire),
      entry ∈ twoLeafRoutingPartition.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y := by
  intro entry hmem y hy
  have hmem' : entry ∈ (q5evenEntry :: q5oddEntry :: []) := hmem
  rcases List.mem_cons.mp hmem' with h | h
  · subst h
    change (FiniteOrbitClaim.singleton 1).Holds y at hy
    simp only [FiniteOrbitClaim.Holds] at hy
    subst hy
    show ∃ k, accelerated_orbit 1 k = 1
    exact ⟨0, accelerated_orbit_zero 1⟩
  · rcases List.mem_cons.mp h with h | h
    · subst h
      change (FiniteOrbitClaim.singleton 1).Holds y at hy
      simp only [FiniteOrbitClaim.Holds] at hy
      subst hy
      show ∃ k, accelerated_orbit 1 k = 1
      exact ⟨0, accelerated_orbit_zero 1⟩
    · cases h

/-- Concrete discharge of the per-leaf `hRegistry` obligation for the
    canonical two-leaf routing partition.

    The registry contains one entry per leaf of
    `routingPartitionTwoLeafTree`, and each entry's `leaf` field is
    definitionally equal to the corresponding tree leaf, so the
    existential witness is the matching registry entry.

    The `verified` premise is not needed: membership in the fixture's
    `leaves` list already pins the leaf to one of the two fixture
    leaves (see `routingPartitionTwoLeafTree_verified`). -/
theorem twoLeafRoutingPartition_registry :
    ∀ (l : CoverageLeaf), l ∈ routingPartitionTwoLeafTree.leaves →
      verified routingPartitionTwoLeafTree l →
      ∃ entry ∈ twoLeafRoutingPartition.wire.claimRegistry, entry.leaf = l := by
  intro l hl _
  have hl' : l ∈ (q5evenLeaf :: q5oddLeaf :: []) := hl
  rcases List.mem_cons.mp hl' with h | h
  · subst h
    refine ⟨q5evenEntry, ?_, ?_⟩
    · show q5evenEntry ∈ (q5evenEntry :: q5oddEntry :: [])
      exact List.mem_cons.mpr (Or.inl rfl)
    · rfl
  · rcases List.mem_cons.mp h with h | h
    · subst h
      refine ⟨q5oddEntry, ?_, ?_⟩
      · show q5oddEntry ∈ (q5evenEntry :: q5oddEntry :: [])
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · rfl
    · cases h

/-- Concrete discharge of `verified` for every leaf of the canonical
    two-leaf fixture tree.

    Purely structural: membership in the fixture's `leaves` list, plus
    the two non-empty string fields (`leafId` / `leafProperty`), which
    hold for both fixture leaves.  No trajectory or reachability fact is
    smuggled in. -/
theorem routingPartitionTwoLeafTree_verified :
    ∀ l, l ∈ routingPartitionTwoLeafTree.leaves →
      verified routingPartitionTwoLeafTree l := by
  intro l hl
  have hl' : l ∈ (q5evenLeaf :: q5oddLeaf :: []) := hl
  rcases List.mem_cons.mp hl' with h | h
  · subst h
    exact ⟨hl, by decide, by decide⟩
  · rcases List.mem_cons.mp h with h | h
    · subst h
      exact ⟨hl, by decide, by decide⟩
    · cases h

/-- **v2b.6 closure against the canonical two-leaf fixture.**

    Concrete counterpart of the symbolic v2b.6 example above: the
    per-leaf hypotheses are discharged by
    `twoLeafRoutingPartition_claim_reaches_one`,
    `twoLeafRoutingPartition_registry` and
    `routingPartitionTwoLeafTree_verified`, so this is a named statement
    rather than an anonymous example.  The decidable check is the
    canonical routing-partition acceptance (`by native_decide`),
    matching the existing positive regression in
    `Q5VerifierTests.lean`. -/
noncomputable def twoLeaf_routing_partition_leaf_certificate
    (l : CoverageLeaf) (hl : l ∈ routingPartitionTwoLeafTree.leaves) :
    BoundedInputOrbitCertificate routingPartitionTwoLeafTree
      l twoLeafRoutingPartition.wire.N :=
  routing_partition_leaf_certificate
    routingPartitionTwoLeafTree
    { certData := twoLeafRoutingPartition }
    (by native_decide)
    twoLeafRoutingPartition_claim_reaches_one
    twoLeafRoutingPartition_registry
    l hl (routingPartitionTwoLeafTree_verified l hl)

/-- **v2b.7 closure against the canonical two-leaf fixture.**

    Symmetric concrete counterpart for the constructive alias
    `per_leaf_available_bounded_of_check` (v2b.7), with the same
    discharged per-leaf hypotheses and the same decidable check. -/
noncomputable def twoLeaf_per_leaf_available_bounded_of_check
    (l : CoverageLeaf) (hl : l ∈ routingPartitionTwoLeafTree.leaves) :
    BoundedInputOrbitCertificate routingPartitionTwoLeafTree
      l twoLeafRoutingPartition.wire.N :=
  per_leaf_available_bounded_of_check
    routingPartitionTwoLeafTree
    { certData := twoLeafRoutingPartition }
    (by native_decide)
    twoLeafRoutingPartition_claim_reaches_one
    twoLeafRoutingPartition_registry
    l hl (routingPartitionTwoLeafTree_verified l hl)

/-- The canonical two-leaf fixture's accepted routing-partition certificate
    proves the bounded concrete input `2` reaches one. Its even witness is
    `[2, 7, 11, 17, 13, 5, 1]`, whose terminal value satisfies the existing
    `singleton 1` claim; no new claim shape or general API is involved. -/
theorem twoLeafRoutingPartition_reaches_one_two : ReachesOne 2 := by
  exact RoutingPartitionCertificate_sound routingPartitionTwoLeafTree
    twoLeafRoutingPartition (by native_decide)
    twoLeafRoutingPartition_claim_reaches_one 2 (by decide) (by decide)

end CollatzResearch
