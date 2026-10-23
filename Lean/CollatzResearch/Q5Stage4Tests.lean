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

Concrete constructive tests with the two-leaf routing partition
test data (`routingPartitionTwoLeafTree` +
`twoLeafRoutingPartition`) are deferred to a follow-up — they
require constructing `hClaimReachesOne` from the
`FiniteOrbitClaim.singleton 1` reachability obligation (one
`ReachesOne 1` proof per registry entry), which is non-trivial
and orthogonal to the v2b.6 / v2b.7 signature.

## Kernel-clean

No `sorry` / `admit` / `axiom` in any test. All tests are
type-only or `rfl` (definitional equality).

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

/-! ## Concrete-data test (v2b.6 + v2b.7)

Replaces the abstract `t : CoverageTree` from the type-only layer with the
actual `routingPartitionTwoLeafTree` fixture from `Q5VerifierTests.lean`.
This exercises v2b.6 + v2b.7 elaborating against:

- The canonical `BoundedInputCertificateTree` wrapper
  (`{ certData := twoLeafRoutingPartition }`),
- The canonical routing-partition check (`by native_decide`,
  matching the existing `RoutingPartitionCertificate_sound` example
  in `Q5RoutingPartitionTests.lean`).

The per-leaf hypotheses (`hClaimReachesOne` / `hRegistry` /
`hl` / `hver`) are retained symbolically per LEAN_PATTERNS.md P10
("retain a symbolic theorem for general claims"). Each is a
constructive obligation discharged independently by a downstream
caller; this test verifies that v2b.6 + v2b.7 typecheck and
elaborate against the canonical fixture + the decidable check. -/

noncomputable example
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ twoLeafRoutingPartition.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ (l : CoverageLeaf),
      l ∈ routingPartitionTwoLeafTree.leaves →
      verified routingPartitionTwoLeafTree l →
      ∃ entry ∈ twoLeafRoutingPartition.wire.claimRegistry,
        entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ routingPartitionTwoLeafTree.leaves)
    (hver : verified routingPartitionTwoLeafTree l) :
    BoundedInputOrbitCertificate routingPartitionTwoLeafTree
      l twoLeafRoutingPartition.wire.N :=
  per_leaf_available_bounded_of_check
    routingPartitionTwoLeafTree
    { certData := twoLeafRoutingPartition }
    (by native_decide)
    hClaimReachesOne
    hRegistry l hl hver

/-! ## Concrete-data test (v2b.6 via `routing_partition_leaf_certificate`)

Symmetric concrete-data elaboration test for v2b.6 (the parent's
`routing_partition_leaf_certificate` extraction). Same fixture,
same per-leaf hypotheses retained symbolically, same decidable
check.  Independent elaboration site from v2b.7 above: if the
v2b.6 extraction reuses the v2b.6 sub-proofs
(`registry_unique_of_pairwise_irrefl`,
`trajectory_anchor_orbit_step`, etc., kernel-clean in
`Q5Stage4Subproofs.lean`) then this test elaborates against the
same concrete data without touching the proof bodies. -/

noncomputable example
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ twoLeafRoutingPartition.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hRegistry : ∀ (l : CoverageLeaf),
      l ∈ routingPartitionTwoLeafTree.leaves →
      verified routingPartitionTwoLeafTree l →
      ∃ entry ∈ twoLeafRoutingPartition.wire.claimRegistry,
        entry.leaf = l)
    (l : CoverageLeaf) (hl : l ∈ routingPartitionTwoLeafTree.leaves)
    (hver : verified routingPartitionTwoLeafTree l) :
    BoundedInputOrbitCertificate routingPartitionTwoLeafTree
      l twoLeafRoutingPartition.wire.N :=
  routing_partition_leaf_certificate
    routingPartitionTwoLeafTree
    { certData := twoLeafRoutingPartition }
    (by native_decide)
    hClaimReachesOne
    hRegistry l hl hver

end CollatzResearch
