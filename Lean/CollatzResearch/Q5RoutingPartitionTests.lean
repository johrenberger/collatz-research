/- Q5-RP-4 — API-shape and accepted-slot regressions. -/

import CollatzResearch.Q5RoutingPartition
import CollatzResearch.Q5VerifierTests

namespace CollatzResearch

/-- Global acceptance exposes acceptance of each canonical slot. -/
example : checkRoutingPartitionWitness routingPartitionTwoLeafTree 1
    routingPartitionRegistry (twoLeafRoutingPartition.routingWitness ⟨0, by decide⟩).val = true :=
  checkRoutingPartitionCertificate_accepts_slot routingPartitionTwoLeafTree
    twoLeafRoutingPartition (by native_decide) ⟨0, by decide⟩

/-- Accepted witness decomposition preserves the canonical head and the
registered claim lookup for the odd leaf in the two-leaf fixture. -/
example : ∃ claim,
    findRoutingLeafClaim routingPartitionRegistry
      (twoLeafRoutingPartition.routingWitness ⟨0, by decide⟩).val.leaf = some claim ∧
    ∃ hd rest,
      (twoLeafRoutingPartition.routingWitness ⟨0, by decide⟩).val.trajectory = hd :: rest ∧
      hd = 1 ∧
      routesToRoutingLeaf routingPartitionTwoLeafTree 1
        (twoLeafRoutingPartition.routingWitness ⟨0, by decide⟩).val.leaf = true ∧
      (match (hd :: rest).getLast? with
       | some last => decide (claim.Holds last)
       | none => false) = true ∧
      List.foldl (fun acc pair => acc && pair.snd == acceleratedStep pair.fst)
        true (List.zip (hd :: rest) (hd :: rest).tail) = true :=
  checkRoutingPartitionWitness_accepts routingPartitionTwoLeafTree 1
    routingPartitionRegistry (twoLeafRoutingPartition.routingWitness ⟨0, by decide⟩).val
    (by native_decide)

/-- The RP-5 composition theorem closes a singleton terminal claim under its
explicit reachability obligation.  This exercises no global acceptance or
legacy certificate construction. -/
example : ReachesOne 1 := by
  let w : CertWitness 1 :=
    { l := { leafId := "L", leafProperty := "0:0-0" }, trajectory := [1] }
  apply routing_trajectory_reaches_one 1 w (FiniteOrbitClaim.singleton 1)
  · native_decide
  · intro i hi
    simp [w] at hi
  · simp [w, FiniteOrbitClaim.Holds]
  · intro y hy
    simp [FiniteOrbitClaim.Holds] at hy
    subst y
    exact ⟨0, by simp⟩

/-- Global acceptance composes with an explicit registry-wide reachability
assumption; this remains conditional and does not assert convergence of an
untrusted claim registry. -/
example (hClaimReachesOne : ∀ entry ∈ routingPartitionRegistry, ∀ y,
    entry.claim.Holds y → ReachesOne y) : ReachesOne 1 :=
  routing_partition_certificate_slot_reaches_one routingPartitionTwoLeafTree
    twoLeafRoutingPartition (by native_decide) hClaimReachesOne
    ⟨0, by decide⟩

/-- Soundness closure scenario (v2b'.4 — option-b single-leaf redesign
via routing partition): the routing-partition soundness theorem closes
ReachesOne for every canonical input slot 1..N, conditional on every
registered claim reaching 1.  This is the Q5-closure regression: the
soundness theorem (added in PR #74) is kernel-checked and proves the
batched per-slot reachability in a single shot via the per-slot helper.

    The proof supplies an explicit registry-wide reachability assumption
`hClaimReachesOne`; the theorem does not assert unconditional convergence
of an untrusted claim registry. -/
example (hClaimReachesOne : ∀ entry ∈ routingPartitionRegistry, ∀ y,
    entry.claim.Holds y → ReachesOne y) :
    ∀ (x : Nat), 0 < x → x ≤ twoLeafRoutingPartition.wire.N → ReachesOne x :=
  RoutingPartitionCertificate_sound routingPartitionTwoLeafTree
    twoLeafRoutingPartition (by native_decide) hClaimReachesOne

/-- Wrong-route witness regression (v2b'.4): a witness can name a
registered leaf and still be rejected when it is not the leaf recomputed by
`descendOrbit` for its canonical input.  Mirrors the same-name rejection
behavior as the per-leaf `BoundedInputCertificateData` checker. -/
example : ¬ checkRoutingPartitionWitness routingPartitionTwoLeafTree 1
    routingPartitionRegistry
      { leaf := { leafId := "even", leafProperty := "2:0-0" },
        trajectory := [1] } = true := by
  native_decide

/-- Empty-registry lookup regression (v2b'.4): a missing registry entry is
reported as `none` by the executable lookup.  Mirrors `findRoutingLeafClaim`
rejection for empty registry. -/
example : findRoutingLeafClaim []
    { leafId := "odd", leafProperty := "2:1-1" } = none := by
  native_decide

/-- Empty trajectory regression (v2b'.4): a witness with empty trajectory
is rejected (the witness must have a nonempty trajectory with a head
matching the canonical input).  Mirrors the empty-trajectory rejection in
the per-leaf checker. -/
example : ¬ checkRoutingPartitionWitness routingPartitionTwoLeafTree 1
    routingPartitionRegistry
      { leaf := { leafId := "odd", leafProperty := "2:1-1" }, trajectory := [] } = true := by
  native_decide

/-- Head-mismatch regression (v2b'.4): a witness whose trajectory head does
not equal the canonical input is rejected.  Mirrors the head-mismatch
rejection in the per-leaf checker. -/
example : ¬ checkRoutingPartitionWitness routingPartitionTwoLeafTree 1
    routingPartitionRegistry
      { leaf := { leafId := "odd", leafProperty := "2:1-1" }, trajectory := [2] } = true := by
  native_decide

/-- Multi-leaf routing positive regression (v2b'.4): global acceptance
verifies the full bounded domain across multiple leaves with correct
per-leaf routing.  Mirrors PR #62 scenario A (positive multi-leaf
routing-partition). -/
example : checkRoutingPartitionCertificate routingPartitionTwoLeafTree
    twoLeafRoutingPartition = true := by
  native_decide

end CollatzResearch
