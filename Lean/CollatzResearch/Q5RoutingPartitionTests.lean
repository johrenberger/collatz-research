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

end CollatzResearch
