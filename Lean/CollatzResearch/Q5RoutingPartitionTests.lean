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

end CollatzResearch
