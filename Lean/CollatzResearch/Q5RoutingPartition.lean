/-
Q5-RP-4 — kernel-checked acceptance facts for global routing partitions.

This module proves only what the executable routing-partition checker accepted:
each canonical slot was checked, and each accepted witness has a registered
claim, a canonical head, accepted routing, terminal, and transition facts.
It deliberately does not compose a claim with `ReachesOne`, and does not
construct a legacy single-leaf certificate.  Those are Q5-RP-5 work.
-/

import CollatzResearch.Q5Integration

namespace CollatzResearch

/-! ## Boolean fold extraction -/

/-- Generalized extraction from a Boolean conjunction fold.  The accumulator
invariant is required because, after consuming a head, the recursive fold
starts from `acc && p head`, not from `true`. -/
theorem routing_foldl_and_extract_aux {α : Type u} (xs : List α)
    (p : α → Bool) (acc : Bool)
    (h : List.foldl (fun a x => a && p x) acc xs = true) :
    acc = true ∧ ∀ x, x ∈ xs → p x = true := by
  induction xs generalizing acc with
  | nil =>
      refine ⟨?_, ?_⟩
      · simpa using h
      · intro x hx
        simp at hx
  | cons a rest ih =>
      rcases ih (acc && p a) h with ⟨hacc, hrest⟩
      rcases (Bool.and_eq_true_eq_eq_true_and_eq_true acc (p a)).mp hacc with
        ⟨ha, hpa⟩
      refine ⟨ha, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hxa | hxr
      · subst x
        exact hpa
      · exact hrest x hxr

/-- Extract a Boolean conjunct for an element of a fold. -/
theorem routing_foldl_and_extract {α : Type u} (xs : List α) (p : α → Bool)
    (h : List.foldl (fun a x => a && p x) true xs = true)
    (x : α) (hx : x ∈ xs) : p x = true :=
  (routing_foldl_and_extract_aux xs p true h).2 x hx

/-! ## Accepted canonical slots -/

/-- If the global checker accepts, its check for every canonical input slot
also accepts.  This is purely an extraction fact: it does not yet attach any
reachability semantics to the registered claim. -/
theorem checkRoutingPartitionCertificate_accepts_slot
    (t : CoverageTree) (d : RoutingPartitionCertificateData)
    (hcheck : checkRoutingPartitionCertificate t d = true)
    (i : Fin d.wire.N) :
    checkRoutingPartitionWitness t (i.val + 1) d.wire.claimRegistry
      (d.routingWitness i).val = true := by
  apply routing_foldl_and_extract (List.finRange d.wire.N)
    (fun j => checkRoutingPartitionWitness t (j.val + 1)
      d.wire.claimRegistry (d.routingWitness j).val) hcheck i
  simp

/-! ## Accepted witness decomposition -/

/-- An accepted routing-partition witness exposes the exact Boolean facts
checked by the executable verifier.  The terminal and transition facts are
kept in their executable forms here; Q5-RP-5 will transport them into the
explicit conditional reachability theorem. -/
theorem checkRoutingPartitionWitness_accepts
    (t : CoverageTree) (x : Nat) (registry : List LeafClaimWire)
    (w : RoutingWitnessWire)
    (hcheck : checkRoutingPartitionWitness t x registry w = true) :
    ∃ claim, findRoutingLeafClaim registry w.leaf = some claim ∧
      ∃ hd rest, w.trajectory = hd :: rest ∧ hd = x ∧
        routesToRoutingLeaf t x w.leaf = true ∧
        (match (hd :: rest).getLast? with
         | some last => decide (claim.Holds last)
         | none => false) = true ∧
        List.foldl (fun acc pair =>
          acc && pair.snd == acceleratedStep pair.fst) true
          (List.zip (hd :: rest) (hd :: rest).tail) = true := by
  unfold checkRoutingPartitionWitness at hcheck
  split at hcheck
  · rename_i hlookup
    simp at hcheck
  · rename_i claim hlookup
    refine ⟨claim, hlookup, ?_⟩
    cases htraj : w.trajectory with
    | nil =>
        simp [htraj] at hcheck
    | cons hd rest =>
        simp only [htraj, Bool.and_eq_true] at hcheck
        rcases hcheck with ⟨⟨⟨hhead, hroutes⟩, hterminal⟩, htransitions⟩
        have hhead' : hd = x := by simpa using hhead
        exact ⟨hd, rest, rfl, hhead', hroutes, hterminal,
          htransitions⟩

/-! ## Conditional reachability composition -/

/-- A checked trajectory reaches one when its terminal claim is explicitly
known to reach one.  The transition relation and claim-reachability premise
remain explicit: this theorem performs only the kernel-checked composition,
and does not construct a legacy single-leaf certificate. -/
theorem routing_trajectory_reaches_one
    (x : Nat) (w : CertWitness x) (claim : FiniteOrbitClaim)
    (hAnchor : anchorOk x w = true)
    (hTrans : ∀ i, i + 1 < w.trajectory.length →
      w.trajectory[i + 1]! = acceleratedStep w.trajectory[i]!)
    (hLast : claim.Holds (w.trajectory[w.trajectory.length - 1]!))
    (hClaimReachesOne : ∀ y, claim.Holds y → ReachesOne y) :
    ReachesOne x := by
  have hOrbitClaim :
      claim.Holds (accelerated_orbit x (w.trajectory.length - 1)) :=
    terminal_claim_transport x w claim hAnchor hTrans hLast
  exact orbit_predecessor_reaches_one x (w.trajectory.length - 1)
    (accelerated_orbit x (w.trajectory.length - 1)) rfl
    (hClaimReachesOne _ hOrbitClaim)

end CollatzResearch
