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

/-- An accepted transition fold supplies the adjacent accelerated-step
relation at every in-bounds trajectory index.  This uses indexed access to
the zipped trajectory and its tail, avoiding a fragile membership induction
over the implementation of `List.zip`. -/
theorem routing_transition_fold_step (xs : List Nat)
    (hfold : List.foldl (fun acc pair =>
      acc && pair.snd == acceleratedStep pair.fst) true
      (List.zip xs xs.tail) = true)
    (i : Nat) (hi : i + 1 < xs.length) :
    xs[i + 1]! = acceleratedStep xs[i]! := by
  have hzip : i < (List.zip xs xs.tail).length := by
    simp only [List.length_zip, List.length_tail]
    omega
  have hpair := routing_foldl_and_extract (List.zip xs xs.tail)
    (fun pair => pair.snd == acceleratedStep pair.fst) hfold
    (List.zip xs xs.tail)[i] (List.getElem_mem hzip)
  have hpair' : (List.zip xs xs.tail)[i].snd =
      acceleratedStep (List.zip xs xs.tail)[i].fst := by
    simpa using hpair
  rw [List.getElem_zip] at hpair'
  rw [List.getElem_tail] at hpair'
  simpa only [getElem!_pos xs (i + 1) hi,
    getElem!_pos xs i (Nat.lt_of_succ_lt hi)] using hpair'

/-- A successful registry lookup is backed by a concrete registry entry with
the returned claim. -/
theorem findRoutingLeafClaim_some (registry : List LeafClaimWire)
    (leaf : CoverageLeaf) (claim : FiniteOrbitClaim)
    (hfind : findRoutingLeafClaim registry leaf = some claim) :
    ∃ entry ∈ registry, entry.claim = claim ∧
      sameCoverageLeaf entry.leaf leaf = true := by
  induction registry with
  | nil => simp [findRoutingLeafClaim] at hfind
  | cons entry rest ih =>
      unfold findRoutingLeafClaim at hfind
      split at hfind
      · rename_i hsame
        simp at hfind
        subst claim
        exact ⟨entry, by simp, rfl, hsame⟩
      · rcases ih hfind with ⟨entry', hmem, hclaim, hsame⟩
        exact ⟨entry', List.mem_cons_of_mem _ hmem, hclaim, hsame⟩

/-- A Boolean-accepted routing witness reaches one when every registered
claim is explicitly known to reach one.  The theorem is conditional: it
does not assert convergence for unverified claims or unchecked witnesses. -/
theorem routing_partition_witness_reaches_one
    (t : CoverageTree) (x : Nat) (registry : List LeafClaimWire)
    (w : RoutingWitnessWire)
    (hcheck : checkRoutingPartitionWitness t x registry w = true)
    (hClaimReachesOne : ∀ entry ∈ registry, ∀ y,
      entry.claim.Holds y → ReachesOne y) :
    ReachesOne x := by
  rcases checkRoutingPartitionWitness_accepts t x registry w hcheck with
    ⟨claim, hfind, hd, rest, htraj, hhead, hroutes, hterminal, hfold⟩
  rcases findRoutingLeafClaim_some registry w.leaf claim hfind with
    ⟨entry, hentry, hclaim, _⟩
  let checked : CertWitness x := { l := w.leaf, trajectory := w.trajectory }
  have hAnchor : anchorOk x checked = true := by
    simp [anchorOk, checked, htraj, hhead]
  have hTrans : ∀ i, i + 1 < checked.trajectory.length →
      checked.trajectory[i + 1]! = acceleratedStep checked.trajectory[i]! := by
    intro i hi
    dsimp [checked] at hi ⊢
    rw [htraj] at hi ⊢
    exact routing_transition_fold_step (hd :: rest) hfold i hi
  have hne : hd :: rest ≠ [] := by simp
  have hlast : claim.Holds ((hd :: rest)[(hd :: rest).length - 1]!) := by
    have hidx : (hd :: rest).length - 1 < (hd :: rest).length := by
      simp
    rw [getElem!_pos (hd :: rest) ((hd :: rest).length - 1) hidx]
    rw [← List.getLast_eq_getElem hne]
    have hterm' : decide (claim.Holds ((hd :: rest).getLast hne)) = true := by
      simpa [List.getLast?_eq_some_getLast hne] using hterminal
    exact of_decide_eq_true hterm'
  have hClaim : ∀ y, claim.Holds y → ReachesOne y := by
    intro y hy
    apply hClaimReachesOne entry hentry y
    simpa [hclaim] using hy
  exact routing_trajectory_reaches_one x checked claim hAnchor hTrans
    (by simpa [checked, htraj] using hlast) hClaim


/-- **The ADR 0009 evidence tier, as a general obligation-discharge lemma.**

    For a claim registry whose entries all carry the terminal-value-1
    claim `FiniteOrbitClaim.singleton 1`, the reachability obligation that
    the per-leaf certificate construction demands
    (`∀ y, entry.claim.Holds y → ReachesOne y`) is **discharged by checked
    evidence** rather than assumed:

    - the claim's `Holds` reduces to `y = 1` (the terminal value is 1);
    - `ReachesOne 1` is witnessed at `k := 0` by `accelerated_orbit_zero 1`.

    This is the general form of the fixture-local proof in
    `Q5Stage4Tests.lean`: it holds for ANY registry of terminal-value-1
    claims, so it applies to a tree whose registry comes from the
    external producer as well as to a hand-written fixture.

    The two witnesses stay distinct (ADR 0009): the fact discharged here is
    the CLAIMED VALUE's zero-step reachability (`ReachesOne 1` at
    `k := 0`); the SOURCE's own orbit equality is a separate fact,
    established at the certificate's witness index by `trajectory_index`
    inside `terminal_claim_transport`.

    Kernel-clean: no orbit equation is evaluated, no `native_decide` is
    used, and no reachability hypothesis is assumed. -/
theorem terminal_value_one_claim_obligation
    (registry : List LeafClaimWire)
    (htier : ∀ entry ∈ registry, entry.claim = FiniteOrbitClaim.singleton 1) :
    ∀ entry ∈ registry, ∀ y, entry.claim.Holds y → ReachesOne y := by
  intro entry hmem y hy
  have hclaim : entry.claim = FiniteOrbitClaim.singleton 1 := htier entry hmem
  have hy1 : y = 1 := by
    rw [hclaim] at hy
    simpa only [FiniteOrbitClaim.Holds] using hy
  subst hy1
  exact ⟨0, accelerated_orbit_zero 1⟩

/-- Global checker acceptance yields conditional reachability for each
canonical input slot, provided every registered terminal claim is explicitly
known to reach one. -/
theorem routing_partition_certificate_slot_reaches_one
    (t : CoverageTree) (d : RoutingPartitionCertificateData)
    (hcheck : checkRoutingPartitionCertificate t d = true)
    (hClaimReachesOne : ∀ entry ∈ d.wire.claimRegistry, ∀ y,
      entry.claim.Holds y → ReachesOne y)
    (i : Fin d.wire.N) : ReachesOne (i.val + 1) :=
  routing_partition_witness_reaches_one t (i.val + 1)
    d.wire.claimRegistry (d.routingWitness i).val
    (checkRoutingPartitionCertificate_accepts_slot t d hcheck i)
    hClaimReachesOne

/-- **Terminal-value-one registry check (ADR 0009 evidence tier).**

    Returns `true` iff EVERY entry of the claim registry carries the
    canonical terminal-value-one claim `FiniteOrbitClaim.singleton 1`.

    This is a *data-side* obligation: it inspects only the SHAPE of the
    registered claims, never the orbit.  A producer may therefore
    discharge it by evaluation, exactly as the ADR 0009 tier permits for
    data-side obligations.  It asserts nothing by itself about
    reachability; the reachability conclusion is discharged separately,
    by the kernel-checked terminal-value-one lemma
    (`terminal_value_one_claim_obligation` in `Q5RoutingPartition.lean`).

    The claim shapes this check REJECTS: `.singleton n` for `n ≠ 1`
    (its `Holds` reduces to `y = n`, not `y = 1`) and `.bounded K`
    (its `Holds` reduces to `y ≤ K`, which admits `y = 0`).  Only
    `.singleton 1` reduces to `y = 1`, the terminal-value-1 condition
    the tier admits. -/
def checkTerminalValueOneClaims (registry : List LeafClaimWire) : Bool :=
  registry.all (fun entry => decide (entry.claim = FiniteOrbitClaim.singleton 1))

/-- **Soundness of the terminal-value-one registry check.**  A `true`
    check certifies the claim SHAPE of every registered entry; it makes no
    reachability claim of its own.  The reachability obligation it enables
    is discharged separately by `terminal_value_one_claim_obligation`. -/
theorem checkTerminalValueOneClaims_sound
    (registry : List LeafClaimWire)
    (h : checkTerminalValueOneClaims registry = true) :
    ∀ entry ∈ registry, entry.claim = FiniteOrbitClaim.singleton 1 := by
  intro entry hmem
  have hall := List.all_eq_true.mp h entry hmem
  exact of_decide_eq_true hall

/-- **Terminal-value-one per-slot routing reachability (ADR 0009 tier).**

    The general `routing_partition_certificate_slot_reaches_one` demands a
    per-registered REACHABILITY hypothesis
    (`entry.claim.Holds y → ReachesOne y`).  Under the ADR 0009 tier that
    hypothesis is a reachability obligation a producer may not discharge by
    evaluation.

    This variant replaces it with a CLAIM-SHAPE hypothesis — every
    registered entry carries `FiniteOrbitClaim.singleton 1` — which is
    data-side and decidable.  The reachability obligation is then
    DISCHARGED by `terminal_value_one_claim_obligation`, which reduces
    the claimed value to `y = 1` and supplies `ReachesOne 1` at
    `k := 0` via `accelerated_orbit_zero 1`.

    Trust boundary: no orbit equation is evaluated, no `native_decide` is
    used, and no reachability hypothesis is assumed. -/
theorem routing_partition_certificate_slot_reaches_one_terminal_value_one
    (t : CoverageTree) (d : RoutingPartitionCertificateData)
    (hcheck : checkRoutingPartitionCertificate t d = true)
    (htier : ∀ entry ∈ d.wire.claimRegistry,
      entry.claim = FiniteOrbitClaim.singleton 1)
    (i : Fin d.wire.N) : ReachesOne (i.val + 1) :=
  routing_partition_certificate_slot_reaches_one t d hcheck
    (terminal_value_one_claim_obligation d.wire.claimRegistry htier) i

/-- Global soundness of the routing-partition checker: every canonical
input slot (1..N) reaches 1, provided every registered claim is explicitly
known to reach 1.  This is the option-b (single-leaf redesign via routing
partition) analogue of `checkBoundedCertificate_sound`, closed via
the per-slot reachability above.  No `sorry` / `admit` / `axiom`; closed
by 2-line bounded proof (`intro x hx hN; simpa […]`). -/
theorem RoutingPartitionCertificate_sound
    (t : CoverageTree) (d : RoutingPartitionCertificateData)
    (hcheck : checkRoutingPartitionCertificate t d = true)
    (hClaimReachesOne : ∀ (entry : LeafClaimWire),
      entry ∈ d.wire.claimRegistry → ∀ y,
        entry.claim.Holds y → ReachesOne y) :
    ∀ (x : Nat), 0 < x → x ≤ d.wire.N → ReachesOne x := by
  intro x hx hN
  -- Convert the canonical input x (with 0 < x ≤ N) to the Fin-indexed slot
  -- `i = ⟨x - 1, hN : x - 1 < N⟩` whose canonical input is `i.val + 1 = x`.
  -- Use `simpa` + `Nat.sub_add_cancel` to rewrite the per-slot conclusion
  -- `ReachesOne ((x - 1) + 1)` to `ReachesOne x`.
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ x)] using
    routing_partition_certificate_slot_reaches_one t d hcheck
      hClaimReachesOne ⟨x - 1, by omega⟩

/-- **Terminal-value-one routing-partition soundness (ADR 0009 tier).**

    The global counterpart of
    `routing_partition_certificate_slot_reaches_one_terminal_value_one`:
    `checkRoutingPartitionCertificate t d = true` plus the data-side
    claim-shape hypothesis yields
    `∀ x, 0 < x → x ≤ d.wire.N → ReachesOne x`, with the general
    reachability hypothesis of `RoutingPartitionCertificate_sound`
    REPLACED rather than assumed.

    Trust boundary: no orbit equation is evaluated, no `native_decide` is
    used, and no reachability hypothesis is assumed. -/
theorem RoutingPartitionCertificate_sound_terminal_value_one
    (t : CoverageTree) (d : RoutingPartitionCertificateData)
    (hcheck : checkRoutingPartitionCertificate t d = true)
    (htier : ∀ entry ∈ d.wire.claimRegistry,
      entry.claim = FiniteOrbitClaim.singleton 1) :
    ∀ (x : Nat), 0 < x → x ≤ d.wire.N → ReachesOne x :=
  RoutingPartitionCertificate_sound t d hcheck
    (terminal_value_one_claim_obligation d.wire.claimRegistry htier)

end CollatzResearch
