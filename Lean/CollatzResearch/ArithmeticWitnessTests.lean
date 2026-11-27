import CollatzResearch.ArithmeticWitness
import CollatzResearch.ArithmeticWitnessTraces
import CollatzResearch.StandardMapBridge

/-!
# Regression tests for arithmetic step witnesses (story R04)

These tests pin the boundaries the story names:

- the concrete odd trajectory 3 -> 5 -> 1 and the longer trajectory from 27
  are accepted by the checker, and the acceptance yields the **canonical**
  trajectory endpoint through the generic theorem `traceOk_sound`, not by
  evaluating the orbit;
- an even start reaches one through the R02 standard normalization bridge;
- a malformed trace is rejected: an altered exponent, a non-odd successor,
  an incorrect arithmetic equation, an empty required trace, a wrong start,
  a wrong endpoint, and an even start;
- the zero-step trace for input 1 is represented by an empty step list.

No example evaluates an orbit equation with `native_decide`: a reachability
conclusion is kernel-checked (ADR 0009). The concrete acceptance checks use
`decide`, which reduces in the Lean kernel and therefore adds no
compiler-evaluated axiom; the endpoint facts are obtained by applying the
exported generic theorems.
-/

namespace CollatzResearch

/-! ## The concrete odd traces -/

/-- The trace 3 -> 5 -> 1 is accepted by the checker. -/
theorem traceThreeFiveOne_accepted : traceOk traceThreeFiveOne = true := by
  decide

/-- **The trace 3 -> 5 -> 1 is the canonical accelerated trajectory.**

The endpoint is obtained by applying the generic soundness theorem to the
accepted trace, so this test exercises `traceOk_sound` rather than
evaluating the orbit. -/
theorem traceThreeFiveOne_endpoint : trajectory 3 2 = 1 := by
  have h := traceOk_sound traceThreeFiveOne traceThreeFiveOne_accepted
  simpa [traceThreeFiveOne] using h

/-- The same trace, stated on the other accelerated-iteration name, so that
the result does not depend on which iteration definition is used. -/
theorem traceThreeFiveOne_reaches_one : ReachesOne 3 := by
  have h := traceOk_sound traceThreeFiveOne traceThreeFiveOne_accepted
  have htraj : trajectory 3 2 = 1 := by simpa [traceThreeFiveOne] using h
  refine ⟨2, ?_⟩
  rw [← trajectory_eq_accelerated_orbit]
  exact htraj

/-- The trajectory from 27 is accepted by the checker. -/
theorem traceTwentySeven_accepted : traceOk traceTwentySeven = true := by
  decide

/-- **The trajectory from 27 is the canonical accelerated trajectory.**

This is the nontrivial longer trace the story asks for: 41 accelerated steps
from 27 to 1, every one of them re-checked by the kernel. -/
theorem traceTwentySeven_endpoint : trajectory 27 41 = 1 := by
  have h := traceOk_sound traceTwentySeven traceTwentySeven_accepted
  simpa [traceTwentySeven] using h

/-! ## The zero-step trace for input 1 -/

/-- **The zero-step trace for input 1.**

The zero-step trace is represented by an *empty* step list: the trace starts
at 1, takes no steps, and therefore reaches its start. The endpoint field
still carries the claimed value 1, and the checker compares it against the
value the transitions reach. -/
def traceOne : TraceWitness :=
  { start := 1, steps := [], endpoint := 1 }

/-- The zero-step trace for input 1 is accepted. -/
theorem traceOne_accepted : traceOk traceOne = true := by
  decide

/-- The zero-step trace for input 1 reaches 1 in zero steps, through the
generic soundness theorem. -/
theorem traceOne_endpoint :
    trajectory traceOne.start traceOne.steps.length = traceOne.endpoint :=
  traceOk_sound traceOne traceOne_accepted

/-- The same, stated on concrete values. -/
theorem traceOne_concrete : trajectory 1 0 = 1 := by
  have h := traceOne_endpoint
  simpa only [traceOne, List.length_nil, trajectory_zero] using h

/-! ## An even start, through the R02 standard normalization bridge -/

/-- **The standard normalization of the even start 6.**

The accelerated map is only meaningful on the odd domain, so an even start
has to be handled on the standard map. The R02 bridge supplies the
normalization: 6 is a power of two times an odd part, and the standard
trajectory reaches that odd part after the halvings. -/
theorem even_start_six_normalization :
    ∃ a q : Nat, Odd q ∧ 0 < q ∧ 6 = 2 ^ a * q ∧ standardTrajectory 6 a = q :=
  exists_odd_normalization 6 (by omega)

/-- **The odd part of the even start 6 is 3.**

The normalization is unique here: `6 = 2 ^ a * q` with `q` odd and positive
forces `a = 1` and `q = 3`. This is the step that lets the even-start
result reuse the checked odd trace 3 -> 5 -> 1. -/
theorem even_start_six_odd_part :
    ∃ a q : Nat, Odd q ∧ 0 < q ∧ 6 = 2 ^ a * q ∧ standardTrajectory 6 a = q ∧ q = 3 := by
  obtain ⟨a, q, hq_odd, hq_pos, hn_eq, hstd⟩ := exists_odd_normalization 6 (by omega)
  have h2a_le : 2 ^ a ≤ 6 := by
    have hq1 : 1 ≤ q := by omega
    have hmul : 2 ^ a * 1 ≤ 2 ^ a * q := Nat.mul_le_mul_left (2 ^ a) hq1
    rw [← hn_eq] at hmul
    simpa using hmul
  have ha_lt : a < 3 := by
    have hlt : 2 ^ a < 2 ^ 3 := by omega
    exact (Nat.pow_lt_pow_iff_right (by omega : (1 : Nat) < 2)).1 hlt
  refine ⟨a, q, hq_odd, hq_pos, hn_eq, hstd, ?_⟩
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · -- 6 = 1 * q forces q = 6, which is even: this case cannot occur.
    simp only [pow_zero, one_mul] at hn_eq
    rw [Nat.odd_iff] at hq_odd
    omega
  · -- 6 = 2 * q forces q = 3.
    simp only [pow_one] at hn_eq
    omega
  · -- 6 = 4 * q has no natural solution: this case cannot occur.
    simp only [pow_two] at hn_eq
    omega

/-- **The even start 6 reaches one on the standard map.**

The bridge is used, not a second accelerated map: the standard trajectory
from 6 halves to its odd part 3, and the accepted odd trace 3 -> 5 -> 1
continues from there. The odd-domain trace is what the R04 checker verifies;
the standard-map transport is the existing R02 theorem
`acceleratedTrajectory_reaches_one_implies_standard`. -/
theorem even_start_six_reaches_one : ∃ m', standardTrajectory 6 m' = 1 := by
  obtain ⟨a, q, hq_odd, hq_pos, hn_eq, hstd, hq⟩ := even_start_six_odd_part
  subst hq
  have h3 : trajectory 3 2 = 1 := traceThreeFiveOne_endpoint
  obtain ⟨m', hstd3⟩ :=
    acceleratedTrajectory_reaches_one_implies_standard 3 2 (by decide) h3
  refine ⟨a + m', ?_⟩
  rw [← standardTrajectory_compose 6 a m', hstd, hstd3]

/-- The concrete standard length for the even start 6, checked in the
kernel. -/
theorem even_start_six_concrete_length : standardTrajectory 6 8 = 1 := by
  decide

/-! ## Rejection tests -/

/-- **An altered exponent is rejected.**

The first step of 3 -> 5 is `⟨1, 5⟩`: the equation is 3 * 3 + 1 = 2 * 5.
Altering the exponent to 2 makes the equation 3 * 3 + 1 = 4 * 5, which is
false, so the checker rejects the trace. -/
def traceThreeFiveOneAlteredExponent : TraceWitness :=
  { start := 3
    steps := [⟨2, 5⟩, ⟨4, 1⟩]
    endpoint := 1 }

theorem traceThreeFiveOneAlteredExponent_rejected :
    traceOk traceThreeFiveOneAlteredExponent = false := by
  decide

/-- **A non-odd successor is rejected.**

The step `⟨1, 8⟩` from 5 satisfies the arithmetic equation
3 * 5 + 1 = 16 = 2 * 8, but the successor 8 is even. The checker rejects it
because the accelerated map preserves oddness, so an even successor cannot
be an accelerated step. -/
def traceNonOddSuccessor : TraceWitness :=
  { start := 5
    steps := [⟨1, 8⟩]
    endpoint := 8 }

theorem traceNonOddSuccessor_rejected : traceOk traceNonOddSuccessor = false := by
  decide

/-- **An incorrect arithmetic equation is rejected.**

The step `⟨1, 6⟩` from 3 would require 3 * 3 + 1 = 2 * 6, which is false. -/
def traceWrongEquation : TraceWitness :=
  { start := 3
    steps := [⟨1, 6⟩, ⟨4, 1⟩]
    endpoint := 1 }

theorem traceWrongEquation_rejected : traceOk traceWrongEquation = false := by
  decide

/-- **An empty required trace is rejected.**

A trace that claims 3 reaches 1 with no steps at all is rejected: the
checker recomputes the reached value from the transitions, finds 3, and
compares it against the claimed endpoint 1. -/
def traceEmptyRequired : TraceWitness :=
  { start := 3, steps := [], endpoint := 1 }

theorem traceEmptyRequired_rejected : traceOk traceEmptyRequired = false := by
  decide

/-- **A wrong start is rejected.**

The first step of the 27 trajectory is `⟨1, 41⟩`, whose equation is
3 * 27 + 1 = 2 * 41. Reusing it from the wrong start 3 would require
3 * 3 + 1 = 2 * 41, which is false. -/
def traceWrongStart : TraceWitness :=
  { start := 3
    steps := [⟨1, 41⟩]
    endpoint := 41 }

theorem traceWrongStart_rejected : traceOk traceWrongStart = false := by
  decide

/-- **A wrong endpoint is rejected.**

The transitions of 3 -> 5 -> 1 reach 1, so a trace that claims they reach 5
is rejected. This is the case that shows the endpoint is checked rather than
trusted: the transitions are all individually correct, and only the
endpoint field is wrong. -/
def traceWrongEndpoint : TraceWitness :=
  { start := 3
    steps := [⟨1, 5⟩, ⟨4, 1⟩]
    endpoint := 5 }

theorem traceWrongEndpoint_rejected : traceOk traceWrongEndpoint = false := by
  decide

/-- **An even start is rejected by the odd-domain checker.**

The accelerated map is meaningful only on the odd domain, so the odd-domain
checker rejects an even start. The even start is handled on the standard map
by the R02 bridge, as `even_start_six_reaches_one` shows. -/
def traceEvenStart : TraceWitness :=
  { start := 2
    steps := [⟨1, 7⟩]
    endpoint := 7 }

theorem traceEvenStart_rejected : traceOk traceEvenStart = false := by
  decide

/-! ## The generic theorems are exercised, not just the examples -/

/-- The generic arithmetic-to-step bridge applies to a concrete step: the
equation 3 * 3 + 1 = 2 * 5 determines the valuation and the step. -/
theorem generic_bridge_applies_three :
    twoAdicValuation (3 * 3 + 1) = 1 ∧ acceleratedStep 3 = 5 := by
  refine ⟨twoAdicValuation_of_odd_factorization 3 1 5 (by omega) (by decide), ?_⟩
  exact acceleratedStep_of_odd_factorization 3 1 5 (by omega) (by decide)

/-- The generic checker soundness theorem applies to the concrete trace,
which is the point of exporting it: the example above is one instance of a
statement about every accepted trace. -/
theorem generic_soundness_applies_three :
    trajectory 3 traceThreeFiveOne.steps.length = traceThreeFiveOne.endpoint :=
  traceOk_sound traceThreeFiveOne traceThreeFiveOne_accepted

end CollatzResearch