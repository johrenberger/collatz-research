import CollatzResearch.Basic
import CollatzResearch.CoverageTree
import CollatzResearch.DescentWitness
import CollatzResearch.DescentToConvergence

/-!
# Regression tests for the descent-to-convergence reduction (story R03)

These tests pin the boundaries the story names:

- `n = 1` is the terminal base case, not a strict-descent case;
- a zero-step witness and an equal-endpoint witness cannot satisfy descent;
- the descent endpoint stays positive and odd, which is what the strong
  induction consumes at every inductive call.

No example evaluates an orbit equation with `native_decide`: a reachability
conclusion is kernel-checked (ADR 0009). The concrete application test is
conditional on a descent hypothesis, so it exercises the generic theorem
without asserting any arithmetic fact about a concrete orbit.
-/

namespace CollatzResearch

/-- `n = 1` is the terminal base case, not a strict-descent case: no witness
can end strictly below 1 and stay positive. -/
theorem not_eventually_descends_one : ¬ EventuallyDescends 1 := by
  rintro ⟨k, _hk, hpos, hlt⟩
  omega

/-- The terminal base case is nevertheless convergent in one step of the
accelerated map: the orbit of 1 is 1. -/
theorem terminal_base_reaches_one : ReachesOne 1 := by
  exact ⟨0, accelerated_orbit_zero 1⟩

/-- A zero-step witness cannot satisfy descent: at step 0 the trajectory is
still the starting value, so it is not strictly below it. -/
theorem zero_step_is_not_descent (n : Nat) :
    ¬ (0 < trajectory n 0 ∧ trajectory n 0 < n) := by
  rw [trajectory_zero]
  omega

/-- An equal-endpoint witness cannot satisfy descent: descent is strict. -/
theorem equal_endpoint_is_not_descent (n k : Nat) (h : trajectory n k = n) :
    ¬ (0 < trajectory n k ∧ trajectory n k < n) := by
  rw [h]
  omega

/-- A descent witness yields a strictly smaller endpoint. -/
theorem descent_is_strict (h : EventuallyDescends n) :
    ∃ k, 0 < k ∧ 0 < trajectory n k ∧ trajectory n k < n := h

/-- The descent endpoint stays positive and odd, which is exactly what the
strong induction consumes at every inductive call: the induction hypothesis
is stated for odd positive inputs. -/
theorem descent_endpoint_stays_odd (hOdd : Odd n) (h : EventuallyDescends n) :
    ∃ k, Odd (trajectory n k) ∧ 0 < trajectory n k ∧ trajectory n k < n := by
  obtain ⟨k, hk, hpos, hlt⟩ := h
  exact ⟨k, DescentWitness.trajectory_odd n k hOdd, hpos, hlt⟩

/-- The strong-induction step applies to a concrete input: assuming 3
descends, 3 reaches one.

The descent hypothesis at 3 is assumed, not proved: proving it is the open
obligation of story R03, and the concrete arithmetic of that orbit is not
checked here (an orbit equation may not be discharged by `native_decide`).
What this test does check is that the generic step theorem applies, that its
induction hypothesis is discharged for every smaller odd positive input, and
that the endpoint lands on the terminal base case 1. -/
theorem reaches_one_three_of_descent (h : EventuallyDescends 3) : ReachesOne 3 := by
  refine reaches_one_of_descent_step (n := 3) (hOdd := ?_) h ?_
  · exact Nat.odd_iff.mpr (by decide)
  · intro m hmOdd hmPos hmLt
    have hm : m = 1 := by
      have hmod : m % 2 = 1 := Nat.odd_iff.mp hmOdd
      omega
    subst hm
    exact ⟨0, accelerated_orbit_zero 1⟩

/-- The composed theorem is applicable: the R02 standard-map bridge consumes
the descent premise. -/
theorem standard_convergence_from_descent (H : UniversalOddDescent)
    (n : Nat) (hn : 0 < n) : StandardReachesOne n :=
  universal_standard_convergence_of_universal_odd_descent H n hn

end CollatzResearch
