import CollatzResearch.DescentToConvergence
import CollatzResearch.FixedDepthDescent

/-!
# Regression tests for the fixed-depth descent obstruction (story R05)

These tests pin the concrete ascent family the story names (`L = 1, 2, 3`)
and the universally quantified obstruction.

The tests apply the exported generic theorems rather than restating them,
so a change in the generic statements is caught here. No test evaluates an
orbit equation with `native_decide`: the concrete values are obtained by
applying the closed form and then evaluating pure arithmetic with
`decide`, which reduces in the Lean kernel and therefore adds no
compiler-evaluated axiom.

No test asserts a convergence claim. A bound that is hit is an unknown
outcome, never a negative universal conclusion.
-/

namespace CollatzResearch

/-! ## The concrete ascent family -/

/-- **The ascent family of depth 1 starts at 3.** -/
theorem ascentStart_one : ascentStart 1 = 3 := by decide

/-- **The ascent family of depth 2 starts at 7.** -/
theorem ascentStart_two : ascentStart 2 = 7 := by decide

/-- **The ascent family of depth 3 starts at 15.** -/
theorem ascentStart_three : ascentStart 3 = 15 := by decide

/-- **The ascent family of depth 1 is odd and exceeds one.** -/
theorem ascentStart_one_odd_gt_one : Odd (ascentStart 1) ∧ 1 < ascentStart 1 := by
  exact ⟨ascentStart_odd 1, ascentStart_gt_one 1 (by omega)⟩

/-- **The ascent family of depth 2 is odd and exceeds one.** -/
theorem ascentStart_two_odd_gt_one : Odd (ascentStart 2) ∧ 1 < ascentStart 2 := by
  exact ⟨ascentStart_odd 2, ascentStart_gt_one 2 (by omega)⟩

/-- **The ascent family of depth 3 is odd and exceeds one.** -/
theorem ascentStart_three_odd_gt_one : Odd (ascentStart 3) ∧ 1 < ascentStart 3 := by
  exact ⟨ascentStart_odd 3, ascentStart_gt_one 3 (by omega)⟩

/-! ## The closed form at concrete depths -/

/-- **At depth 1, step 1, the trajectory reaches 5.**

This is the story's `L = 1` example: the trajectory from `3` reaches `5`
after one accelerated step, which is *above* the start, so no descent has
happened. The value comes from the closed form, not from evaluating the
orbit. -/
theorem ascent_one_step : trajectory (ascentStart 1) 1 = 5 := by
  calc trajectory (ascentStart 1) 1 = 3 ^ 1 * 2 ^ (1 + 1 - 1) - 1 :=
      trajectory_ascentFormula_sub_uncond 1 1 (by omega)
    _ = 5 := by decide

/-- **At depth 2, step 1, the trajectory reaches 11.** -/
theorem ascent_two_step_one : trajectory (ascentStart 2) 1 = 11 := by
  calc trajectory (ascentStart 2) 1 = 3 ^ 1 * 2 ^ (2 + 1 - 1) - 1 :=
      trajectory_ascentFormula_sub_uncond 2 1 (by omega)
    _ = 11 := by decide

/-- **At depth 2, step 2, the trajectory reaches 17.** -/
theorem ascent_two_step_two : trajectory (ascentStart 2) 2 = 17 := by
  calc trajectory (ascentStart 2) 2 = 3 ^ 2 * 2 ^ (2 + 1 - 2) - 1 :=
      trajectory_ascentFormula_sub_uncond 2 2 (by omega)
    _ = 17 := by decide

/-- **At depth 3, step 3, the trajectory reaches 53.** -/
theorem ascent_three_step_three : trajectory (ascentStart 3) 3 = 53 := by
  calc trajectory (ascentStart 3) 3 = 3 ^ 3 * 2 ^ (3 + 1 - 3) - 1 :=
      trajectory_ascentFormula_sub_uncond 3 3 (by omega)
    _ = 53 := by decide

/-- **The closed form in the subtraction form the story states.**

For `L = 1` and `j = 1` the identity reads
`trajectory (2^(L+1) - 1) j = 3^j * 2^(L+1-j) - 1`. -/
theorem ascent_one_formula_sub :
    trajectory (ascentStart 1) 1 = 3 ^ 1 * 2 ^ (1 + 1 - 1) - 1 :=
  trajectory_ascentFormula_sub_uncond 1 1 (by omega)

/-! ## The ascent family does not descend within its depth -/

/-- **At depth 1 there is no descent within one step.** -/
theorem no_descent_within_one : ¬ EventuallyDescendsWithin 1 (ascentStart 1) := by
  exact ascent_no_descent_within 1

/-- **At depth 2 there is no descent within two steps.** -/
theorem no_descent_within_two : ¬ EventuallyDescendsWithin 2 (ascentStart 2) := by
  exact ascent_no_descent_within 2

/-- **At depth 3 there is no descent within three steps.** -/
theorem no_descent_within_three : ¬ EventuallyDescendsWithin 3 (ascentStart 3) := by
  exact ascent_no_descent_within 3

/-! ## The obstruction -/

/-- **No fixed depth bounds the first descent.** -/
theorem obstruction_holds :
    ∃ n, Odd n ∧ 1 < n ∧ ¬ EventuallyDescendsWithin 1 n := by
  exact no_fixed_depth_descent_bound 1

/-- **No fixed depth bounds the first descent, even outside finitely many
exceptional inputs.**

The exceptional set here is `{1, 3, 5}`, so the witness the theorem
produces lies outside it: the obstruction is not rescued by excepting a
handful of inputs. -/
theorem obstruction_except_finite_holds :
    ∃ n, Odd n ∧ 1 < n ∧ n ∉ ({1, 3, 5} : Set Nat) ∧
      ¬ EventuallyDescendsWithin 2 n := by
  have hE : ({1, 3, 5} : Set Nat).Finite := by simp
  exact no_fixed_depth_descent_bound_except_finite 2 _ hE

/-- **A bounded descent is still a descent.**

The obstruction is about *bounded* descent only: the unbounded descent
predicate is strictly stronger, so the obstruction does not by itself
settle the descent question. -/
theorem bounded_descent_is_descent {L n : Nat} (h : EventuallyDescendsWithin L n) :
    EventuallyDescends n :=
  EventuallyDescendsWithin.of_descends h

end CollatzResearch
