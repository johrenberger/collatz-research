import CollatzResearch.StandardMapBridge

/-!
# Regression cases for the standard-map boundary

Story R02 asks for regression coverage of the boundary between the odd-domain
accelerated map and the standard map: zero excluded from the final theorem, one
as the base case, two and eight via halving, and three via the odd bridge. It
also asks explicitly for the even-input divergence to be recorded:
`acceleratedStep 2 = 7` against `standardStep 2 = 1`.

These are executable specifications, not the formal verification: the proofs
themselves live in `CollatzResearch.StandardMapBridge`.

**Trust discipline (ADR 0009).** The standard-map facts are kernel-checked by
`decide`, because `standardStep` and `standardTrajectory` reduce in the kernel.
The concrete `acceleratedStep` values use `native_decide`, because
`Nat.factorization` does not reduce in the kernel; they are data-side
obligations about the arithmetic of one map step, following the sibling
`CollatzResearch.CoverageTreeOrbitTests` convention. No example here asserts
that an orbit reaches 1: an orbit equation is a reachability conclusion, and
`native_decide` may never discharge one. The odd-domain bridge is instead
kernel-checked through `acceleratedStep_odd_of_odd`, and the orbit-to-one fact
for the base case is the definitional `accelerated_orbit 1 0 = 1`.
-/

namespace CollatzResearch

/-- Scenario: zero is excluded from the bridge theorem.

The standard map fixes zero (`standardStep 0 = 0`), so the standard trajectory
from zero never reaches 1, and the bridge theorem therefore requires
`0 < n`. The accelerated map sends zero to 1, so the two maps disagree at zero
as well as diverging elsewhere. -/
example : standardStep 0 = 0 := by decide
example : standardTrajectory 0 5 = 0 := by decide
example : acceleratedStep 0 = 1 := by native_decide

/-- Scenario: one is the base case.

One is odd, and the accelerated map fixes it, so the accelerated orbit of one
is 1 with no steps at all — a definitional fact, kernel-checked. The standard
trajectory of one is 1 with no steps as well. -/
example : accelerated_orbit 1 0 = 1 := rfl
example : standardTrajectory 1 0 = 1 := by decide
example : acceleratedStep 1 = 1 := by native_decide

/-- Scenario: two and eight reach 1 by halving.

Both are even, so the standard map halves them: two halves to one, and eight
halves through four and two. Their odd parts are one, so normalization gives
`2 = 2 ^ 1 * 1` and `8 = 2 ^ 3 * 1`, and the standard trajectory lands on the
odd part after exactly that many steps.

The even-input divergence the story asks to be recorded: the accelerated map at
an even input computes the odd part of `3n + 1` and is nothing like the
standard map's halving. -/
example : standardStep 2 = 1 := by decide
example : standardTrajectory 2 1 = 1 := by decide
example : standardTrajectory 8 3 = 1 := by decide
example : acceleratedStep 2 = 7 := by native_decide

/-- Scenario: three reaches 1 through the odd bridge.

Three is odd, so the accelerated map applies directly: three maps to five and
five maps to 1. The standard map instead takes three to ten and halves from
there. Normalization keeps three as its own odd part, so the standard
trajectory starts at the odd part with no halvings. The odd-domain invariant
that licenses the accelerated step is kernel-checked by
`acceleratedStep_odd_of_odd`. -/
example : Odd 3 := by decide
example : Odd (acceleratedStep 3) := acceleratedStep_odd_of_odd 3 (by decide)
example : acceleratedStep 3 = 5 := by native_decide
example : acceleratedStep 5 = 1 := by native_decide
example : standardStep 3 = 10 := by decide
example : standardTrajectory 3 0 = 3 := by decide

end CollatzResearch
