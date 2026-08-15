import Mathlib.Data.Nat.Factorization.Basic

/-!
# Basic accelerated Collatz definitions

This file intentionally contains definitions and elementary interface lemmas only.
It makes no convergence, cycle-exclusion, or global descent claim.
-/

namespace CollatzResearch

/-- The exponent of two dividing `n`; `Nat.factorization` makes the zero case explicit. -/
def twoAdicValuation (n : Nat) : Nat := n.factorization 2

/-- The odd-only accelerated Collatz step. The caller supplies the odd-domain invariant. -/
def acceleratedStep (n : Nat) : Nat := (3 * n + 1) / 2 ^ twoAdicValuation (3 * n + 1)

/-- Iteration of the accelerated map. -/
def trajectory (n : Nat) : Nat → Nat
  | 0 => n
  | steps + 1 => acceleratedStep (trajectory n steps)

@[simp] theorem trajectory_zero (n : Nat) : trajectory n 0 = n := rfl

@[simp] theorem trajectory_succ (n steps : Nat) :
    trajectory n (steps + 1) = acceleratedStep (trajectory n steps) := by
  rfl

/-- `acceleratedStep` on specific closed values (Story 07c-4 executable
    spec needs these closed Nat computations to reduce). `native_decide`
    closes the closed Nat evaluation; the `@[simp]` annotation makes
    `simp` (hence proofs closing through `simp`) reduce `acceleratedStep n`
    for these inputs without needing kernel-level reduction of Mathlib's
    `twoAdicValuation`. -/
@[simp] theorem acceleratedStep_zero : acceleratedStep 0 = 1 := by native_decide
@[simp] theorem acceleratedStep_one  : acceleratedStep 1 = 1 := by native_decide
@[simp] theorem acceleratedStep_five : acceleratedStep 5 = 1 := by native_decide

end CollatzResearch
