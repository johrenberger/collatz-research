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

/-- `acceleratedStep` preserves oddness on the odd domain.

For odd `n`, `3n+1` is even, so `ν₂(3n+1) ≥ 1`. The quotient
`(3n+1)/2^ν₂(3n+1)` is the maximal odd divisor of `3n+1`, hence odd.

This is the relocated declaration from `Certificate.lean` per the Story 02c/03c
spec (PR #30); both `Certificate.lean::DescentWitness.trajectory_odd` and
`Equivalence.lean::acceleratedTrajectory_reaches_one_implies_standard` consume
this version.
-/
theorem acceleratedStep_odd_of_odd (n : Nat) (h : Odd n) :
    Odd (acceleratedStep n) := by
  -- acceleratedStep n = (3n+1) / 2^ν₂(3n+1) where ν₂ m = m.factorization 2
  -- By Mathlib notation: ordCompl[2] m = m / ordProj[2] m, where
  --   ordProj[2] m = 2^(m.factorization 2) (the 2-power part of m)
  --   ordCompl[2] m = the odd part of m
  -- So acceleratedStep n = ordCompl[2] (3n+1) (the odd part of 3n+1).
  --
  -- The key Mathlib fact is Nat.not_dvd_ordCompl:
  --   ¬ p ∣ ordCompl[p] m  when  p is prime and  m ≠ 0.
  -- For p = 2 (Nat.prime_two), this gives  ¬ 2 ∣ ordCompl[2] (3n+1).
  -- The conversion ¬ 2 ∣ x ↔ Odd x is Nat.odd_iff (the standard equivalence).
  --
  -- Step 1: 3n+1 is nonzero (trivially, since 3n+1 ≥ 1 for all n)
  have h_nonzero : 3 * n + 1 ≠ 0 := by omega
  -- Step 2: Apply Nat.not_dvd_ordCompl with p := 2
  have h_not_dvd : ¬ 2 ∣ Nat.ordCompl[2] (3 * n + 1) :=
    Nat.not_dvd_ordCompl Nat.prime_two h_nonzero
  -- Step 3: acceleratedStep n = Nat.ordCompl[2] (3n+1) by definition
  have h_eq : acceleratedStep n = Nat.ordCompl[2] (3 * n + 1) := by
    unfold acceleratedStep twoAdicValuation Nat.ordProj Nat.ordCompl
    rfl
  rw [h_eq] at h_not_dvd
  -- Step 4: Convert ¬ 2 ∣ acceleratedStep n to Odd acceleratedStep n
  rw [Nat.odd_iff]
  exact h_not_dvd

end CollatzResearch
