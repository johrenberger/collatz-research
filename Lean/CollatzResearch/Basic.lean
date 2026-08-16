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
  -- For odd n: 3n+1 is even, so ν₂(3n+1) ≥ 1
  -- The quotient by 2^ν₂(3n+1) has no factor of 2 by definition
  -- Step 1: 3n+1 is even
  have h_even : (3 * n + 1) % 2 = 0 := by
    obtain ⟨k, hk⟩ := h
    rw [hk]; ring_nf; simp
  -- Step 2: factorization 2 is positive (2 ∣ (3n+1) ↔ factorization 2 ≥ 1)
  have h_fact : 0 < (3 * n + 1).factorization 2 :=
    Nat.factorization_pos_iff_dvd.mpr (by
      rw [Nat.dvd_iff_mod_eq_zero]; exact h_even)
  -- Step 3: ((3n+1) / 2^ν₂(3n+1)).factorization 2 = 0 (no factor of 2 remains)
  have h_quot : ((3 * n + 1) / 2 ^ (3 * n + 1).factorization 2).factorization 2 = 0 := by
    rw [Nat.factorization_div _ _ (Nat.factorization_le_iff_dvd.mpr le_rfl),
        Nat.factorization_pow]
    ring
  -- Step 4: factorization 2 = 0 ↔ ¬ 2 ∣ (n) ↔ Odd n
  rw [Nat.factorization_eq_zero_iff] at h_quot
  rw [Nat.odd_iff]
  exact h_quot

end CollatzResearch
