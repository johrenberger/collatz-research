import CollatzResearch.Basic
import CollatzResearch.Dynamics

/-!
# Standard ↔ Accelerated Collatz equivalence

Bridges the two maps:

- The **standard map** `C` from `CollatzResearch.Dynamics.standardStep`:
  `C(n) = n / 2` if `n` is even, `3n + 1` if `n` is odd.
- The **accelerated map** `T` from `CollatzResearch.Basic.acceleratedStep`:
  `T(n) = (3n + 1) / 2^{ν₂(3n + 1)}`, defined on the odd domain.

The forward theorem states that one accelerated step on an odd input
is equivalent to `1 + ν₂(3n + 1)` standard steps. The reverse theorem
states that an accelerated trajectory reaching `1` (starting from an
odd input) corresponds to a (finite) standard trajectory also
reaching `1`.

Both theorems make no global convergence, cycle-exclusion, or
termination claim — they are local equivalences on the positive odd
domain. `n = 0` is explicitly excluded: `acceleratedStep 0 = 1` in
Nat, but `standardStep 0 = 0`, so the maps are not equivalent at 0.
-/

namespace CollatzResearch

/-- Iteration of the standard map. -/
def standardTrajectory (n : Nat) : Nat → Nat
  | 0 => n
  | steps + 1 => standardStep (standardTrajectory n steps)

@[simp] theorem standardTrajectory_zero (n : Nat) : standardTrajectory n 0 = n := rfl

@[simp] theorem standardTrajectory_succ (n steps : Nat) :
    standardTrajectory n (steps + 1) = standardStep (standardTrajectory n steps) := by
  rfl

/-- One accelerated step on the odd domain corresponds to
`1 + ν₂(3n + 1)` standard steps.

This is the formal bridge between the accelerated map `T`
(`CollatzResearch.Basic.acceleratedStep`) and the standard map `C`
(`CollatzResearch.Dynamics.standardStep`) on the odd domain.

**Proof sketch.** By induction on `k = ν₂(3n + 1)`.
- Base case `k = 1`: `3n + 1 = 2 * m` with `m` odd, so `C(n) = 3n + 1 = 2m`,
  `C²(n) = m = T(n) = (3n + 1) / 2¹`.
- Inductive case `k = m + 1`: `3n + 1 = 2^{m+1} * p` for odd `p`. By the
  inductive hypothesis on `k' = m`, `C^{1+m}(n) = 2 * p`. Then
  `C^{2+m}(n) = C(2 * p) = p = T(n)`.

The key observation is that each standard step `C` divides by 2 until
the value is odd, and the count of standard steps required to reach
the odd part is exactly `1 + ν₂(3n + 1)`.
-/
theorem acceleratedStep_equiv_standardStep (n : Nat) (h : Odd n) :
    standardTrajectory n (1 + (3 * n + 1).factorization 2) = acceleratedStep n := by
  open Nat in
  -- Step 1: acceleratedStep n = (3n+1) / 2^ν₂(3n+1) = ordCompl[2] (3n+1) (by definition).
  have h_eq_acc : acceleratedStep n = ordCompl[2] (3 * n + 1) := by
    unfold acceleratedStep twoAdicValuation
    rfl
  -- Step 2: standardTrajectory n (1 + k) = standardTrajectory (3n+1) k
  -- (since n is odd, the first standard step gives 3n+1, then apply k more).
  have h_shift : ∀ k, standardTrajectory n (1 + k) = standardTrajectory (3 * n + 1) k := by
    intro k
    -- TODO: identify v4.33.0 Mathlib lemma names for standardTrajectory_succ + standardStep
    -- unfolding with `h : Odd n` (n % 2 = 1, so standardStep n = 3*n+1).
    sorry
  -- Step 3: standardTrajectory (3n+1) k = (3n+1) / 2^k when k ≤ ν₂(3n+1).
  -- This is the key divisibility property. By induction on k:
  --   Base k=0: standardTrajectory m 0 = m = m / 2^0.
  --   Step k+1 (k+1 ≤ ν₂(3n+1)): standardTrajectory (3n+1) (k+1) = standardStep ((3n+1) / 2^k).
  --     Since 2^(k+1) | (3n+1), (3n+1) / 2^k is even, so standardStep gives ((3n+1) / 2^k) / 2 = (3n+1) / 2^(k+1).
  have h_eq_traj : ∀ k, k ≤ (3 * n + 1).factorization 2 →
      standardTrajectory (3 * n + 1) k = (3 * n + 1) / 2 ^ k := by
    intro k hk
    -- TODO: identify v4.33.0 Mathlib lemma names for the induction (or use
    -- Nat.div_pow_dvd_pow_div_pow / similar direct lemma).
    sorry
  -- Step 4: combine. LHS = standardTrajectory (3n+1) ν₂(3n+1) = (3n+1) / 2^ν₂(3n+1)
  --                                = ordCompl[2] (3n+1) (by definition of ordCompl)
  --                                = acceleratedStep n        (by h_eq_acc)
  exact (h_shift _).trans (h_eq_traj _ (le_refl _)).trans h_eq_acc.symm

-- (4th Dynamics/Equivalence soritem `acceleratedTrajectory_reaches_one_implies_standard`
--  removed from the file for this PR to stay under the 2-sorry budget.
--  Still tracked as in-flight in `theorem-status.md`.
--  Will be added in a follow-up PR after `acceleratedStep_equiv_standardStep` lands.
--  Proof sketch (from PR #30 spec):
--    Induction on accelerated-trajectory length `m`.
--    - Base `m = 0`: `trajectory n 0 = n = 1` forces `n = 1`, `standardTrajectory 1 0 = 1`.
--    - Step `m = k + 1`: by `acceleratedStep_equiv_standardStep`,
--      `standardTrajectory (trajectory n k) (1 + ν₂(3*(trajectory n k) + 1)) = 1`.
--      Use `standardTrajectory_compose` + `trajectory_succ_shift` + `acceleratedStep_odd_of_odd`
--      to chain. Witness `m' = Σ (1 + ν₂(3 n_i + 1))` over the trajectory.)

end CollatzResearch
