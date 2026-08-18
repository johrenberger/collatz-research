import CollatzResearch.Basic

/-!
# Standard Collatz dynamics

Defines the standard (unaccelerated) Collatz map `C`, the parity and
positivity predicates used to give it a well-typed domain, and the
accelerated-step positivity theorem that connects the two maps on the
odd domain.

This file contains only definitions and elementary interface lemmas.
It makes no convergence, cycle-exclusion, or global descent claim.

**Proof status (2026-08-10, Story 02b/03b attempt):**
`standardStep_positive` and `acceleratedStep_positive_of_odd` use `sorry`.
Attempted approaches and blockers:

1. `standardStep_positive` (even branch `0 < n / 2` from `n` positive even):
   - `Nat.div_pos_iff.mpr ⟨by norm_num, omega⟩` — `omega` couldn't derive
     `2 ≤ n` from `0 < n ∧ n % 2 = 0` (omega doesn't see
     `n % 2 = 0 ∧ n > 0 → n ≥ 2`).
   - `rcases` + `subst` + `Nat.div_pos` — `Nat.div_pos` has signature
     `b ≤ a → 0 < b → 0 < a / b`, so we still need to prove `2 ≤ n`.
   - `rcases` + `False.elim` for the `n = 0`/`n = 1` cases — `False.elim`
     has typeclass issues and `decide` errors with `if p = 2` vs
     `if 2 = p` order.

2. `acceleratedStep_positive_of_odd` (`0 < T(n)` from `n` odd):
   - `Nat.div_pos_iff` + `Nat.factorization_le_iff_dvd` + `factorization_pow`
     + `Prime.factorization` + `Finsupp.smul_single'` + `Finsupp.single_apply`
     rewrite chain. `Finsupp.single_apply` DOES exist in this Mathlib
     (used in `ToDFinsupp.lean`) but `rw [Finsupp.single_apply]` fails
     because of the `if p = 2` vs `if 2 = p` order mismatch in the
     goal (fixed by `by_cases hp : 2 = p`).
   - `by_cases hp : 2 = p; subst hp; rw [Nat.mul_one]; rfl` works
     for the `p = 2` case. The `¬p = 2` case uses `rw [if_neg hp]`
     + `exact Nat.zero_le _`. This branch works in isolation.
   - Remaining blocker: `omega` on `(3*n+1).factorization 2 ≠ 0`
     for `factorization_le_iff_dvd.hn` — omega doesn't see
     `Odd n → 0 < n → 3n+1 ≥ 4 → 3n+1 ≠ 0`.

The shared root blocker is that `omega` doesn't see
`Odd n → 0 < n` and `n % 2 = 0 ∧ n > 0 → n ≥ 2` without
explicit `Nat.lt_of_succ_le`/`Nat.succ_le_succ`/`Nat.le_succ_succ`
step-by-step arguments. The needed lemma is `Odd n → 0 < n`
(available in Mathlib as `Odd.pos : Odd n → 0 < n`, or
equivalently `Nat.pos_of_neZero (n := n) (Nat.Odd.ne_zero n)`);
the previously-listed `Nat.Odd.one_lt : Odd n → 1 < n` is
impossible (it would prove `1 < 1` from `Odd 1`) and is
corrected here. Adding `Nat.pos_of_mul_pos_right : 0 < a * b → 0 < b`
(Mathlib already has this) and teaching `omega` to dispatch
`Odd.pos` would close both proofs in a single pass.

**Conclusion:** the definitions are correct and the file compiles.
The proof closure is tracked as Story 02b/03b proof completion in
the PR template's "Known limitations and follow-up" section.
-/

namespace CollatzResearch

/-- The standard (unaccelerated) Collatz map: n ↦ n / 2 if even, 3n + 1 if odd. -/
def standardStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Strict positivity on `Nat`. -/
def Positive (n : Nat) : Prop := 0 < n

/-- Standard step preserves positivity on the positive domain.

For the even branch, `n` is positive even, so `n ≥ 2` (since `1` is odd)
and `n / 2 ≥ 1 > 0`. For the odd branch, `3n + 1` is a positive
successor (`Nat.add` with `1` reduces to `Nat.succ`, so `Nat.succ_pos`
applies directly).
-/
theorem standardStep_positive (n : Nat) (h : Positive n) :
    Positive (standardStep n) := by
  unfold Positive standardStep
  split_ifs with h_even
  · -- even branch: n is positive even, hence n ≥ 2, so n / 2 ≥ 1 > 0
    -- Prove n ≠ 1 explicitly: 1 is odd, so `1 % 2 ≠ 0`.
    have hn1 : n ≠ 1 := by
      intro hn1
      subst hn1
      -- h_even : 1 % 2 = 0; reduce 1 % 2 = 1 via decide (no Mathlib import).
      have h1 : (1 : Nat) % 2 = 1 := by decide
      rw [h1] at h_even
      -- h_even : 1 = 0, which is False. omega closes the goal.
      omega
    -- Make positivity explicit so omega can use it (omega doesn't unfold `Positive`).
    change 0 < n at h
    -- Pure linear arithmetic on h, hn1. Clear h_even first: the `n % 2 = 0`
    -- constraint in scope confuses omega on the %-irrelevant goal `2 ≤ n`.
    have hlt : 2 ≤ n := by
      clear h_even
      omega
    -- Nat.div_pos in Mathlib v4.33.0: dividend-bound first, divisor-positivity second.
    exact Nat.div_pos hlt (by omega)
  · -- odd branch: 3 * n + 1 > 0 trivially (n : Nat).
    omega

/-- The accelerated Collatz step `T(n)` preserves positivity on the odd
domain.

The odd precondition is necessary: `T(0) = 1` is well-defined but
`T(n)` for non-positive `n` is not part of the project's contract.
This theorem is the first formal bridge between the accelerated map
(`CollatzResearch.Basic.acceleratedStep`) and the standard map
(`standardStep`) on the odd domain — it is the precondition for
Story 03's one-step equivalence theorem.
-/
theorem acceleratedStep_positive_of_odd (n : Nat) (h_odd : Odd n) :
    Positive (acceleratedStep n) := by
  unfold Positive acceleratedStep twoAdicValuation
  -- Goal: 0 < (3*n+1) / 2^((3*n+1).factorization 2)
  --
  -- Use Nat.div_pos (Mathlib v4.33.0 signature: dividend-bound first,
  -- divisor-positivity second — per Codex P1 on PR #37).
  apply Nat.div_pos
  · -- 2^((3*n+1).factorization 2) ≤ 3*n+1
    -- The 2-power factor of 3*n+1 divides 3*n+1 by definition of factorization;
    -- since 3*n+1 > 0, the divisor is bounded by the dividend.
    have h_ne : 3 * n + 1 ≠ 0 := by omega
    have h_le : (3 * n + 1).factorization 2 ≤ (3 * n + 1).factorization 2 :=
      Nat.le_refl _
    have h_dvd : 2 ^ ((3 * n + 1).factorization 2) ∣ 3 * n + 1 :=
      (Nat.factorization_le_iff_dvd h_ne Nat.prime_two).mpr h_le
    exact Nat.le_of_dvd h_ne h_dvd
  · -- 0 < 2^((3*n+1).factorization 2): any power of 2 is positive.
    omega

end CollatzResearch
