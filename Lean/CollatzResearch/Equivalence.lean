import CollatzResearch.Basic
import CollatzResearch.Dynamics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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

/-- **Shift lemma** for `standardTrajectory`: stepping `n` forward by one in
the trajectory equals starting from `standardStep n` and taking `k` steps.

    standardTrajectory n (k + 1) = standardTrajectory (standardStep n) k

Foundation for the proof of `acceleratedTrajectory_reaches_one_implies_standard`:
the induction hypothesis rewrites the inner `standardTrajectory n m` form to
`standardTrajectory (standardStep n) (m - 1)` so the IH can apply to the
one-step-reduced input.

**Why not `@[simp]`.** This lemma's LHS pattern (`standardTrajectory n (_ + 1)`)
overlaps with the existing `@[simp] theorem standardTrajectory_succ`. Marking
both creates a non-confluent simp rewrite system (simp would have two choices
for the same redex). Per `docs/lean-api-discipline.md`, this would violate
the stop-guessing rule's "prefer nearby proven local patterns" discipline.
Call this lemma explicitly via `rw [standardTrajectory_succ_shift]` when
the shift form is the target. -/
theorem standardTrajectory_succ_shift (n k : Nat) :
    standardTrajectory n (k + 1) = standardTrajectory (standardStep n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [standardTrajectory_succ, ih, ← standardTrajectory_succ]

/-- **Power division for `standardTrajectory`**: for `2^k ∣ x`, applying
`standardStep` `k` times to `x` divides by `2` at each step, yielding
`x / 2^k`.

    2^k ∣ x → standardTrajectory x k = x / 2^k

Foundation for `acceleratedStep_equiv_standardStep` (Equivalence
admission #1). Pure library-light lemma; no `Odd` hypothesis.

**Why not `@[simp]`.** The RHS `x / 2^k` is not a definitional
unfolding target; marking this `@[simp]` would create a non-confluent
simp rewrite system (LHS pattern `standardTrajectory x k` overlaps with
the existing `@[simp] theorem standardTrajectory_succ`). Per
`docs/lean-api-discipline.md`, prefer nearby-proven local patterns
over adding overlapping simp lemmas. Call this lemma explicitly via
`rw [standardTrajectory_pow_div]` when the power-division form is
the target.

**Proof.** Induction on `k`. Base `k = 0` is `simp [standardTrajectory]`. Step `k → k+1`:
`standardTrajectory x (k+1) = standardStep (standardTrajectory x k)`
`= standardStep (x / 2^k)` (by IH) `= (x / 2^k) / 2` (since
`x / 2^k` is even when `2^(k+1) ∣ x`) `= x / 2^(k+1)`. -/
lemma standardTrajectory_pow_div (x k : Nat) (h : 2^k ∣ x) :
    standardTrajectory x k = x / 2^k := by
  induction k generalizing x with
  | zero =>
    simp [standardTrajectory]
  | succ k ih =>
    rcases exists_eq_mul_left_of_dvd h with ⟨m, rfl⟩
    rw [show m * 2 ^ (k + 1) = 2 ^ k * (2 * m) by ring]
    rw [standardTrajectory_succ]
    have ih' := ih (2 ^ k * (2 * m)) ⟨2 * m, rfl⟩
    rw [ih']
    have h1 : (2 ^ k * (2 * m)) / 2 ^ k = 2 * m := by
      rw [Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 2))]
    rw [h1]
    have h2 : standardStep (2 * m) = m := by
      rw [standardStep]
      have h_even : (2 * m : Nat) % 2 = 0 := by omega
      rw [if_pos h_even]
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [h2]
    have h3 : (2 ^ k * (2 * m)) / 2 ^ (k + 1) = m := by
      rw [show 2 ^ k * (2 * m) = 2 ^ (k + 1) * m by ring]
      rw [Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 2))]
    rw [h3]

/-- One accelerated step on the odd domain corresponds to
`1 + ν₂(3n + 1)` standard steps.

This is the formal bridge between the accelerated map `T`
(`CollatzResearch.Basic.acceleratedStep`) and the standard map `C`
(`CollatzResearch.Dynamics.standardStep`) on the odd domain.

**Proof.** 4-`rw` composition of the three helper lemmas
`standardTrajectory_succ_shift` (PR #42, one-step shift),
`standardStep_of_odd` (PR #43, parity dispatch), and
`standardTrajectory_pow_div` (PR #45, power-division). The proof is
**not** by induction (the original PR #30 spec sketched an inductive
proof; the three helpers enabled a direct compositional rewrite).

Step-by-step:
1. `rw [Nat.add_comm]` — reorder `1 + x` to `x + 1`. Lean 4 `rw` does
   not reduce `1 + x` definitionally, so this rewrite is needed before
   step 2 matches.
2. `rw [standardTrajectory_succ_shift]` — unfold:
   `standardTrajectory n (k + 1) = standardTrajectory (standardStep n) k`.
3. `rw [standardStep_of_odd n h]` — on the odd domain (`Odd n`),
   `standardStep n = 3 * n + 1`.
4. `rw [standardTrajectory_pow_div (3*n+1) ((3*n+1).factorization 2)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity)).mpr (le_refl _))]`
   — apply power-division. The divisibility witness is constructed via
   `Nat.Prime.pow_dvd_iff_le_factorization` (canonical Mathlib v4.33.0 name;
   same lemma used by `Nat.Prime.pow_dvd_iff_dvd_ordProj` in
   `Mathlib.Data.Nat.Factorization.Basic` line 168). The `.mpr` direction
   takes `k ≤ n.factorization p` (here `le_refl _`) and produces `p^k ∣ n`.
5. `rw [acceleratedStep, twoAdicValuation]` — unfold the accelerated
   map (`acceleratedStep n = (3*n+1) / 2^twoAdicValuation (3*n+1)`) and
   `twoAdicValuation (3*n+1) = (3*n+1).factorization 2`. The goal
   closes by `rfl`.

The key observation is that each standard step `C` divides by 2 until
the value is odd, and the count of standard steps required to reach
the odd part is exactly `1 + ν₂(3n + 1)`.
-/
theorem acceleratedStep_equiv_standardStep (n : Nat) (h : Odd n) :
    standardTrajectory n (1 + (3 * n + 1).factorization 2) = acceleratedStep n := by
  rw [Nat.add_comm]
  rw [standardTrajectory_succ_shift]
  rw [standardStep_of_odd n h]
  rw [standardTrajectory_pow_div (3*n+1) ((3*n+1).factorization 2)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity)).mpr (le_refl _))]
  rw [acceleratedStep, twoAdicValuation]

/-- **Shift lemma for `trajectory`**: stepping `n` forward by one in
the accelerated trajectory equals starting from `acceleratedStep n` and
taking `k` steps.

    trajectory n (k + 1) = trajectory (acceleratedStep n) k

Foundation for `acceleratedTrajectory_reaches_one_implies_standard`:
the induction hypothesis rewrites the inner `trajectory n (k + 1)` form to
`trajectory (acceleratedStep n) k` so the IH can apply to the
one-step-reduced accelerated input (which is odd by
`acceleratedStep_odd_of_odd`).

**Why not `@[simp]`.** LHS pattern `trajectory n (k + 1)` overlaps with
the existing `@[simp] theorem trajectory_succ` — adding both creates a
non-confluent simp rewrite system. Per `docs/lean-api-discipline.md`,
prefer nearby-proven local patterns over adding overlapping simp lemmas.
Call this lemma explicitly via `rw [trajectory_succ_shift]`.

**Proof.** Induction on `k`. Base `k = 0` is `rfl` (using `trajectory n 1 =
acceleratedStep n` as `trajectory n (0 + 1)`). Step `k → k+1`: unfold via
`trajectory_succ`, apply IH, refold via `trajectory_succ`. -/
theorem trajectory_succ_shift (n k : Nat) :
    trajectory n (k + 1) = trajectory (acceleratedStep n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [trajectory_succ, ih, trajectory_succ]

/-- **Composition for `standardTrajectory`**: stepping
`standardTrajectory n a` forward by `b` steps equals starting from `n`
and taking `a + b` steps.

    standardTrajectory (standardTrajectory n a) b = standardTrajectory n (a + b)

Foundation for `acceleratedTrajectory_reaches_one_implies_standard`: chains
the forward-step equivalence
(`standardTrajectory n (1 + ν₂(3n+1)) = acceleratedStep n`) with the
inner-trajectory IH witness to produce the outer-trajectory witness
`m' = (1 + ν₂(3n+1)) + r`.

**Why not `@[simp]`.** LHS pattern `standardTrajectory (standardTrajectory n a) b`
overlaps with the existing `@[simp] theorem standardTrajectory_succ`. Per
`docs/lean-api-discipline.md`, prefer nearby-proven local patterns over
adding overlapping simp lemmas. Call this lemma explicitly via
`rw [standardTrajectory_compose]`.

**Proof.** Induction on `b`. Base `b = 0` is `rfl`. Step `b → b+1`: unfold
via `standardTrajectory_succ`, apply IH, refold via `standardTrajectory_succ`. -/
theorem standardTrajectory_compose (n a b : Nat) :
    standardTrajectory (standardTrajectory n a) b = standardTrajectory n (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show standardTrajectory (standardTrajectory n a) (b + 1) = standardTrajectory n (a + b + 1)
    rw [standardTrajectory_succ, ih, standardTrajectory_succ]

/-- An accelerated trajectory starting on the odd domain and reaching
`1` corresponds to a (finite) standard trajectory reaching `1`.

Forward direction of the standard ↔ accelerated equivalence at
trajectory level: a finite accelerated witness to convergence lifts
to a finite standard witness.

The `Odd n` precondition is essential for two reasons:
- `n = 0` divergence: `acceleratedStep 0 = 1` in `Nat` (since
  `0.factorization 2 = 0`, so `(0+1)/2^0 = 1`), but `standardStep 0 = 0`,
  so the maps diverge at `n = 0`. (Covered by `Odd n`, which implies
  `n ≥ 1` on `Nat`.)
- Even-input divergence: `acceleratedStep 2 = 7` while `standardStep 2 = 1`,
  so the forward equivalence `acceleratedStep_equiv_standardStep` does
  not hold on even inputs. Restricting to `Odd n` makes every iterate
  of the accelerated trajectory stay in the odd domain, where the
  forward equivalence applies at each step.

**Proof.** Induction on the accelerated-trajectory length `m`.
- Base case `m = 0`: `trajectory n 0 = n = 1` forces `n = 1`, and
  `standardTrajectory n 0 = n = 1`.
- Inductive case `m = k + 1`: rewrite the hypothesis via
  `trajectory_succ_shift` to `trajectory (acceleratedStep n) k = 1`.
  `acceleratedStep n` is odd (by `acceleratedStep_odd_of_odd n h_odd`),
  so the IH applies with witness `r`. Compose via `standardTrajectory_compose`:
  `standardTrajectory n ((1 + ν₂(3n+1)) + r) = standardTrajectory (standardTrajectory n (1 + ν₂(3n+1))) r
                                       = standardTrajectory (acceleratedStep n) r  (by acceleratedStep_equiv_standardStep)
                                       = 1                                        (by IH)

The proof is **not** by direct construction of the full sum
`(1 + ν₂(3n+1)) + (1 + ν₂(3 n_1 + 1)) + ... + (1 + ν₂(3 n_{k-1} + 1))`
as originally spec'd; the front-of-trajectory induction (per
re-review #3 P1 2026-08-16T18:04:30Z) reduces the witness to
`(1 + ν₂(3n+1)) + r` where `r` is the IH witness for the inner
trajectory. -/
theorem acceleratedTrajectory_reaches_one_implies_standard (n m : Nat)
    (h_odd : Odd n) (h : trajectory n m = 1) : ∃ m', standardTrajectory n m' = 1 := by
  induction m using Nat.strongRecOn generalizing n with
  | _ m ih =>
    cases m with
    | zero =>
      -- h : trajectory n 0 = 1, so n = 1 (by trajectory_zero)
      -- standardTrajectory n 0 = n (by standardTrajectory_zero), so standardTrajectory n 0 = 1
      exact ⟨0, by
        show standardTrajectory n 0 = 1
        rw [show standardTrajectory n 0 = n from rfl, ← trajectory_zero]
        exact h⟩
    | succ k =>
      -- h : trajectory n (k + 1) = 1
      rw [trajectory_succ_shift] at h
      -- h : trajectory (acceleratedStep n) k = 1
      -- ih : ∀ m' < succ k, ∀ n', Odd n' → trajectory n' m' = 1 → ∃ m'', standardTrajectory n' m'' = 1
      -- Apply ih at m' = k (since k < succ k), n' = acceleratedStep n
      have h_odd' : Odd (acceleratedStep n) := acceleratedStep_odd_of_odd n h_odd
      obtain ⟨r, hr⟩ := ih k (by omega) (acceleratedStep n) h_odd' h
      -- hr : standardTrajectory (acceleratedStep n) r = 1
      -- Witness m' = (1 + ν₂(3n+1)) + r (forward step + inner IH witness)
      exact ⟨(1 + (3*n+1).factorization 2) + r, by
        show standardTrajectory n ((1 + (3*n+1).factorization 2) + r) = 1
        rw [standardTrajectory_compose]
        rw [acceleratedStep_equiv_standardStep n h_odd]
        rw [hr]⟩

end CollatzResearch