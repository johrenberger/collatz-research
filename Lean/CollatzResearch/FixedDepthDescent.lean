import Mathlib.Order.Bounds.Basic
import CollatzResearch.ArithmeticWitness
import CollatzResearch.Basic
import CollatzResearch.DescentToConvergence

/-!
# Fixed-depth descent obstruction (story R05)

Story R05 asks for a proof of what the current finite-prefix
representation cannot establish: there is no fixed depth that bounds the
first strict descent of every positive odd input.

## The ascent family

For `K >= 1` let `n = 2^(K+1) - 1`. The odd trajectory from `n` does not
descend within `K` steps; it *ascends*:

    trajectory n j + 1 = 3^j * 2^(K+1-j)        for 0 <= j <= K

Equivalently `trajectory n j = 3^j * 2^(K+1-j) - 1`. Each of the first
`K` transitions has two-adic valuation exactly one, so every step is a
single halving and the recurrence unrolls exactly.

## The obstruction

- `no_fixed_depth_descent_bound`: no `L` bounds the first descent of
  *every* positive odd `n > 1`; and
- `no_fixed_depth_descent_bound_except_finite`: for any finite set `E` of
  positive odd inputs, some positive odd `n > 1` outside `E` still has no
  descent within `L` steps.

The second form is the stronger statement: it is what rules out rescuing
a fixed-depth bound by excepting finitely many inputs.

## The architectural consequence

A finite list of explicit fixed-length descent words cannot cover the full
domain: the depth of the first descent is unbounded. Parameterized proofs,
recursion, and other ranking measures remain possible, and nothing here
rules them out.

## Why the arithmetic is stated with explicit side conditions

The closed form involves natural subtraction, which would otherwise be
silently truncated. The induction is therefore stated in the `+ 1` form,
where every quantity is a product and no truncation can occur, and the
subtraction form is recovered only where its side condition is explicit
(`trajectory_ascentFormula_sub`).

## Trust boundary

This module proves **no convergence, no descent, and no cycle
exclusion**. It proves a *negative* statement about a fixed-depth
strategy: such a strategy cannot work on the whole domain. The
universal descent premise of R03 (`UniversalOddDescent`) remains
**OPEN**; this module does not assume it, refute it, or weaken it. The
story is also consistent with `UniversalOddDescent` holding: the
obstruction is about the existence of a *uniform* bound on the depth of
the first descent, and says nothing about whether a given input descends.

No `sorry`, no `admit`, no `axiom`, and no `native_decide`.
-/

namespace CollatzResearch

/-! ## Definitions -/

/-- The starting point of the ascent family of depth `K`: `2^(K+1) - 1`. -/
def ascentStart (K : Nat) : Nat := 2 ^ (K + 1) - 1

/-- The value the ascent family reaches after `j` steps, for `j <= K`. -/
def ascentValue (K j : Nat) : Nat := 3 ^ j * 2 ^ (K + 1 - j) - 1

/-- **Descent within a bounded number of steps.**

`n` descends within `L` steps when some positive `k <= L` reaches a
strictly smaller positive value. This is the bounded-depth notion the
story asks about; it is *stronger* than `EventuallyDescends`, which puts
no bound on `k`: `EventuallyDescendsWithin L n` implies
`EventuallyDescends n` (see `EventuallyDescendsWithin.of_descends`). -/
def EventuallyDescendsWithin (L : Nat) (n : Nat) : Prop :=
  ∃ k, 0 < k ∧ k ≤ L ∧ 0 < trajectory n k ∧ trajectory n k < n

/-- A descent within a bounded number of steps is a descent. -/
theorem EventuallyDescendsWithin.of_descends {L n : Nat} (h : EventuallyDescendsWithin L n) :
    EventuallyDescends n := by
  obtain ⟨k, hk1, _, hk3, hk4⟩ := h
  exact ⟨k, hk1, hk3, hk4⟩

/-! ## Arithmetic helpers -/

/-! The valuation lemma this module needs is **R04's**:
`twoAdicValuation_of_odd_factorization` in `CollatzResearch.ArithmeticWitness`
states that from `3 * n + 1 = 2 ^ k * m` and `Odd m` one gets
`twoAdicValuation (3 * n + 1) = k`. Its shape is exactly the shape used
below, so R05 reuses it rather than restating it: the arithmetic-to-step
bridge is proved once, in R04. -/

/-- **A power of two in successor form.** -/
theorem two_pow_succ (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ]
  ring

/-- **A power of two is twice the preceding power** (for a positive exponent). -/
theorem two_pow_pred (m : Nat) (h : 0 < m) : 2 ^ m = 2 * 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.pow_succ]
  simp only [Nat.succ_sub_one]
  ring

/-- **A power of two is at least one more than its exponent.** -/
theorem two_pow_ge_succ : ∀ k : Nat, 2 ^ k ≥ k + 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      have h2 : (k + 1) * 2 = 2 * k + 2 := by ring
      have hmul : (k + 1) * 2 ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 ih
      omega

/-- **One less than a positive even number is odd.** -/
theorem odd_of_even_mul_sub_one {r : Nat} (h : 0 < r) : Odd (2 * r - 1) := by
  refine ⟨r - 1, ?_⟩
  omega

/-- **One less than three times a positive even number is odd.** -/
theorem odd_of_three_mul_even_sub_one {Y : Nat} (hY : 0 < Y) (hYeven : ∃ r, Y = 2 * r) :
    Odd (3 * Y - 1) := by
  obtain ⟨r, hr⟩ := hYeven
  have hr1 : 0 < r := by
    rw [hr] at hY
    omega
  have h3r : 0 < 3 * r := by omega
  obtain ⟨k, hk⟩ := odd_of_even_mul_sub_one (r := 3 * r) h3r
  refine ⟨k, ?_⟩
  have heq : 3 * Y - 1 = 2 * (3 * r) - 1 := by
    rw [hr]
    omega
  rw [heq]
  exact hk

/-- **The arithmetic of one ascent step.**

If `x + 1 = 2 * Y`, then `3 * x + 1 = 2 * (3 * Y - 1)`.

The subtraction is exact because `Y` is positive. -/
theorem step_fac (x Y : Nat) (_hY : 0 < Y) (h : x + 1 = 2 * Y) :
    3 * x + 1 = 2 * (3 * Y - 1) := by
  have h1 : 3 * x + 1 = 3 * (x + 1) - 2 := by
    have hge : 2 ≤ 3 * (x + 1) := by
      have : 0 < 3 * (x + 1) := by positivity
      omega
    omega
  have h2 : 3 * (x + 1) - 2 = 6 * Y - 2 := by
    rw [h]
    have heq : 3 * (2 * Y) = 6 * Y := by ring
    rw [heq]
  have h3 : 2 * (3 * Y - 1) = 6 * Y - 2 := by
    have heq : 2 * (3 * Y) = 6 * Y := by ring
    rw [Nat.mul_sub_left_distrib, heq]
  exact h1.trans (h2.trans h3.symm)

/-- **One accelerated step of the ascent family.**

If `x + 1 = 2 * Y` with `Y` positive and even, then the accelerated step
out of `x` is a single halving to `3 * Y - 1`, and the two-adic valuation
of `3 * x + 1` is exactly one.

This is the arithmetic core of the ascent family: every step divides by
exactly two. -/
theorem acceleratedStep_of_two_mul (x Y : Nat) (hY : 0 < Y) (h : x + 1 = 2 * Y)
    (hYeven : ∃ r, Y = 2 * r) : acceleratedStep x = 3 * Y - 1 := by
  have hodd := odd_of_three_mul_even_sub_one hY hYeven
  have hfac := step_fac x Y hY h
  have hval : twoAdicValuation (3 * x + 1) = 1 := by
    have hfac2 : 3 * x + 1 = 2 ^ 1 * (3 * Y - 1) := by
      rw [hfac]
      norm_num
    exact twoAdicValuation_of_odd_factorization _ 1 _ hfac2 hodd
  unfold acceleratedStep
  rw [hval, Nat.pow_one]
  have hdiv : (3 * x + 1) / 2 = 3 * Y - 1 := by
    rw [hfac]
    exact Nat.mul_div_cancel_left (3 * Y - 1) (by omega)
  exact hdiv

/-! ## The ascent family -/

/-- **The starting point of the ascent family is odd.** -/
theorem ascentStart_odd (K : Nat) : Odd (ascentStart K) := by
  have hge : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  refine ⟨2 ^ K - 1, ?_⟩
  unfold ascentStart
  rw [two_pow_succ]
  omega

/-- **The starting point of the ascent family exceeds one** (for `K >= 1`). -/
theorem ascentStart_gt_one (K : Nat) (h : 1 ≤ K) : 1 < ascentStart K := by
  have h1 : 0 < K + 1 := by omega
  have hp : 2 ^ (K + 1) = 2 * 2 ^ K := two_pow_pred _ h1
  have h4 : 2 ≤ 2 ^ K := Nat.le_pow (a := 2) (b := K) (by omega)
  have h5 : 4 ≤ 2 ^ (K + 1) := by rw [hp]; omega
  unfold ascentStart
  omega

/-- **The starting point of the ascent family is positive** (for `K >= 1`). -/
theorem ascentStart_pos (K : Nat) (h : 1 ≤ K) : 0 < ascentStart K := by
  have hgt := ascentStart_gt_one K h
  omega

/-- **The closed form, in the form that avoids subtraction.**

For `0 <= j <= K` the accelerated trajectory from `2^(K+1) - 1` reaches a
value one below `3^j * 2^(K+1-j)`.

Proof by induction on `j`. The base case is `trajectory n 0 = n`. In the
step, `x = trajectory n j` satisfies `x + 1 = 3^j * 2^(K+1-j)`, so
`3 * x + 1 = 3^(j+1) * 2^(K+1-j) - 2 = 2 * (3^(j+1) * 2^(K-j) - 1)`, whose
odd part is `3^(j+1) * 2^(K-j) - 1`: the accelerated step is a single
halving.
-/
theorem trajectory_ascentFormula (K j : Nat) (hj : j ≤ K) :
    trajectory (ascentStart K) j + 1 = 3 ^ j * 2 ^ (K + 1 - j) := by
  induction j generalizing K with
  | zero =>
      have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
      simp only [trajectory_zero, pow_zero, Nat.sub_zero, Nat.one_mul]
      unfold ascentStart
      omega
  | succ j ih =>
      have hjK : j ≤ K := by omega
      have hIH : trajectory (ascentStart K) j + 1 = 3 ^ j * 2 ^ (K + 1 - j) := ih K hjK
      have hidx : K + 1 - j - 1 = K - j := by omega
      have hp : 2 ^ (K + 1 - j) = 2 * 2 ^ (K - j) := by
        have h := two_pow_pred (K + 1 - j) (by omega)
        rw [h, hidx]
      set Y := 3 ^ j * 2 ^ (K - j) with hYdef
      have hYpos : 0 < Y := by
        rw [hYdef]
        positivity
      have hx1 : trajectory (ascentStart K) j + 1 = 2 * Y := by
        rw [hIH, hYdef, hp]
        ring
      have hYeven : ∃ r, Y = 2 * r := by
        refine ⟨3 ^ j * 2 ^ (K - j - 1), ?_⟩
        have h2 : 2 ^ (K - j) = 2 * 2 ^ (K - j - 1) := two_pow_pred _ (by omega)
        rw [hYdef, h2]
        ring
      have hstep := acceleratedStep_of_two_mul (trajectory (ascentStart K) j) Y hYpos hx1 hYeven
      have h3 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [Nat.pow_succ']
      have h3Y : 3 * Y = 3 ^ (j + 1) * 2 ^ (K - j) := by
        rw [hYdef, h3]
        ring
      rw [trajectory_succ, hstep]
      have hidxC : K + 1 - (j + 1) = K - j := by omega
      rw [h3Y, hidxC]
      have hpos : 0 < 3 ^ (j + 1) * 2 ^ (K - j) := by positivity
      omega

/-- **The side condition of the subtraction form.** -/
theorem ascentFormula_side (K j : Nat) (_hj : j ≤ K) :
    0 < 3 ^ j * 2 ^ (K + 1 - j) := by
  positivity

/-- **The closed form in the subtraction form the story states.**

The side condition `0 < 3^j * 2^(K+1-j)` is explicit: it is what makes
the subtraction exact rather than truncated. -/
theorem trajectory_ascentFormula_sub (K j : Nat) (hj : j ≤ K)
    (hpos : 0 < 3 ^ j * 2 ^ (K + 1 - j)) :
    trajectory (ascentStart K) j = 3 ^ j * 2 ^ (K + 1 - j) - 1 := by
  have h := trajectory_ascentFormula K j hj
  omega

/-- The subtraction form, stated unconditionally. -/
theorem trajectory_ascentFormula_sub_uncond (K j : Nat) (hj : j ≤ K) :
    trajectory (ascentStart K) j = ascentValue K j := by
  have hpos := ascentFormula_side K j hj
  exact trajectory_ascentFormula_sub K j hj hpos

/-- **Each of the first `K` transitions has two-adic valuation exactly one.** -/
theorem ascent_valuation_one (K j : Nat) (hj1 : j + 1 ≤ K) :
    twoAdicValuation (3 * trajectory (ascentStart K) j + 1) = 1 := by
  have hIH : trajectory (ascentStart K) j + 1 = 3 ^ j * 2 ^ (K + 1 - j) :=
    trajectory_ascentFormula K j (by omega)
  have hidx : K + 1 - j - 1 = K - j := by omega
  have hp : 2 ^ (K + 1 - j) = 2 * 2 ^ (K - j) := by
    have h := two_pow_pred (K + 1 - j) (by omega)
    rw [h, hidx]
  set Y := 3 ^ j * 2 ^ (K - j) with hYdef
  have hYpos : 0 < Y := by
    rw [hYdef]
    positivity
  have hx1 : trajectory (ascentStart K) j + 1 = 2 * Y := by
    rw [hIH, hYdef, hp]
    ring
  have hYeven : ∃ r, Y = 2 * r := by
    refine ⟨3 ^ j * 2 ^ (K - j - 1), ?_⟩
    have h2 : 2 ^ (K - j) = 2 * 2 ^ (K - j - 1) := two_pow_pred _ (by omega)
    rw [hYdef, h2]
    ring
  have hodd := odd_of_three_mul_even_sub_one hYpos hYeven
  have hfac := step_fac (trajectory (ascentStart K) j) Y hYpos hx1
  have hfac2 : 3 * trajectory (ascentStart K) j + 1 = 2 ^ 1 * (3 * Y - 1) := by
    rw [hfac]
    norm_num
  exact twoAdicValuation_of_odd_factorization _ 1 _ hfac2 hodd

/-! ## Ascent: the value exceeds the start -/

/-- **A power of three exceeds the same power of two** (for `j >= 1`). -/
theorem three_pow_gt_two_pow : ∀ j : Nat, 1 ≤ j → 2 ^ j < 3 ^ j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro h
      by_cases hj0 : j = 0
      · subst j
        norm_num
      · have hj1 : 1 ≤ j := by omega
        have hgt : 2 ^ j < 3 ^ j := ih hj1
        rw [Nat.pow_succ, Nat.pow_succ]
        have hA : 2 ^ j * 2 < 3 ^ j * 2 := Nat.mul_lt_mul_of_pos_right hgt (by omega)
        have hB : 3 ^ j * 2 ≤ 3 ^ j * 3 := Nat.mul_le_mul_left (3 ^ j) (by omega)
        exact Nat.lt_of_lt_of_le hA hB

/-- **The ascent family ascends: the value at `j` exceeds the start.** -/
theorem ascentValue_gt_start (K j : Nat) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    trajectory (ascentStart K) j > ascentStart K := by
  have hform := trajectory_ascentFormula K j hjK
  have hn : ascentStart K + 1 = 2 ^ (K + 1) := by
    unfold ascentStart
    have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
    omega
  have h3 : 2 ^ j < 3 ^ j := three_pow_gt_two_pow j hj1
  have hc : 0 < 2 ^ (K + 1 - j) := by positivity
  have hmul : 2 ^ j * 2 ^ (K + 1 - j) < 3 ^ j * 2 ^ (K + 1 - j) :=
    Nat.mul_lt_mul_of_pos_right h3 hc
  have hexp : 2 ^ j * 2 ^ (K + 1 - j) = 2 ^ (K + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  omega

/-- **No descent within `K` steps for the ascent family of depth `K`.** -/
theorem ascent_no_descent_within (K : Nat) :
    ¬ EventuallyDescendsWithin K (ascentStart K) := by
  intro h
  obtain ⟨k, hk1, hk2, _, hk4⟩ := h
  have hgt := ascentValue_gt_start K k hk1 hk2
  omega

/-! ## The obstruction -/

/-- **No fixed depth bounds the first descent of every positive odd input.** -/
theorem no_fixed_depth_descent_bound (L : Nat) :
    ∃ n, Odd n ∧ 1 < n ∧ ¬ EventuallyDescendsWithin L n := by
  set K := max L 1 with hK
  have hKL : L ≤ K := Nat.le_max_left L 1
  have hK1 : 1 ≤ K := by
    have h := Nat.le_max_right L 1
    omega
  refine ⟨ascentStart K, ascentStart_odd K, ascentStart_gt_one K hK1, ?_⟩
  intro h
  obtain ⟨k, hk1, hk2, _, hk4⟩ := h
  have hjk : k ≤ K := by omega
  have hgt := ascentValue_gt_start K k hk1 hjk
  omega

/-- **No fixed depth bounds the first descent, even outside finitely many
exceptional inputs.** -/
theorem no_fixed_depth_descent_bound_except_finite (L : Nat) (E : Set Nat) (hE : E.Finite) :
    ∃ n, Odd n ∧ 1 < n ∧ n ∉ E ∧ ¬ EventuallyDescendsWithin L n := by
  have hbdd : BddAbove E := hE.bddAbove
  rw [bddAbove_def] at hbdd
  obtain ⟨M, hM⟩ := hbdd
  set K := max (max (M + 1) L) 1 with hK
  have hKL : L ≤ K := by
    have h1 : L ≤ max (M + 1) L := Nat.le_max_right _ _
    have h2 : max (M + 1) L ≤ max (max (M + 1) L) 1 := Nat.le_max_left _ _
    omega
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ max (max (M + 1) L) 1 := Nat.le_max_right _ _
    have h2 : max (M + 1) L ≤ max (max (M + 1) L) 1 := Nat.le_max_left _ _
    omega
  have hKM : M + 1 ≤ K := by
    have h1 : M + 1 ≤ max (M + 1) L := Nat.le_max_left _ _
    have h2 : max (M + 1) L ≤ max (max (M + 1) L) 1 := Nat.le_max_left _ _
    omega
  refine ⟨ascentStart K, ascentStart_odd K, ascentStart_gt_one K hK1, ?_, ?_⟩
  · intro hn
    have hnM : ascentStart K ≤ M := hM _ hn
    have hgt : M < ascentStart K := by
      have hp := two_pow_ge_succ (K + 1)
      have h1 : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
      unfold ascentStart
      omega
    omega
  · intro h
    obtain ⟨k, hk1, hk2, _, hk4⟩ := h
    have hjk : k ≤ K := by omega
    have hgt := ascentValue_gt_start K k hk1 hjk
    omega

end CollatzResearch
