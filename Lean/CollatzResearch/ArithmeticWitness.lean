import CollatzResearch.Basic
import CollatzResearch.Equivalence

/-!
# Arithmetic step witnesses without native evaluation

Story R04 asks for finite trajectories that are certified by explicit
arithmetic equations and generic lemmas, *without* trusting native
evaluation of `Nat.factorization`.

The gap this module closes: `CollatzResearch.Basic.acceleratedStep` computes
the odd part of `3n + 1` through `Nat.factorization`, so a result that
merely evaluates an orbit equation leans on that computation. Checking such
an equation with `native_decide` is worse: it makes the result
compiler-dependent, which the transitive axiom audit (R01, ADR 0013)
classifies as a `compiler_dependent_instance`.

This module takes the other route. A producer supplies **raw numbers**: the
exponent `k` and the successor `m` of a step, together with the equation
`3 * n + 1 = 2 ^ k * m`. Lean then checks that equation with ordinary
kernel-checked arithmetic, and this module proves **once** that the equation
determines the accelerated step:

- `twoAdicValuation_of_odd_factorization`: the equation forces
  `twoAdicValuation (3 * n + 1) = k`, so the producer cannot pick a
  wrong exponent.
- `acceleratedStep_of_odd_factorization`: the equation forces
  `acceleratedStep n = m`, so a producer cannot supply a wrong successor.

The proof never evaluates `Nat.factorization`; it uses the Mathlib
factorization *lemmas* symbolically (`Nat.factorization_mul`,
`Nat.factorization_pow_self`, `Nat.factorization_eq_zero_of_not_dvd`).

## The finite-trace checker

`stepsOk` and `traceOk` are **total**: they take raw numeric data and
return a `Bool`, with no partial functions and no proof fields supplied by
the producer. `traceOk` checks

1. the start is positive and odd;
2. every transition satisfies `StepWitness.Valid` — positive odd input,
   exponent at least one, positive odd successor, and the arithmetic
   equation `3 * x + 1 = 2 ^ exponent * successor`;
3. the declared endpoint is the value the transitions actually reach.

`stepsOk_sound` and `traceOk_sound` then prove that acceptance implies the
**canonical** trajectory endpoint: `trajectory start steps.length = endpoint`.
The endpoint is derived from the transitions, never carried as a proof field.

## Trust boundary

This module proves no convergence, no descent, and no cycle exclusion. It
certifies **finite** trajectories only, and only on the odd domain, which is
where `acceleratedStep` is meaningful. The standard-map side is reached
through the R02 bridge (`acceleratedStep_equiv_standardStep`), never by
defining a second, competing accelerated map.

No `sorry`, no `admit`, no `axiom`, and no `native_decide`: every
concrete result in this module and its companions has a kernel-checked
`#print axioms` closure free of native-evaluation axioms.
-/

namespace CollatzResearch

/-- One raw arithmetic transition of an accelerated trajectory.

The two fields are **data**, not proofs: the exponent of two and the
successor value. `StepWitness.Valid` is the predicate that says a pair of
raw numbers really is a transition of the accelerated map, and it is what the
checker establishes. -/
structure StepWitness where
  /-- The exponent `k` in `3 * x + 1 = 2 ^ k * successor`. -/
  exponent : Nat
  /-- The successor `m` in `3 * x + 1 = 2 ^ k * successor`. -/
  successor : Nat
  deriving Repr, DecidableEq

/-- A raw finite trajectory: the start value, the transitions, and the
claimed endpoint.

All three are raw numbers supplied by an untrusted producer. The claimed
endpoint is *checked* against the transitions rather than trusted; the
acceptance theorem `traceOk_sound` derives the canonical trajectory
endpoint from the transitions alone. -/
structure TraceWitness where
  /-- The first value of the trajectory. -/
  start : Nat
  /-- The transitions, in order. -/
  steps : List StepWitness
  /-- The value the producer claims the trajectory reaches. -/
  endpoint : Nat
  deriving Repr, DecidableEq

/-- **The value a list of transitions reaches.**

The last successor, or the starting value when there are no transitions.
This is computed from the raw step data alone; it is not the producer's
claim, and the checker compares the two. -/
def reached : Nat → List StepWitness → Nat
  | x, [] => x
  | _, s :: rest => reached s.successor rest

/-! ## The generic arithmetic-to-step bridge -/

/-- **A step witness determines the two-adic valuation.**

If `3 * n + 1 = 2 ^ k * m` and `m` is odd, then
`twoAdicValuation (3 * n + 1) = k`.

This is the first half of R04's "prove once" requirement: the exponent in a
step witness is not a free parameter, it is the valuation, so a producer
cannot supply a wrong exponent.

**Proof.** Rewrite the equation, split the factorization over the product
(`Nat.factorization_mul`), evaluate the power of two
(`Nat.factorization_pow_self`), and read off the odd factor
(`Nat.factorization_eq_zero_of_not_dvd`, since `m` is odd and so not
divisible by two). The factorization lemmas are used symbolically; the
valuation is never evaluated. -/
theorem twoAdicValuation_of_odd_factorization (n k m : Nat)
    (h : 3 * n + 1 = 2 ^ k * m) (hm : Odd m) :
    twoAdicValuation (3 * n + 1) = k := by
  have h2k : 2 ^ k ≠ 0 := by
    have : 0 < 2 ^ k := by positivity
    exact this.ne'
  have hm0 : m ≠ 0 := by
    intro hmz
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    rw [hmz] at hmod
    simp at hmod
  have hnotdvd : ¬ (2 : Nat) ∣ m := by
    intro hh
    have hmod : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hh
    have hmod1 : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  unfold twoAdicValuation
  rw [h, Nat.factorization_mul h2k hm0]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  omega

/-- **A step witness determines the accelerated step.**

If `3 * n + 1 = 2 ^ k * m` and `m` is odd, then `acceleratedStep n = m`.

This is the second half of R04's "prove once" requirement: the successor in
a step witness is not a free parameter, it is the canonical accelerated step,
so a producer cannot supply a wrong successor.

The proof rewrites the valuation using
`twoAdicValuation_of_odd_factorization` and then cancels the power of two.
No native evaluation is involved. -/
theorem acceleratedStep_of_odd_factorization (n k m : Nat)
    (h : 3 * n + 1 = 2 ^ k * m) (hm : Odd m) :
    acceleratedStep n = m := by
  unfold acceleratedStep
  rw [twoAdicValuation_of_odd_factorization n k m h hm]
  rw [h]
  have hpos : 0 < 2 ^ k := by positivity
  exact Nat.mul_div_cancel_left m hpos

/-- **A step witness with a positive exponent forces the input to be odd.**

The exponent being at least one means `2 ^ k` divides `3 * n + 1`, so
`3 * n + 1` is even and therefore `3 * n` is odd, so `n` is odd. This
records that the odd-domain precondition of the accelerated map is implied
by the witness format itself, not merely assumed.

**Proof.** `2 ^ k` is even when `k` is at least one, so `2 ^ k * m` is
even, so `3 * n + 1` is even. A case split on `n % 2` then shows `n` is
odd: if `n` were even, `3 * n` would be even and `3 * n + 1` odd, a
contradiction. -/
theorem odd_of_two_pow_mul_odd (n k m : Nat) (hk : 1 ≤ k)
    (h : 3 * n + 1 = 2 ^ k * m) : Odd n := by
  have hpow : (2 : Nat) ^ k % 2 = 0 := by
    have hk' : k = (k - 1) + 1 := by omega
    rw [hk', ← Nat.succ_eq_add_one, pow_succ, Nat.mul_mod]
    simp
  have hmod : (3 * n + 1) % 2 = 0 := by
    rw [h, Nat.mul_mod, hpow]
    simp
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · have hmod3 : (3 * n) % 2 = 0 := by
      simp [Nat.mul_mod, h0]
    have hplus : (3 * n + 1) % 2 = 1 := by
      simp [Nat.add_mod, hmod3]
    rw [hplus] at hmod
    simp at hmod
  · exact Nat.odd_iff.mpr h1

/-- **The standard-map length of a witnessed step.**

If `n` is odd and `3 * n + 1 = 2 ^ k * m` with `m` odd, then the
standard trajectory reaches `m` after exactly `1 + k` standard steps: one
odd step to `3 * n + 1`, followed by `k` halvings.

This is where the R02 boundary is reused rather than re-implemented: the
standard-map statement is the existing `acceleratedStep_equiv_standardStep`,
and only the accelerated half is re-expressed through a witness. -/
theorem standardTrajectory_of_odd_factorization (n k m : Nat) (hn : Odd n)
    (h : 3 * n + 1 = 2 ^ k * m) (hm : Odd m) :
    standardTrajectory n (1 + k) = m := by
  have hval : twoAdicValuation (3 * n + 1) = k :=
    twoAdicValuation_of_odd_factorization n k m h hm
  have hstd : standardTrajectory n (1 + twoAdicValuation (3 * n + 1)) = acceleratedStep n :=
    acceleratedStep_equiv_standardStep n hn
  rw [hval] at hstd
  rw [hstd]
  exact acceleratedStep_of_odd_factorization n k m h hm

/-! ## The step and trace predicates -/

/-- **A raw pair of numbers is a valid transition.**

The four obligations, in order: the input is positive and odd (the domain
where `acceleratedStep` is meaningful), the exponent is at least one, the
successor is positive and odd, and the arithmetic equation
`3 * x + 1 = 2 ^ exponent * successor` holds.

Everything here is arithmetic on raw numbers. Nothing in this predicate is a
proof supplied by the producer. -/
def StepWitness.Valid (x : Nat) (s : StepWitness) : Prop :=
  0 < x ∧ (Odd x ∧ (1 ≤ s.exponent ∧ (0 < s.successor ∧
    (Odd s.successor ∧ (3 * x + 1 = 2 ^ s.exponent * s.successor)))))

/-- **A list of raw steps is valid from a starting value.**

Mirrors the recursive structure of the checker: the head step must be valid
from the current value, and the tail must be valid from the head's
successor. -/
def stepsValid : Nat → List StepWitness → Prop
  | _, [] => True
  | x, s :: rest => StepWitness.Valid x s ∧ stepsValid s.successor rest

/-- **A raw trajectory is valid.**

The start is positive and odd, the transitions are valid, and the claimed
endpoint is the value the transitions actually reach. -/
def TraceWitness.Valid (t : TraceWitness) : Prop :=
  0 < t.start ∧ (Odd t.start ∧ (stepsValid t.start t.steps ∧
    (reached t.start t.steps = t.endpoint)))

/-! ## The total checker -/

/-- **Check one transition.**

Total: a plain Boolean function over raw numbers. It establishes the
transition from the arithmetic equation alone.

The conjunction is written right-nested on purpose: it matches the shape of
`StepWitness.Valid` exactly, so the agreement theorem below is a rewrite
rather than a re-association. -/
def stepOk (x : Nat) (s : StepWitness) : Bool :=
  decide (0 < x) && (decide (x % 2 = 1) && (decide (1 ≤ s.exponent) &&
    (decide (0 < s.successor) && (decide (s.successor % 2 = 1) &&
      decide (3 * x + 1 = 2 ^ s.exponent * s.successor)))))

/-- **Check a whole list of transitions, threading the current value through.**

Total: returns `true` for the empty list, which is the zero-step trace. -/
def stepsOk : Nat → List StepWitness → Bool
  | _, [] => true
  | x, s :: rest => stepOk x s && stepsOk s.successor rest

/-- **The total finite-trace checker.**

Accepts raw numeric trace data and returns a `Bool`. It checks the start,
every transition, and the declared endpoint.

The endpoint is *checked against* the transitions, not trusted: the producer
supplies `t.endpoint`, the checker recomputes `reached t.start t.steps`
from the transition data and compares. -/
def traceOk (t : TraceWitness) : Bool :=
  decide (0 < t.start) && (decide (t.start % 2 = 1) &&
    (stepsOk t.start t.steps && decide (reached t.start t.steps = t.endpoint)))

/-- The Boolean checker and the propositional validity agree on a single
transition. -/
theorem stepOk_iff (x : Nat) (s : StepWitness) :
    stepOk x s = true ↔ StepWitness.Valid x s := by
  simp only [stepOk, StepWitness.Valid, Bool.and_eq_true, decide_eq_true_eq,
    Nat.odd_iff]

/-- The Boolean checker and the propositional validity agree on a list of
transitions. -/
theorem stepsOk_iff (x : Nat) (steps : List StepWitness) :
    stepsOk x steps = true ↔ stepsValid x steps := by
  induction steps generalizing x with
  | nil => simp [stepsOk, stepsValid]
  | cons s rest ih =>
      simp only [stepsOk, stepsValid, Bool.and_eq_true, stepOk_iff, ih]

/-- The Boolean checker and the propositional validity agree on a whole
trace. -/
theorem traceOk_iff (t : TraceWitness) :
    traceOk t = true ↔ TraceWitness.Valid t := by
  simp only [traceOk, TraceWitness.Valid, Bool.and_eq_true, decide_eq_true_eq,
    Nat.odd_iff, stepsOk_iff]

/-- **Acceptance implies the canonical trajectory endpoint.**

If the transitions of a list are accepted from `x`, then the canonical
accelerated trajectory from `x` ends at the value those transitions
reach.

This is the core soundness statement of R04's finite-trace checker: the
endpoint is *derived*, never supplied.

**Proof.** Induction on the list of transitions. The empty list gives a
zero-step trajectory, whose endpoint is the start. For a nonempty list, the
head transition is valid, so its equation determines the accelerated step
(`acceleratedStep_of_odd_factorization`); `trajectory_succ_shift` then
rewrites the trajectory to start from the successor, and the induction
hypothesis applies. -/
theorem stepsOk_sound : ∀ (steps : List StepWitness) (x e : Nat),
    stepsOk x steps = true → reached x steps = e → trajectory x steps.length = e := by
  intro steps
  induction steps with
  | nil =>
      intro x e _ hreach
      simp only [reached] at hreach
      simp only [List.length_nil]
      rw [trajectory_zero, hreach]
  | cons s rest ih =>
      intro x e hsteps hreach
      simp only [stepsOk, Bool.and_eq_true] at hsteps
      have hstep : StepWitness.Valid x s := (stepOk_iff x s).mp hsteps.1
      have hrest : stepsOk s.successor rest = true := hsteps.2
      have hreach' : reached s.successor rest = e := by
        simpa only [reached] using hreach
      have htraj : trajectory s.successor rest.length = e :=
        ih s.successor e hrest hreach'
      have hEq : 3 * x + 1 = 2 ^ s.exponent * s.successor := hstep.2.2.2.2.2
      have hOdd : Odd s.successor := hstep.2.2.2.2.1
      have hstepEq : acceleratedStep x = s.successor :=
        acceleratedStep_of_odd_factorization x s.exponent s.successor hEq hOdd
      simp only [List.length_cons]
      rw [trajectory_succ_shift, hstepEq, htraj]

/-- **Acceptance of a whole trace implies the canonical trajectory
endpoint.**

The public soundness theorem for the finite-trace checker: a trace whose
transitions and declared endpoint are accepted yields
`trajectory t.start t.steps.length = t.endpoint`. -/
theorem traceOk_sound (t : TraceWitness) (h : traceOk t = true) :
    trajectory t.start t.steps.length = t.endpoint := by
  have hvalid : TraceWitness.Valid t := (traceOk_iff t).mp h
  have hok : stepsOk t.start t.steps = true := (stepsOk_iff _ _).mpr hvalid.2.2.1
  have hreach : reached t.start t.steps = t.endpoint := hvalid.2.2.2
  exact stepsOk_sound t.steps t.start t.endpoint hok hreach

end CollatzResearch
