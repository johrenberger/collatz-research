# Story R05 — the obstruction to fixed-depth universal descent

## The problem this closes

The repository represents trajectories by finite prefixes and tries to
certify descent by exhibiting a bounded witness: a list of steps that
reaches a smaller value. That strategy has a limit, and R05 makes the limit
explicit and provable.

A **fixed-depth** strategy would assert that some constant `L` bounds the
first strict descent of every positive odd input. R05 proves that no such
`L` exists — not merely that some input escapes a particular `L`, but that
for every `L` and every *finite* set of exceptional inputs, some input
outside that set still escapes. A bound cannot be rescued by excepting a
handful of cases.

This is a **negative** result. It does not settle the Collatz conjecture and
it does not settle the descent obligation: the ascent family does descend
eventually, just not within a bounded number of steps.

## The ascent family

For `K >= 1` let `n = 2^(K+1) - 1`. The odd trajectory from `n` ascends:

```
trajectory n j + 1 = 3^j * 2^(K+1-j)        for 0 <= j <= K
```

so equivalently `trajectory n j = 3^j * 2^(K+1-j) - 1`. The first few:

| K | n | trajectory values |
|---|---|---|
| 1 | 3 | 3 -> 5 |
| 2 | 7 | 7 -> 11 -> 17 |
| 3 | 15 | 15 -> 23 -> 35 -> 53 |

Every one of these values is *above* the start, so no `k <= K` witnesses a
descent.

The mechanism is simple: each of the first `K` transitions has two-adic
valuation exactly one, so every step is a single halving of `3x + 1` and
the recurrence unrolls exactly.

## The exact propositions

### The start is a positive odd input

`ascentStart_odd : Odd (ascentStart K)` and
`ascentStart_gt_one : 1 ≤ K → 1 < ascentStart K`.

### Each of the first K transitions has valuation one

`ascent_valuation_one : j + 1 ≤ K → twoAdicValuation (3 * trajectory (ascentStart K) j + 1) = 1`.

### The closed form

Two statements, because the story's identity involves natural subtraction
and that subtraction must not be silently truncated:

- `trajectory_ascentFormula : trajectory (ascentStart K) j + 1 = 3^j * 2^(K+1-j)`,
  the subtraction-free form. Every quantity here is a product, so no
  truncation can occur. This is the statement the induction actually proves.
- `trajectory_ascentFormula_sub : 0 < 3^j * 2^(K+1-j) → trajectory (ascentStart K) j = 3^j * 2^(K+1-j) - 1`,
  the subtraction form the story states, with the side condition explicit.

`ascentFormula_side` discharges that side condition, and
`trajectory_ascentFormula_sub_uncond` packages the pair.

### Ascent

`ascentValue_gt_start : 1 ≤ j → j ≤ K → trajectory (ascentStart K) j > ascentStart K`.

Since a descent witness needs `trajectory n k < n`, no `k <= K` can
witness a descent: `ascent_no_descent_within` states that directly.

### The obstruction

- `no_fixed_depth_descent_bound : ∀ L, ∃ n, Odd n ∧ 1 < n ∧ ¬ EventuallyDescendsWithin L n`.
- `no_fixed_depth_descent_bound_except_finite : ∀ L E, E.Finite → ∃ n, Odd n ∧ 1 < n ∧ n ∉ E ∧ ¬ EventuallyDescendsWithin L n`.

`EventuallyDescendsWithin L n` is the bounded-depth predicate: some
positive `k <= L` reaches a strictly smaller positive value. It is weaker
than R03's `EventuallyDescends`, which puts no bound on `k`; the bridge
`EventuallyDescendsWithin.of_descends` records that direction, so the
obstruction is exactly about *bounded* descent and nothing stronger.

## The architectural consequence

**A finite list of explicit fixed-length descent words cannot cover the
full domain.** The depth of the first descent is unbounded, and excluding
finitely many exceptional inputs does not restore a bound.

This constrains future coverage stories: an approach that enumerates
fixed-length descent words will not terminate on the whole domain, and no
finite patch list repairs that. Parameterized proofs, recursion, and other
ranking measures remain possible, and nothing here rules them out — the
obstruction is about *fixed depth*, not about descent itself.

## Trust boundary

**This story proves no convergence, no descent, and no cycle exclusion.**

The universal descent premise of R03 (`UniversalOddDescent`) remains
**OPEN**. This module does not assume it, refute it, or weaken it, and it
is consistent with that premise holding: the ascent family descends
eventually, just not within a bounded number of steps.

No `sorry`, no `admit`, no `axiom`, and no `native_decide`. The
two-adic valuation is never *evaluated*: the proofs use the Mathlib
factorization lemmas symbolically (`Nat.factorization_mul`,
`Nat.factorization_pow_self`, `Nat.factorization_eq_zero_of_not_dvd`),
exactly as R04 does.

## Files

| File | Role |
|---|---|
| `Lean/CollatzResearch/FixedDepthDescent.lean` | the ascent family, the closed form, and the obstruction |
| `Lean/CollatzResearch/FixedDepthDescentTests.lean` | the concrete `L = 1, 2, 3` examples and the obstruction regressions |

## The valuation lemma comes from R04

R05 needs exactly one fact about the two-adic valuation: from
`3 * n + 1 = 2 ^ k * m` with `Odd m`, the valuation of `3 * n + 1` is `k`.
That is R04's `twoAdicValuation_of_odd_factorization` in
`CollatzResearch.ArithmeticWitness`, and its shape matches the shape used
here exactly, so R05 **imports and reuses** it rather than restating it.
The arithmetic-to-step bridge is therefore proved once, in R04.

This module was originally developed against a `main` that predated R04,
where the lemma had to be restated locally. When R04 merged (PR #133,
commit `3724b31`) the local restatement was dropped in favour of R04's
lemma, and this note records the change so a reviewer can see that the
dependency is deliberate.
