# Story R04 — arithmetic step witnesses without native evaluation

**Status:** implemented. Every concrete result is kernel-checked and free of
native-evaluation axioms.

Source: `docs/collatz-next-stories.md`, section "R04 — Verify arithmetic step
witnesses without native evaluation".

## The problem this closes

`CollatzResearch.Basic.acceleratedStep` computes the odd part of `3n + 1`
through `Nat.factorization`. A result that merely *evaluates* an orbit
equation therefore leans on that computation, and checking such an equation
with `native_decide` is worse: it makes the result compiler-dependent, which
the transitive axiom audit (R01, ADR 0013) classifies as a
`compiler_dependent_instance`.

The R04 route is the opposite one. A producer supplies **raw numbers** — the
exponent `k` and the successor `m` of a step — and Lean checks the
arithmetic equation `3 * n + 1 = 2 ^ k * m` with ordinary kernel-checked
arithmetic. The module then proves **once** that the equation determines the
canonical accelerated step.

## The exact propositions

### The generic arithmetic-to-step bridge

`Lean/CollatzResearch/ArithmeticWitness.lean` proves:

- `twoAdicValuation_of_odd_factorization (n k m)` — from
  `3 * n + 1 = 2 ^ k * m` and `Odd m`, `twoAdicValuation (3 * n + 1) = k`.
- `acceleratedStep_of_odd_factorization (n k m)` — from the same hypotheses,
  `acceleratedStep n = m`.
- `odd_of_two_pow_mul_odd (n k m)` — from `3 * n + 1 = 2 ^ k * m` and
  `1 ≤ k`, `Odd n`. The odd-domain precondition of the accelerated map is
  *implied* by the witness format, not merely assumed.
- `standardTrajectory_of_odd_factorization (n k m)` — the standard map
  reaches `m` after exactly `1 + k` standard steps. This reuses the R02
  bridge (`acceleratedStep_equiv_standardStep`) rather than defining a second
  accelerated map.

**All positivity and oddness hypotheses are explicit.** The proofs use
Mathlib's factorization *lemmas* symbolically (`Nat.factorization_mul`,
`Nat.factorization_pow_self`, `Nat.factorization_eq_zero_of_not_dvd`); the
valuation is never evaluated, and no `native_decide` appears.

### The total finite-trace checker

`StepWitness` carries raw data only (`exponent`, `successor`). `TraceWitness`
carries the start, the list of transitions, and the claimed endpoint.

The checkers are **total** Boolean functions over raw numeric data:

- `stepOk x s` — checks `0 < x`, `x % 2 = 1`, `1 ≤ s.exponent`,
  `0 < s.successor`, `s.successor % 2 = 1`, and
  `3 * x + 1 = 2 ^ s.exponent * s.successor`.
- `stepsOk x steps` — threads the current value through the transitions.
- `traceOk t` — checks the start, every transition, and the endpoint.

**The endpoint is checked against the transitions, not carried as a proof
field.** The producer supplies `t.endpoint`; the checker recomputes
`reached t.start t.steps` from the transition data alone and compares.

The soundness theorems:

- `stepsOk_sound` — acceptance implies `trajectory x steps.length = e` where
  `e` is the value the transitions reach.
- `traceOk_sound` — acceptance of a whole trace implies
  `trajectory t.start t.steps.length = t.endpoint`.

`traceOk_sound` is the public theorem: the endpoint is **derived** from the
transitions, never supplied by the producer.

## The concrete traces

`Lean/CollatzResearch/ArithmeticWitnessTraces.lean` is **generated** by
`scripts/generate_arithmetic_traces.py` from the untrusted Python reference
arithmetic. The generator is deterministic; `--check` mode verifies that the
committed file is current, and `tests/test_arithmetic_trace.py` asserts that
regeneration reproduces it byte for byte.

- `traceThreeFiveOne` — the odd trajectory `3 → 5 → 1`, two accelerated
  steps, exponents `⟨1, 5⟩` and `⟨4, 1⟩`.
- `traceTwentySeven` — the trajectory from `27`, 41 accelerated steps to
  `1`.

Every one of those 41 steps is re-checked by the Lean kernel. The generator
contributes data, never a proof.

## The zero-step trace for input 1

**The zero-step trace is represented by an empty step list.** The trace
starts at `1`, takes no steps, and therefore reaches its start:

```lean
def traceOne : TraceWitness :=
  { start := 1, steps := [], endpoint := 1 }
```

The endpoint field still carries the claimed value `1`, and the checker
compares it against the value the transitions reach. `stepsOk` returns
`true` for the empty list, and `traceOk_sound` yields
`trajectory 1 0 = 1`.

## Rejection tests

`Lean/CollatzResearch/ArithmeticWitnessTests.lean` pins every malformed
case the story names. Each is rejected by the checker, not by convention:

| Case | Fixture | Why it is rejected |
|---|---|---|
| Altered exponent | `traceThreeFiveOneAlteredExponent` | `⟨2, 5⟩` would need `3 * 3 + 1 = 4 * 5`, false |
| Non-odd successor | `traceNonOddSuccessor` | `⟨1, 8⟩` satisfies the equation but the successor is even |
| Incorrect arithmetic equation | `traceWrongEquation` | `⟨1, 6⟩` would need `3 * 3 + 1 = 2 * 6`, false |
| Empty required trace | `traceEmptyRequired` | no steps, but the endpoint claims `1` and the transitions reach `3` |
| Wrong start | `traceWrongStart` | `⟨1, 41⟩` from `3` would need `3 * 3 + 1 = 2 * 41`, false |
| Wrong endpoint | `traceWrongEndpoint` | the transitions are all correct and reach `1`, but the endpoint claims `5` |
| Even start | `traceEvenStart` | the accelerated map is meaningful only on the odd domain |

The wrong-endpoint case is the one that shows the endpoint is *checked*
rather than trusted: every transition is individually correct, and only the
endpoint field is wrong.

## The even start, through the R02 bridge

The accelerated map is only meaningful on the odd domain, so an even start
is handled on the standard map. `even_start_six_odd_part` establishes that the
odd part of `6` is `3` (`6 = 2 ^ a * q` with `q` odd forces `a = 1`, `q = 3`),
and `even_start_six_reaches_one` then composes the R02 normalization
(`exists_odd_normalization`) with the existing transport theorem
(`acceleratedTrajectory_reaches_one_implies_standard`) and the accepted odd
trace `3 → 5 → 1`. No second accelerated map is introduced.

## The generic theorems are exercised

The concrete tests apply the exported generic theorems rather than
restating their conclusions: `traceThreeFiveOne_endpoint` is
`traceOk_sound` applied to the accepted trace, and
`generic_bridge_applies_three` is the generic arithmetic-to-step bridge
applied to the concrete step `⟨1, 5⟩`.

## Trust boundary

**This story proves no convergence, no descent, and no cycle exclusion.** It
certifies *finite* trajectories only, on the odd domain. The standard-map
side is reached through the R02 bridge, never by re-implementing the
standard map.

No `sorry`, no `admit`, no `axiom`, and no `native_decide` was introduced.
The concrete acceptance checks use `decide`, which reduces in the Lean
kernel and therefore adds no compiler-evaluated axiom.

The Python side (`python/collatz_research/arithmetic_trace.py`) is untrusted
proposal machinery in the sense of ADR 0003: it may propose, Lean disposes.
No Python result is consumed as a Lean hypothesis.

The producer's step limit bounds how many accelerated steps a trace may take:
a trace that reaches 1 within that many steps is accepted, including the
zero-step trace from 1 when no step is permitted. A limit that is reached
without hitting 1 raises, which is an unknown outcome and never a claim that
the trajectory does not converge.

## Non-goals honoured

- Million-input verification is **not** attempted; the checker is a bounded
  finite-trace checker.
- The retired v1 digest-based Lean acceptance bridge is **not** revived.
  Hashes establish artifact identity, not arithmetic soundness; nothing here
  uses a digest.

## Files

| File | Role |
|---|---|
| `Lean/CollatzResearch/ArithmeticWitness.lean` | the generic bridge and the total checker |
| `Lean/CollatzResearch/ArithmeticWitnessTraces.lean` | generated concrete trace fixtures |
| `Lean/CollatzResearch/ArithmeticWitnessTests.lean` | acceptance and rejection regression tests |
| `python/collatz_research/arithmetic_trace.py` | the untrusted trace producer |
| `scripts/generate_arithmetic_traces.py` | the deterministic fixture generator |
| `tests/test_arithmetic_trace.py` | producer and reproducibility tests |