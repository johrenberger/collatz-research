# Story R03 — the descent-to-convergence reduction

**Status:** implemented as a conditional reduction. The universal descent
premise is **OPEN** and is not discharged here.

Source: `docs/collatz-next-stories.md`, section "R03 — Prove the
descent-to-convergence reduction".

## The exact proposition

Story R03 names the target premise as:

> for every odd `n > 1` there is `k > 0` with `0 < trajectory n k < n`.

R03 formalizes this as two declarations in
`Lean/CollatzResearch/DescentToConvergence.lean`:

- `EventuallyDescends n` — the per-input predicate
  `∃ k, 0 < k ∧ 0 < trajectory n k ∧ trajectory n k < n`. The three conjuncts
  are the three obligations the story names separately: **positive length**,
  **positive endpoint**, **strict inequality**. A zero-step witness
  (`trajectory n 0 = n`) and an equal-endpoint witness are therefore excluded
  by construction, not by convention.
- `UniversalOddDescent` — the universal premise
  `∀ n, Odd n → 1 < n → EventuallyDescends n`.

**`UniversalOddDescent` is a `def`, not an `axiom`.** It contributes no
trusted assumption to any result: every theorem that depends on it takes it
as an explicit hypothesis, so each conclusion is visibly conditional. No
certificate, leaf structure, or default field carries it.

## The domain

- **Map:** the accelerated map `CollatzResearch.Basic.acceleratedStep`, which
  is meaningful only on the odd domain. `EventuallyDescends` therefore
  quantifies over accelerated trajectories, and the universal premise is
  stated for odd `n`.
- **Excluded:** `n = 0` (the accelerated map is not the Collatz map there),
  `n = 1` (terminal base case, not a strict-descent case), and even inputs.
- **Positive odd inputs `n > 1`:** the domain of the open obligation.

## The theorems

| Declaration | Statement |
| --- | --- |
| `reaches_one_of_descent_step` | The strong-induction step: an odd `n` that strictly descends, plus the induction hypothesis for every smaller odd positive input, gives `ReachesOne n`. |
| `odd_reaches_one_of_universal_descent` | Strong induction on the input: `UniversalOddDescent` implies `∀ n, Odd n → 0 < n → ReachesOne n`. |
| `universal_standard_convergence_of_universal_odd_descent` | Composed with R02: `UniversalOddDescent` implies `∀ n, 0 < n → StandardReachesOne n`. |
| `eventually_descends_of_reaches_one` | The converse on the odd domain: for odd `n > 1`, `ReachesOne n` implies eventual strict descent. |

The converse matters for the story's stated purpose: it makes the residual
obligation mathematically precise rather than apparently weaker than Collatz.
Universally quantified over odd `n > 1`, eventual strict descent is equivalent
to reachability of one (with `n = 1` handled as the terminal base case). The
forward implication is the strong-induction theorem above; the converse is
`eventually_descends_of_reaches_one`. Thus the open premise is exactly the
classical statement written as a strict descent.

## Dependency graph

```
Basic.trajectory, Basic.acceleratedStep
  └── DescentWitness.trajectory_odd            (oddness preservation)
        ├── reaches_one_of_descent_step
        │     ├── CoverageTree.accelerated_orbit_compose       (orbit composition)
        │     └── StandardMapBridge.trajectory_eq_accelerated_orbit
        │           └── odd_reaches_one_of_universal_descent
        │                 └── universal_standard_convergence_of_universal_odd_descent
        │                       └── StandardMapBridge.universal_standard_convergence_of_universal_odd_convergence (R02)
        └── eventually_descends_of_reaches_one
              └── CoverageTree.ReachesOne, CoverageTree.accelerated_orbit_zero
```

Every edge is an existing, checked result. R03 adds no new dependency on the
standard map and does not re-derive anything R02 established.

## Obligation ledger

| Obligation | Status |
| --- | --- |
| `EventuallyDescends` with explicit positive length, positive endpoint, strict inequality | Discharged (definition) |
| Strong induction: universal odd descent ⇒ odd-input reachability of one | Discharged (conditional on `UniversalOddDescent`) |
| Composition with R02 ⇒ standard positive-input convergence | Discharged (conditional on `UniversalOddDescent`) |
| Converse on the odd domain: convergence ⇒ eventual descent for `n > 1` | Discharged |
| Dependency graph recorded, universal descent premise labelled OPEN | Discharged (this document, plus the module docstring and `docs/theorem-status.md`) |
| **Prove `UniversalOddDescent`** | **OPEN.** Not attempted; not assumed; not smuggled into a certificate. |

## Validation

Covered in `Lean/CollatzResearch/DescentToConvergenceTests.lean`:

- `n = 1` is the terminal base case, not a strict-descent case
  (`not_eventually_descends_one`), while the orbit of 1 is 1
  (`terminal_base_reaches_one`).
- A zero-step witness cannot satisfy descent (`zero_step_is_not_descent`) and
  an equal-endpoint witness cannot satisfy descent
  (`equal_endpoint_is_not_descent`).
- The descent endpoint stays positive and odd, which is what the induction
  consumes at every inductive call (`descent_endpoint_stays_odd`).
- The generic step theorem applies to a concrete input under an assumed
  descent hypothesis (`reaches_one_three_of_descent`): the descent hypothesis
  at 3 is assumed, not proved, and the induction hypothesis is discharged for
  every smaller odd positive input. No example discharges an orbit equation
  with `native_decide` (ADR 0009).

## Trust boundary

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no FFI, no
external process. The conditional theorems rest on the approved standard
axiom set only; the transitive-axiom manifest records them.

## Non-goal

Claiming the universal premise has been established. Nothing in this change
does, and the premise remains the open research obligation.
