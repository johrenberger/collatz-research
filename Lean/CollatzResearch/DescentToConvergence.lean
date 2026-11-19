import CollatzResearch.Basic
import CollatzResearch.CoverageTree
import CollatzResearch.DescentWitness
import CollatzResearch.StandardMapBridge

/-!
# The descent-to-convergence reduction (story R03)

Story R03 asks for the remaining mathematical obligation to be a precise
strict-descent proposition rather than a vague missing leaf certificate. Its
target premise is:

> **Target premise.** For every odd `n > 1` there is `k > 0` with
> `0 < trajectory n k < n`.

This module states that premise, proves the reduction from it to convergence,
proves the converse on the odd domain, and records the dependency graph.

**The premise is not proved here.** It is `UniversalOddDescent` below, an
open obligation: it is a `def`, not an `axiom`, and every result that
depends on it takes it as an explicit hypothesis, so the dependency stays
visible in the statement of each result. Nothing in this module turns the
premise into a proof, and nothing here claims Collatz convergence.

## Declarations

- `EventuallyDescends n`: the strict-descent predicate for one input: a
  positive-length accelerated trajectory that ends at a positive value
  strictly below `n`.
- `UniversalOddDescent`: the universal odd-domain descent premise. **OPEN.**
- `reaches_one_of_descent_step`: the strong-induction step.
- `odd_reaches_one_of_universal_descent`: the strong-induction reduction,
  by strong induction on the input.
- `universal_standard_convergence_of_universal_odd_descent`: the same
  reduction composed with the R02 standard-map bridge.
- `eventually_descends_of_reaches_one`: the converse on the odd domain:
  convergence implies eventual strict descent for `n > 1`.

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

**Trust boundary.** No `sorry`, no `admit`, no `axiom`, no `native_decide`,
no FFI. Every result is kernel-checked, and `UniversalOddDescent` is always a
hypothesis, never a proof.
-/

namespace CollatzResearch

/-- **Eventual strict descent on the accelerated map.**

For an input `n`, the accelerated trajectory from `n` reaches a strictly
smaller positive value in a positive number of steps.

The three conjuncts are exactly the three obligations the story names:

1. `0 < k` — the descent has **positive length**; the zero-step witness
   `trajectory n 0 = n` is not a descent.
2. `0 < trajectory n k` — the endpoint is **positive**, so the trajectory has
   not fallen out of the positive domain.
3. `trajectory n k < n` — the endpoint is **strictly below** the start; an
   equal endpoint is not a descent.

The map is the accelerated map of `CollatzResearch.Basic`, so this predicate
is meaningful on the odd domain; on an even input the accelerated map is not
the Collatz map (see `CollatzResearch.StandardMapBridge`). -/
def EventuallyDescends (n : Nat) : Prop :=
  ∃ k, 0 < k ∧ 0 < trajectory n k ∧ trajectory n k < n

/-- **The universal odd-domain descent premise. OPEN.**

For every odd `n > 1`, the accelerated trajectory from `n` reaches a
strictly smaller positive value in a positive number of steps.

**This is the open obligation of story R03, and it is not proved.** It is
declared as a `def`, not an `axiom`, so it contributes no trusted
assumption to any result: every theorem below that uses it takes it as an
explicit hypothesis, and the theorems are therefore conditional statements
about the premise rather than claims that the premise holds. Nothing in this
repository discharges it, and no certificate, leaf structure, or default
field is allowed to carry it.

See `docs/story-r03-descent-to-convergence.md` for the dependency graph and
the obligation ledger. -/
def UniversalOddDescent : Prop :=
  ∀ n, Odd n → 1 < n → EventuallyDescends n

/-- **The strong-induction step of the descent-to-convergence reduction.**

Suppose `n` is odd and strictly descends, and suppose every smaller odd
positive input already reaches one. Then `n` reaches one.

The step consumes the odd-domain closure of the accelerated trajectory: the
descent endpoint `trajectory n k` is odd (`DescentWitness.trajectory_odd`),
so the induction hypothesis applies to it, and orbit composition
(`CoverageTree.accelerated_orbit_compose`) carries the witness on `n` back
to the smaller endpoint.

**Proof.** Take the descent witness `k` and the oddness of its endpoint, apply
the induction hypothesis to that endpoint, and compose the two orbit
segments. The bridge `trajectory_eq_accelerated_orbit` identifies the
accelerated trajectory with the accelerated orbit used by `ReachesOne`. -/
theorem reaches_one_of_descent_step {n : Nat} (hOdd : Odd n)
    (hDesc : EventuallyDescends n)
    (hRec : ∀ m, Odd m → 0 < m → m < n → ReachesOne m) : ReachesOne n := by
  obtain ⟨k, _hkLen, hkEndPos, hkEndLt⟩ := hDesc
  have hOddEnd : Odd (trajectory n k) := DescentWitness.trajectory_odd n k hOdd
  obtain ⟨k', hk'⟩ := hRec (trajectory n k) hOddEnd hkEndPos hkEndLt
  have hOrbit : accelerated_orbit n k = trajectory n k :=
    (trajectory_eq_accelerated_orbit n k).symm
  refine ⟨k + k', ?_⟩
  rw [accelerated_orbit_compose, hOrbit, hk']

/-- **The descent-to-convergence reduction: universal odd descent implies
universal odd convergence.**

If every odd `n > 1` strictly descends (the open premise
`UniversalOddDescent`), then every positive odd input reaches one under the
accelerated map.

**Proof.** Strong induction on the input. The base case `n = 1` is terminal
(`accelerated_orbit 1 0 = 1`). In the step, `n > 1` is odd, so the premise
supplies a positive-length descent to a strictly smaller positive endpoint;
that endpoint is odd by oddness preservation, so the induction hypothesis
applies to it and yields a reachability witness, which is composed back onto
`n` by orbit composition.

**This is conditional.** The premise `UniversalOddDescent` is the open
obligation of story R03 and is not established anywhere in this repository.
The theorem says what follows *if* it holds; it does not assert it. -/
theorem odd_reaches_one_of_universal_descent (H : UniversalOddDescent) :
    ∀ n, Odd n → 0 < n → ReachesOne n := by
  intro n
  refine Nat.strongRecOn (motive := fun n => Odd n → 0 < n → ReachesOne n) n ?_
  intro n ih hOdd hPos
  by_cases hOne : n = 1
  · subst hOne
    exact ⟨0, accelerated_orbit_zero 1⟩
  · have hGt : 1 < n := by omega
    exact reaches_one_of_descent_step hOdd (H n hOdd hGt)
      (fun m hmOdd hmPos hmLt => ih m hmLt hmOdd hmPos)

/-- **The descent-to-convergence reduction composed with the R02 standard-map
bridge.**

If every odd `n > 1` strictly descends (the open premise
`UniversalOddDescent`), then every positive input reaches one under the
standard Collatz map.

**Proof.** Apply the R02 bridge
`universal_standard_convergence_of_universal_odd_convergence`, whose
hypothesis is exactly the odd-domain convergence conclusion of
`odd_reaches_one_of_universal_descent`.

**This is conditional on the open premise**, exactly as the R02 bridge is
conditional on the odd-domain convergence obligation. -/
theorem universal_standard_convergence_of_universal_odd_descent
    (H : UniversalOddDescent) : ∀ n, 0 < n → StandardReachesOne n := by
  intro n hn
  exact universal_standard_convergence_of_universal_odd_convergence
    (fun m hmOdd hmPos => odd_reaches_one_of_universal_descent H m hmOdd hmPos)
    n hn

/-- **Converse on the odd domain: convergence implies eventual strict
descent.**

For an odd `n > 1`, if the accelerated orbit reaches one, then `n`
eventually strictly descends.

**Proof.** Take the reachability witness `k`. It is positive, because
`accelerated_orbit n 0 = n ≠ 1` when `n > 1`. The endpoint is
`trajectory n k = 1`, which is positive and strictly below `n`. The
endpoint is odd by oddness preservation, so the descent lands back in the odd
domain.

**Why this direction matters.** It shows the open premise
`UniversalOddDescent` is not a weaker-looking surrogate for the Collatz
statement: on the odd domain, descent and convergence are equivalent, so the
residual obligation is exactly the classical one, written as a strict
descent. -/
theorem eventually_descends_of_reaches_one {n : Nat} (hOdd : Odd n) (hGt : 1 < n)
    (h : ReachesOne n) :
    ∃ k, 0 < k ∧ 0 < trajectory n k ∧ trajectory n k < n ∧ Odd (trajectory n k) := by
  obtain ⟨k, hk⟩ := h
  have hkPos : 0 < k := by
    by_contra hkNot
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hkNot
    subst hkZero
    rw [accelerated_orbit_zero] at hk
    omega
  have hOddEnd : Odd (trajectory n k) := DescentWitness.trajectory_odd n k hOdd
  refine ⟨k, hkPos, ?_, ?_, hOddEnd⟩
  · rw [trajectory_eq_accelerated_orbit, hk]
    decide
  · rw [trajectory_eq_accelerated_orbit, hk]
    exact hGt

end CollatzResearch

