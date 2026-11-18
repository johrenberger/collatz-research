import CollatzResearch.Basic
import CollatzResearch.Dynamics
import CollatzResearch.Equivalence
import CollatzResearch.CoverageTree

/-!
# Standard-map reachability: the boundary between the odd-domain accelerated
# map and the standard Collatz map

Story R02 makes the standard-Collatz theorem boundary explicit. The accelerated
map `T` (`CollatzResearch.Basic.acceleratedStep`) is defined only on the odd
domain, while the standard map `C` (`CollatzResearch.Dynamics.standardStep`)
is defined on every natural number. The two agree on the odd domain but
diverge elsewhere, so a statement about the Collatz theorem is ambiguous
until the domain is written down.

This module supplies the pieces that make the boundary explicit:

- `trajectory_eq_accelerated_orbit`: the two accelerated-iteration definitions
  (`CollatzResearch.Basic.trajectory` and
  `CollatzResearch.CoverageTree.accelerated_orbit`) are the same function, so
  callers of either name agree.
- `StandardReachesOne`: standard-map reachability, kept distinct from the
  totalized accelerated predicate `CollatzResearch.CoverageTree.ReachesOne`.
- `exists_odd_normalization`: for every positive `n` there is an odd positive `q`
  and `a` with `n = 2 ^ a * q`, and the standard trajectory reaches `q` after
  exactly `a` halvings.
- `universal_standard_convergence_of_universal_odd_convergence`: the bridge
  theorem. Universal convergence on the positive odd domain, in the accelerated
  map, implies universal convergence on the positive domain, in the standard map.

**No convergence claim.** The bridge is a conditional re-statement: it says the
standard-map statement follows from the odd-domain accelerated statement, not
that either holds. The odd-domain premise remains an open obligation. This
module proves no descent, no termination, and no cycle exclusion, and it
introduces no `sorry`, `admit`, or `axiom`.

The domain boundary is sharp, and the companion test module records it:
`acceleratedStep 0 = 1` while `standardStep 0 = 0`, and `acceleratedStep 2 = 7`
while `standardStep 2 = 1`. The accelerated map is only meaningful when the
caller supplies the odd-domain invariant; at an even input it computes the odd
part of `3n + 1` and has nothing to do with the standard map's halving.
-/

namespace CollatzResearch

/-- **Compatibility of the two accelerated-iteration definitions.**

`trajectory` (in `CollatzResearch.Basic`) and `accelerated_orbit` (in
`CollatzResearch.CoverageTree`) each iterate `acceleratedStep`; they differ
only in how the recursion is written down. This theorem makes them the same
function, so a result stated for one is a result for the other.

Both are stated for every `n` and `k`, with no oddness hypothesis: the
compatibility is about the iteration itself, not about the map being
mathematically meaningful there.

**Proof.** Induction on `k`, generalizing over `n`. The zero case is `rfl` for
both definitions; the step rewrites each side with its own successor equation
and applies the induction hypothesis.
-/
theorem trajectory_eq_accelerated_orbit (n k : Nat) :
    trajectory n k = accelerated_orbit n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [trajectory_succ, accelerated_orbit_succ, ih]

/-- **Standard-map reachability**: some finite standard trajectory from `n`
reaches 1.

This is the standard map's own reachability predicate and is deliberately
distinct from `CollatzResearch.CoverageTree.ReachesOne`, which is the
accelerated map's predicate and is totalized over all natural numbers. The two
differ in both the map and the domain: `ReachesOne` says the accelerated
orbit reaches 1, `StandardReachesOne` says the standard trajectory does.

Because `ReachesOne` quantifies over an accelerated orbit that is only
meaningful on the odd domain, it cannot be read as the standard-map statement
at an even input. `StandardReachesOne` has no such ambiguity.
-/
def StandardReachesOne (n : Nat) : Prop := ∃ k, standardTrajectory n k = 1

/-- **Odd-part normalization of a positive input.**

For every positive `n` there are `a` and `q` with `q` odd and positive,
`n = 2 ^ a * q`, and `standardTrajectory n a = q`: the standard trajectory
halves `n` exactly `a` times and lands on its odd part.

This is the statement that makes the boundary explicit. The odd part `q` is the
point where the accelerated map's odd-domain invariant holds, so the two maps
coincide from `q` onward; before it, the standard map is halving while the
accelerated map is not defined as a map of the same thing.

**Proof.** `Nat.exists_eq_two_pow_mul_odd` splits `n` into its power of two
and its odd part. The odd part is positive because `n` is positive and the
power of two is. The standard trajectory is then pinned by
`standardTrajectory_pow_div`: `2 ^ a` divides `n`, so `standardTrajectory n a`
is `n / 2 ^ a`, which is `q`.
-/
theorem exists_odd_normalization (n : Nat) (hn : 0 < n) :
    ∃ a q : Nat, Odd q ∧ 0 < q ∧ n = 2 ^ a * q ∧ standardTrajectory n a = q := by
  obtain ⟨a, q, hq_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hn)
  have hq_pos : 0 < q := by
    have hprod : 0 < 2 ^ a * q := by
      rw [← hn_eq]
      exact hn
    exact Nat.pos_of_mul_pos_left hprod
  refine ⟨a, q, hq_odd, hq_pos, hn_eq, ?_⟩
  have hdiv : 2 ^ a ∣ n := ⟨q, hn_eq⟩
  rw [standardTrajectory_pow_div n a hdiv, hn_eq]
  exact Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 2))

/-- **The bridge theorem: odd-domain accelerated convergence implies
standard-map convergence on the positive domain.**

If every positive odd `n` has an accelerated orbit reaching 1, then every
positive `n` has a standard trajectory reaching 1.

This is the boundary statement R02 asks for. The premise is the
odd-domain accelerated claim; the conclusion is the standard-map claim for
every positive input. It is a conditional re-statement of one domain in the
terms of another, and it asserts neither convergence.

**Proof.** Normalize `n` into its power of two and odd part (`q`, odd and
positive). The hypothesis applies to `q`, so `q` has an accelerated orbit
reaching 1; `trajectory_eq_accelerated_orbit` converts that to a `trajectory`
witness, and the existing transport theorem
`acceleratedTrajectory_reaches_one_implies_standard` lifts it to a standard
trajectory from `q` reaching 1. Composing that trajectory with the `a`
halvings that reach `q` gives a standard trajectory from `n` reaching 1.
-/
theorem universal_standard_convergence_of_universal_odd_convergence
    (H : ∀ n : Nat, Odd n → 0 < n → ReachesOne n)
    (n : Nat) (hn : 0 < n) : StandardReachesOne n := by
  obtain ⟨a, q, hq_odd, hq_pos, hn_eq, hstd⟩ := exists_odd_normalization n hn
  obtain ⟨m, hm⟩ := H q hq_odd hq_pos
  have htraj : trajectory q m = 1 := by
    rw [trajectory_eq_accelerated_orbit]
    exact hm
  obtain ⟨m', hstd'⟩ := acceleratedTrajectory_reaches_one_implies_standard q m hq_odd htraj
  refine ⟨a + m', ?_⟩
  rw [← standardTrajectory_compose n a m']
  rw [hstd]
  exact hstd'

end CollatzResearch
