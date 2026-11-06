/-
Reachability evidence tier (ADR 0009) — CI-side executable spec for the
tier decision recorded in `docs/adr/0009-reachability-evidence-tier.md`.

WP-CF-2 of the NT-5 convergence-frontier plan (`docs/convergence-frontier.md`
§ 8) requires a regression covering the claim shapes that the tier
distinguishes:

- `.empty`       — holds no orbit state, so it carries no witness at all.
- `.singleton 1` — the canonical terminal-value-1 shape: `Holds` reduces
                    to `y = 1`, so `ReachesOne` is kernel-checkable at
                    `k := 0` with no orbit evaluation.
- `.singleton n` — for `n != 1`, `Holds` reduces to `y = n`, so the
                    terminal-value-1 path does not apply and the tier
                    supplies no unconditional reachability witness.
- `.bounded K`   — `Holds` reduces to `y ≤ K`, which admits `y = 0`, so
                    the terminal-value-1 path does not apply either.
- `.interval`    — excluded from `FiniteOrbitClaim` by construction.

**What this module does NOT assert.** The negative scenarios below are
statements about the *shape* of a claim's `Holds` predicate, not about
the arithmetic of the Collatz orbit. Scenarios 3 and 4 say "this claim
shape does not reduce to `y = 1`", which is why the ADR 0009 tier does
not supply a witness for it; they do NOT say that the mentioned values
fail to reach 1. Nothing here asserts or denies convergence.

**Trust role of `native_decide`.** None. Every example below is a
kernel-checked term; `native_decide` is not used anywhere in this
module, because under the ADR 0009 tier a reachability conclusion may
never be discharged by the compiler-evaluated `native_decide` axiom.
The tier leaves `native_decide` admissible for data-side obligations
only.

Per project discipline (MEMORY.md, "BDD Discipline (Lean vs Python)"),
Lean validation is CI-only; this module does not enter any local BDD
gate. All `example` blocks are compile-checked by `lake build` in
GitHub CI.
-/

import CollatzResearch.CoverageTree
import CollatzResearch.Q5Integration

namespace CollatzResearch

/-- The ADR 0009 tier predicate on a claim shape: every orbit state the
    claim holds is `1`. Only a claim whose `Holds` reduces to `y = 1`
    carries an unconditional, kernel-checkable reachability witness. -/
private def TerminalValueOne (c : FiniteOrbitClaim) : Prop :=
  ∀ y, c.Holds y → y = 1

/-- Scenario 1: `.empty` holds no orbit state, so no reachability
    witness exists for it — there is no `y` to witness. -/
example : ∀ y, (FiniteOrbitClaim.empty).Holds y → False := by
  intro y hy
  change False at hy
  exact hy

/-- Scenario 2: `.singleton 1` is the canonical terminal-value-1 claim.
    Its `Holds` reduces to `y = 1`, so the reachability conclusion
    `ReachesOne y` is obtained by rewriting and closing the orbit at
    `k := 0` with `accelerated_orbit_zero` (an `rfl` lemma). No orbit
    equation is evaluated and no `native_decide` is used. -/
example : ∀ y, (FiniteOrbitClaim.singleton 1).Holds y → ReachesOne y := by
  intro y hy
  change y = 1 at hy
  subst hy
  exact ⟨0, accelerated_orbit_zero 1⟩

/-- Scenario 3: for `n != 1`, `.singleton n` does not reduce to
    `y = 1`. The ADR 0009 tier therefore supplies no unconditional
    reachability witness for this shape: the terminal fact would be
    `accelerated_orbit x k = n`, and continuing that orbit to 1 would
    require evaluating `acceleratedStep`, which is not kernel-reducible.

    This is a statement about the claim *shape* only. It does not assert
    that `n` fails to reach 1. -/
example (n : Nat) (hn : n ≠ 1) :
    ¬ TerminalValueOne (FiniteOrbitClaim.singleton n) := by
  intro h
  have hn' : (FiniteOrbitClaim.singleton n).Holds n := by
    change n = n
    rfl
  have hn1 := h n hn'
  exact hn hn1

/-- Scenario 4: `.bounded K` admits `y = 0`, so it does not reduce to
    `y = 1` and the ADR 0009 tier supplies no unconditional reachability
    witness for it. Shape-level statement only. -/
example (K : Nat) : ¬ TerminalValueOne (FiniteOrbitClaim.bounded K) := by
  intro h
  have h0 : (FiniteOrbitClaim.bounded K).Holds 0 := by
    change 0 ≤ K
    exact Nat.zero_le K
  have h01 := h 0 h0
  omega

/-- Scenario 5: `.interval` is excluded from `FiniteOrbitClaim` by
    construction — the inductive has exactly three constructors. This
    example case-splits over the type, so adding a fourth constructor
    (e.g. `.interval`) breaks it at elaboration time. -/
example : ∀ c : FiniteOrbitClaim,
    c = FiniteOrbitClaim.empty ∨
      (∃ n, c = FiniteOrbitClaim.singleton n) ∨
      (∃ K, c = FiniteOrbitClaim.bounded K) := by
  intro c
  cases c with
  | empty => exact Or.inl rfl
  | singleton n => exact Or.inr (Or.inl ⟨n, rfl⟩)
  | bounded K => exact Or.inr (Or.inr ⟨K, rfl⟩)

/-- Scenario 6: the tier predicate is satisfied by `.singleton 1`, the
    one shape that reduces to `y = 1` and therefore carries an
    unconditional reachability witness. -/
example : TerminalValueOne (FiniteOrbitClaim.singleton 1) := by
  intro y hy
  change y = 1 at hy
  exact hy

/-- Scenario 7: `.empty` satisfies the tier predicate vacuously (it holds
    no value at all). This is why "the claim reduces to `y = 1`" has to
    be paired with "the claim holds something": the tier's witness needs
    a value to witness. -/
example : TerminalValueOne (FiniteOrbitClaim.empty) := by
  intro y hy
  change False at hy
  exact hy.elim

/-- Scenario 8 (API-shape regression): the transport path that keeps the
    reachability conclusion off orbit evaluation.
    `terminal_claim_transport` rewrites the terminal value of an
    accepted witness to `accelerated_orbit x (length - 1)` without
    computing it; `trajectory_index` establishes the per-index equality
    by rewriting with `accelerated_orbit_zero` / `accelerated_orbit_succ`
    (both `rfl`). This example pins the transport signature so a future
    change to that path is caught here, and it carries the same
    "transported, not evaluated" obligation the ADR 0009 tier states. -/
example : ∀ (x : Nat) (w : CertWitness x) (claim : FiniteOrbitClaim)
    (hAnchor : anchorOk x w = true)
    (hTrans : ∀ i, i + 1 < (w.trajectory).length →
                 (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!))
    (hLast : claim.Holds ((w.trajectory)[(w.trajectory).length - 1]!)),
    claim.Holds (accelerated_orbit x ((w.trajectory).length - 1)) :=
  terminal_claim_transport

end CollatzResearch
