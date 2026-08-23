/-
Story Q4 — CI-side executable spec for the bounded-orbit data layer
(`FiniteOrbitClaim` + `IsFiniteClaim : LeafClaim → Prop` +
`BoundedOrbitCertificate`).

These `example` blocks + `def`s are compile-checked by `lake build`
in GitHub CI, not run locally. Per the project-wide rule (MEMORY.md,
"BDD Discipline (Lean vs Python)"), Lean validation is CI-only; this
module does not enter any local BDD gate.

**Scope (Q4 v3 / PR #57).** This file is the regression guard for
the Q4 data layer, parallel to `LeafClaimTests.lean` for Q3 / PR #53+#54
and to `CoverageTreeOrbitTests.lean` for 07c-4 + Q4 / PR #56. It does
NOT cover:
- The companion theorem `coverage_tree_soundness_orbit_cert`
  (PR #58 deliverable)
- The foundation lemmas `accelerated_orbit_compose` +
  `orbit_predecessor_reaches_one` (PR #56 — see
  `CoverageTreeOrbitTests.lean` scenarios 9 + 10)
- Constructive `BoundedOrbitCertificate` construction
  (hypothesis-bearing; requires external Collatz evidence; out of
  scope per Q4 v3 spec — `BoundedOrbitCertificate` cannot be
  constructively inhabited in a closed test without an external
  Collatz oracle; the `.empty` case additionally requires the leaf
  to be unreachable under `descendOrbit`, which is hard to
  construct)

**Trust role of `native_decide`.** Used for closed propositional
equalities on closed `FiniteOrbitClaim` / `LeafClaim` values
(scenarios 1–10). Appropriate as executable-test evidence. Does
NOT contribute to any formal-proof basis (PR #57 is a data-layer
PR; there are no proofs to verify). The executable spec is
regression evidence that the type system + decidability instances
behave as documented.

**API-shape regression (scenario 13).** Performs a `Prop → Type`
elimination by projecting `c.claim : FiniteOrbitClaim` out of a
`BoundedOrbitCertificate t l`. A future PR flipping the sort to
`: Prop` will fail to typecheck this `def` — you cannot project a
`Type`-valued field out of a `Prop`-valued structure (no dependent
elimination from `Prop` into `Type`). Parallel to PR #54's
`def certificateClaim` in `LeafClaimTests.lean` (scenario 14).

**Polymorphic apply-the-instance checks (scenarios 11 + 12).**
Demonstrate the instance signatures directly, guarding the exported
API + type signatures (vs. the value-only cases in scenarios 1–10
which verify compute reduction). The form `inferableInstance c y`
(naming the instance) is the strongest regression: it verifies
both the existence AND the signature of the named instance, not
just whether `decide` resolves on a closed value. Mirrors PR #56's
polymorphic `accelerated_orbit_compose x k k'` check (scenario 9)
and `orbit_predecessor_reaches_one` polymorphic check (scenario 10).

Scenarios:
1.  `.empty.Holds 0 = False` (no orbit states claimed).
2.  `.singleton 5 .Holds 5 = True` (exact match).
3.  `.singleton 5 .Holds 4 = False` (no match).
4.  `.bounded 10 .Holds 0 = True` (well below boundary).
5.  `.bounded 10 .Holds 10 = True` (boundary inclusive).
6.  `.bounded 10 .Holds 11 = False` (just past boundary).
7.  `IsFiniteClaim LeafClaim.empty = True` (finite accepted).
8.  `IsFiniteClaim (LeafClaim.singleton 5) = True` (finite accepted).
9.  `IsFiniteClaim (LeafClaim.bounded 10) = True` (finite accepted).
10. `IsFiniteClaim (LeafClaim.interval 2 1 1) = False`
    (`.interval` rejected — `FiniteOrbitClaim` excludes it by
    construction).
11. Polymorphic apply-the-instance: `(c : FiniteOrbitClaim) →
    (y : Nat) → Decidable (c.Holds y)` (signature-level guard
    via `FiniteOrbitClaim.Holds.decidable c y`).
12. Polymorphic apply-the-instance: `(c : LeafClaim) →
    Decidable (IsFiniteClaim c)` (signature-level guard).
13. API-shape regression: `def boundedCertificateClaim`
    (Prop → Type elimination; mirrors PR #54's `def certificateClaim`).

This is a sibling test module to `LeafClaimTests.lean`,
`CoverageTreeOrbitTests.lean`, `DynamicsHelpersTests.lean`, and
`EquivalenceHelpersTests.lean`. Lean CI compiles this module as
part of the `CollatzResearch` library build (auto-discovered via
`lakefile.toml`'s `[[lean_lib]] srcDir = "Lean"`).
-/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Scenario 1: `.empty.Holds 0 = False` (no orbit states claimed). -/
example : FiniteOrbitClaim.empty.Holds 0 = False := by
  native_decide

/-- Scenario 2: `.singleton 5 .Holds 5 = True` (exact match). -/
example : (FiniteOrbitClaim.singleton 5).Holds 5 = True := by
  native_decide

/-- Scenario 3: `.singleton 5 .Holds 4 = False` (no match). -/
example : (FiniteOrbitClaim.singleton 5).Holds 4 = False := by
  native_decide

/-- Scenario 4: `.bounded 10 .Holds 0 = True` (well below boundary). -/
example : (FiniteOrbitClaim.bounded 10).Holds 0 = True := by
  native_decide

/-- Scenario 5: `.bounded 10 .Holds 10 = True` (boundary inclusive). -/
example : (FiniteOrbitClaim.bounded 10).Holds 10 = True := by
  native_decide

/-- Scenario 6: `.bounded 10 .Holds 11 = False` (just past boundary). -/
example : (FiniteOrbitClaim.bounded 10).Holds 11 = False := by
  native_decide

/-- Scenario 7: `IsFiniteClaim LeafClaim.empty = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim LeafClaim.empty = True := by
  native_decide

/-- Scenario 8: `IsFiniteClaim (LeafClaim.singleton 5) = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.singleton 5) = True := by
  native_decide

/-- Scenario 9: `IsFiniteClaim (LeafClaim.bounded 10) = True`
    (finite accepted). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.bounded 10) = True := by
  native_decide

/-- Scenario 10: `IsFiniteClaim (LeafClaim.interval 2 1 1) = False`
    (`.interval` is structurally excluded from `FiniteOrbitClaim`,
    so any `LeafClaim.interval _ _ _` is "not finite" by definition
    of `IsFiniteClaim`). -/
example : FiniteOrbitClaim.IsFiniteClaim (LeafClaim.interval 2 1 1) = False := by
  native_decide

/-- Scenario 11 (PR #56 v4 pattern — polymorphic apply-the-instance):
    the `Holds.decidable` instance has type
    `(c : FiniteOrbitClaim) → (y : Nat) → Decidable (c.Holds y)`.
    The polymorphic `example` below guards this signature directly
    by **naming the instance**, independent of any concrete value.

    Naming the instance is the strongest regression: it verifies
    both the existence AND the signature of
    `FiniteOrbitClaim.Holds.decidable`. A future PR that breaks
    the instance signature (e.g., removes a parameter, changes the
    sort, drops a constructor case) will fail to typecheck this
    `example`. Mirrors `CoverageTreeOrbitTests.lean` scenario 9's
    polymorphic `accelerated_orbit_compose x k k'` check (which
    names the THEOREM directly). For instances, the analogous
    "name the instance" form is the strongest regression available
    short of building a full dependent eliminator. -/
example (c : FiniteOrbitClaim) (y : Nat) :
    Decidable (c.Holds y) :=
  FiniteOrbitClaim.Holds.decidable c y

/-- Scenario 12 (PR #56 v4 pattern — polymorphic apply-the-instance):
    the `IsFiniteClaim.decidable` instance has type
    `(c : LeafClaim) → Decidable (IsFiniteClaim c)`. The polymorphic
    `example` below guards this signature directly by naming the
    instance.

    Mirrors scenario 11 for the `IsFiniteClaim` predicate.
    Independent of any concrete `LeafClaim` value. -/
example (c : LeafClaim) :
    Decidable (FiniteOrbitClaim.IsFiniteClaim c) :=
  FiniteOrbitClaim.IsFiniteClaim.decidable c

/-- Scenario 13 (Q4 v3 / PR #57 — API-shape regression; replaces the
    v3 `#check @BoundedOrbitCertificate` which would only print the
    sort rather than guard it).

    `BoundedOrbitCertificate` is intentionally `: Type`-valued (a
    proof-carrying data bundle), NOT `: Prop`. The
    `claim : FiniteOrbitClaim` data field cannot live in a
    `: Prop` structure: Lean 4 elaboration rejects `Type`-valued
    fields in `Prop`-valued structures; even if it did compile, the
    field could not be eliminated to `Type`.

    This `def` performs a `Prop → Type` elimination by projecting
    `c.claim : FiniteOrbitClaim` out of a `BoundedOrbitCertificate t l`.
    A future PR flipping the sort to `: Prop` will fail to typecheck
    this `def` — you cannot project a `Type`-valued field out of a
    `Prop`-valued structure (no dependent elimination from `Prop`
    into `Type`).

    Companion guard: scenarios 1–10 (closed-form `native_decide`
    propositional equalities on `Holds` + `IsFiniteClaim`) show that
    the data-side predicates remain kernel-checked even though the
    enclosing structure is `: Type`-valued.

    Per the Q4 v3 spec (PR #55): "`BoundedOrbitCertificate` ...
    Type-valued (NOT `: Prop`)" — the API-shape regression closes
    the loop by demonstrating the actual `Prop → Type` elimination.

    Parallel to PR #54's `def certificateClaim` in
    `LeafClaimTests.lean` scenario 14. -/
def boundedCertificateClaim {t : CoverageTree} {l : CoverageLeaf}
    (c : BoundedOrbitCertificate t l) : FiniteOrbitClaim :=
  c.claim

end CollatzResearch
