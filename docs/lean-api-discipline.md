# Lean API discipline

This document codifies the rules for **discovering the right Mathlib
API surface** before iterating on Lean CI. It complements
`LEAN_PATTERNS.md` (which catalogues positive vetted patterns P01–P13)
by codifying **negative** discipline: when to stop guessing.

## The stop-guessing rule

CI failures caused by guessing Mathlib API surfaces — wrong lemma
name, implicit/explicit argument mismatch, `Nat` vs `Int` confusion,
`ℕ` vs `ℤ` coercion gap, missing instance argument — cannot be
resolved by trying more variants of the same shape:

- Each guess costs a full CI run (5–10 min warm, longer for cold
  Mathlib — see Story 08 / PR #32 for the build-time history).
- A "close" guess can mask a deeper signature mismatch that only
  surfaces on the next lemma that uses similar shapes.

**Rule (codified 2026-08-19 after PR #39 closed without merge; refined 2026-08-19 after PR #43 failure #2):**

After **1 CI failure** with API-surface uncertainty on the same lemma,
the next attempt **must** begin with Exit Path #2 (reuse nearby-proven
pattern) OR Exit Path #3 (read Mathlib source at pinned rev). After
**2 CI failures**, the next attempt **must** begin with Exit Path #3
OR Exit Path #4 (Codex review). CI-only iteration is no longer
acceptable after either threshold.

The original threshold (2 failures) was too lenient: failure #2 is
always worse than failure #1 because it costs another CI run AND
forecloses the option of ditching the surface entirely. PR #43
demonstrated this — failure #1 was a definitional-unfold assumption;
failure #2 was a guess at the conversion name. Exit Path #2 (in
`Basic.lean::acceleratedStep_odd_of_odd`) would have produced the
correct conversion on failure #1.

## The four exit paths

Ordered by typical effort; any of them is acceptable once the
threshold above is hit.

1. **Check the playbook.** `LEAN_PATTERNS.md` (repo root, merged in
   PR #40) catalogues vetted patterns P01–P13 with worked examples.
2. **Reuse a nearby proven lemma.** Search `Lean/` for an analogous
   proof that already exercises the same abstraction. Established
   precedents in this codebase:

   - `Lean/CollatzResearch/Basic.lean::acceleratedStep_odd_of_odd`
     (proved in PR #31) — exercises the `ordCompl` family.
   - `Lean/CollatzResearch/Dynamics.lean::standardStep_positive`
     (proved in PR #37) — parity dispatch via `decide` + `omega`.
   - `Lean/CollatzResearch/Dynamics.lean::acceleratedStep_positive_of_odd`
     (proved in PR #38) — `ordCompl` framing with explicit
     `Nat.ordCompl_dvd (3 * n + 1) 2`.

3. **Read the Mathlib source for the pinned rev.** The pinned target
   is `v4.33.0` per Story 08 (PR #32). Fetch the definition directly:

   ```
   https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.33.0/Mathlib/<path>.lean
   ```

   Or read locally from `~/.lake/packages/mathlib/Mathlib/<path>.lean`
   after `lake update` (do **not** run a full `lake build` to populate
   it — `lake update` alone pulls the source). Confirm the signature
   letter-by-letter against the call site: argument order, implicit
   `{}` vs explicit `()` brackets, instance arguments.

4. **Request Codex review.** Tag `@codex review` on the PR, or stop
   the current branch and ask for review before the next attempt.
   Do not iterate further on CI alone.

## Classifying failures (API-surface vs proof-shape)

If a CI error could be either API-surface or proof-shape, classify
by the error message before deciding which rule applies:

| Error says… | Mode |
|---|---|
| "unknown identifier", "type mismatch", "expected … got …" with a name you wrote | **API-surface** → apply this rule |
| "motive …", "eliminator …", "induction on …", "not well-founded" | proof-shape → re-formulate the induction |
| "no such instance", "inferring … failed", "type class" with an `inst` you didn't write | proof-shape → instance resolution is part of shape |

This rule is **distinct from** the proof-shape stop rule in
`docs/development-lifecycle.md` § "Lean proof work". The proof-shape
rule covers motive/eliminator mismatches fixable by switching
induction principles or documented fallbacks; this rule covers "I
don't know what Mathlib's `X.foo` looks like" — fixable only by
reading source or asking someone who has.

## Counter-examples (do not repeat)

- **PR #39** (`acceleratedStep_equiv_standardStep` direct attempt):
  ~10 CI failures iterating `Nat.factorization_*` and helper-lemma
  variants. Closed without merge per Codex advice; PR was decomposed
  into helper-lemma PRs starting with `standardTrajectory_succ_shift`
  (zero-sorry, library-independent shift lemma) and
  `standardStep_of_odd` (zero-sorry, parity dispatch).
- **PR #38 predecessor attempts** (before Codex identified `ordCompl`):
  stale `Nat.div_pos` + factorization-chain route blocked until
  Codex provided the exact `Nat.ordCompl_dvd (3 * n + 1) 2` signature.
  Both arguments are **explicit**; implicit-argument guessing was the
  wrong call. PR #38 succeeded only after the rule above was
  implicitly applied.
- **PR #43** (`standardStep_of_odd`, branch `story-02c-03c-helpers-2`):
  two-failure pair on the same surface; the refinement above is
  directly motivated by this case.
  - Failure #1: `h has type Odd n but is expected to have type n % 2 = 1`
    — assumption that `Odd n` reduces definitionally was wrong.
  - Failure #2 (anti-pattern): `Unknown identifier 'Odd_iff.mp'`
    — guessed the conversion name without Exit Path #2 first.
  - Correct fix (found via Exit Path #2 from
    `Basic.lean::acceleratedStep_odd_of_odd` PR #31): `Nat.odd_iff.mp h`
    (NOT `Odd_iff.mp`).
  - **Lesson**: Exit Path #2 must be attempted on failure #1, not
    deferred until failure #2. The original "2 failures" threshold
    was too lenient.

## Verified Mathlib v4.33.0 patterns

These conversions have been verified against Mathlib v4.33.0 by
exit-path application. Use them directly; do not second-guess.

| Need | Theorem | Direction |
|---|---|---|
| `Odd n → n % 2 = 1` | `Nat.odd_iff.mp` | mp |
| `n % 2 = 1 → Odd n` | `Nat.odd_iff.mpr` | mpr |
| `n % 2 ≠ 0 → n % 2 = 1` | `Nat.mod_two_ne_zero.mp` | mp |
| `2 ∣ n → n % 2 = 0` | `Nat.dvd_iff_mod_eq_zero.mp` | mp |

The earlier comment trail in `Basic.lean::acceleratedStep_odd_of_odd`
explicitly notes the v4.33.0 change: `Odd` is no longer definitional
in terms of `n % 2 = 1`; the conversion is via `Nat.odd_iff`.

## Adjacent rules (do not conflate)

- **`docs/lean-sorry-budget.json`** — constrains what is *mergeable*.
  Not a discovery aid for Lean API surfaces.
- **"Never remove pending theorem declarations just to satisfy the
  sorry budget"** — codified after PR #39's structural churn in
  which the `acceleratedTrajectory_reaches_one_implies_standard`
  declaration was removed and restored via `7c53589`. A
  sorry-budget-hygiene rule, not an API-discovery rule.
- **`LEAN_PATTERNS.md`** (repo root, PR #40) is the *positive*
  companion to this document. When you discover a working surface,
  add a pattern entry to `LEAN_PATTERNS.md` so the next attempt does
  not need to re-discover it.

## Maintenance

If a new recurring failure mode appears (e.g., `omega` timeouts on
`ℕ`-vs-`ℤ` coercions, `decide` limits on large constant sets, deep
metaprogramming errors), add a focused sub-rule here with a
counter-example. Do not generalize into vague advice — concrete
thresholds and concrete examples are what make this document
actionable at 04:00 GMT+2.

## Provenance

- Codified: 2026-08-19 after PR #39 closed without merge.
- **Refined 2026-08-19 after PR #43 failure #2**: threshold tightened
  from "2 failures" to "1 failure + Exit Path #2 is the next attempt's
  basis". See the PR #43 counter-example.
- Path A active packet (per Justin's 2026-08-16 selection): Story
  02c/03c helper-lemma PRs are the first adopters.
- Companion doc: `LEAN_PATTERNS.md` (playbook, positive patterns).
- Related subsection: `docs/development-lifecycle.md` § "Lean proof
  work" (proof-shape rule and red-test discipline).
