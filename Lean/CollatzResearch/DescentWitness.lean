import CollatzResearch.Basic

/-!
# Local-descent witness infrastructure

This module holds the **structural witness predicates and their interface
lemmas** for local-descent certificates: a `DescentWitness` records a start,
a step count, and a declared endpoint, and `DescentWitness.Valid` says the
endpoint is the canonical accelerated trajectory's endpoint and that it is
strictly below the start.

These declarations are **proven** and are kept deliberately.

**Why this module exists.** They previously lived in `Certificate.lean`,
together with the v1.0 *acceptance* bridge (`ImportedRecord`, `LeanAccepts`,
`check_certificate_sound`) and the JSONL parser in `Importer.lean`. That
bridge is retired: `check_certificate_sound`'s anti-circularity argument
rests on a SHA-256 digest of the proof-bearing fields, and only the Python
side computes it (`python/collatz_research/canonical.py`, `compute_digest`).
There is no Lean `Digest.lean`, so the Lean side of that bridge could not
be discharged, and the Q5 routing-partition architecture bypasses it.

So the admitted declarations are retired and the **proven** witness
infrastructure is relocated here, keeping the content rather than
discarding it. The Python side of the v1.0 format is untouched: the format,
its parser (`python/collatz_research/parser.py`), its checker
(`checker.py`), and its certificate builder (`certificates.py`) all remain
live and tested. Only the *Lean* v1.0 descent-certificate bridge is retired.

**Trust boundary.** This module makes no convergence, cycle-exclusion, or
global descent claim. `Valid` is a structural predicate about a declared
witness; `ends_at`, `strict_descent`, and `start_pos_odd` are projections
from it, and `trajectory_odd` states oddness preservation along the
trajectory.

Per-file admission counts are recorded in `docs/lean-sorry-budget.json`
and enforced by `scripts/check_sorry_budget.py`; this module carries none.
-/

namespace CollatzResearch

/-- A witness establishes a finite, checkable trajectory claim on the odd-positive
domain enforced by Python's `accelerated_step` (which rejects even or non-positive
inputs).

The four conjuncts, in order:
1. `0 < start` — positivity (a precondition for the integer arithmetic).
2. `Odd start` — odd-domain (matches Python's `accelerated_step` precondition).
3. `trajectory start steps = target` — declared endpoint matches the canonical
   accelerated trajectory from `start` of length `steps`.
4. `target < start` — strict descent (the witness claims a finite descent). -/
structure DescentWitness where
  start : Nat
  steps : Nat
  target : Nat
  deriving Repr, DecidableEq

/-- A witness is valid when it starts positive and odd, its declared endpoint is
the canonical accelerated trajectory's endpoint after `steps` steps, and that
endpoint is strictly below the start. -/
def DescentWitness.Valid (w : DescentWitness) : Prop :=
  0 < w.start ∧ Odd w.start ∧ trajectory w.start w.steps = w.target ∧ w.target < w.start

/-- A valid witness has the declared trajectory endpoint. -/
theorem DescentWitness.Valid.ends_at (w : DescentWitness) (h : w.Valid) :
    trajectory w.start w.steps = w.target :=
  h.2.2.1

/-- A valid witness is a strict descent for its declared start. -/
theorem DescentWitness.Valid.strict_descent (w : DescentWitness) (h : w.Valid) :
    w.target < w.start :=
  h.2.2.2

/-- A valid witness has a positive, odd start (matching Python's `accelerated_step`). -/
theorem DescentWitness.Valid.start_pos_odd (w : DescentWitness) (h : w.Valid) :
    0 < w.start ∧ Odd w.start :=
  ⟨h.1, h.2.1⟩

/-- Oddness is preserved along the trajectory (induction on `steps`).

The one-step lemma `acceleratedStep_odd_of_odd` is in `Basic.lean`
(relocated per Story 02c/03c spec, PR #30, merged 2026-08-16) so both
this module and `Equivalence.lean` can consume it. -/
theorem DescentWitness.trajectory_odd (start k : Nat) (h : Odd start) :
    Odd (trajectory start k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact acceleratedStep_odd_of_odd _ ih

end CollatzResearch
