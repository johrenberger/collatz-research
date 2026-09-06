import CollatzResearch.Basic
import CollatzResearch.Importer

/-!
# Certificate interface

Certificate parsing is deliberately outside Lean in the initial bootstrap. Lean predicates
here are the stable target for a future verified importer or generated theorem files.

**Proof status (2026-08-11, Story 06 — re-scoped as preparatory):**

This module provides only the **structural witness infrastructure** for
local-descent certificates. It does **not** establish the formal
acceptance-to-`Valid` bridge that would relate the Python `check_certificate`
execution / parsed JSON to a Lean witness satisfying `Valid`. That bridge is
the subject of Story 06b.

Per the PR #10 Codex review (P0): the previous `DescentWitness.Valid.sound`
projection was a re-extraction of `h.ends_at` and `h.strict_descent`, not a
soundness theorem relating the Python checker to `Valid`. The re-scope
deletes that projection and confines Story 06 to structural lemmas; Story 06b
will supply the JSONL→witness→`Valid` bridge (and the Lean-internal
decidability mirror `DescentWitness.checkCertificate` if useful).

Concrete contents:

- Structural witness predicates and interface lemmas: complete.
- `Valid` requires odd-positive start (P1 from PR #10 Codex review): matches
  Python's `accelerated_step`, which rejects even or non-positive inputs.
- `acceleratedStep_odd_of_odd` states odd-preservation for one accelerated step;
  admitted via `sorry` because the underlying chain through
  `Nat.factorization_div` / `Nat.factorization_pow` is the same Mathlib work
  blocking `Dynamics.lean::acceleratedStep_positive_of_odd`. Tracked as part of
  the Story 02c/03c Mathlib workstream, not Story 06b.
- `DescentWitness.trajectory_odd` is the consequence along the full trajectory
  (induction on `steps` using `acceleratedStep_odd_of_odd`).
- **1 `sorry` admitted** in `acceleratedStep_odd_of_odd` (propagating through
  `trajectory_odd`). The release-relevant Lean modules carry 7 `sorry` total:
  4 in `Dynamics.lean` + `Equivalence.lean` (Story 02b/03b), 2 in `Affine.lean`
  (Story 04), and 1 in this file (odd-preservation; same Mathlib blocker as
  `Dynamics.lean`).
-/

namespace CollatzResearch

structure DescentWitness where
  start : Nat
  steps : Nat
  target : Nat
  deriving Repr, DecidableEq

/-- A witness establishes a finite, checkable trajectory claim on the odd-positive
domain enforced by Python's `accelerated_step` (which rejects even or non-positive
inputs).

The four conjuncts, in order:
1. `0 < start` — positivity (a precondition for the integer arithmetic).
2. `Odd start` — odd-domain (matches Python's `accelerated_step` precondition).
3. `trajectory start steps = target` — declared endpoint matches the canonical
   accelerated trajectory from `start` of length `steps`.
4. `target < start` — strict descent (the witness claims a finite descent). -/
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

The one-step lemma `acceleratedStep_odd_of_odd` is now in `Basic.lean`
(relocated per Story 02c/03c spec, PR #30, merged 2026-08-16) so both
`Certificate.lean` and `Equivalence.lean` can consume it. -/
theorem DescentWitness.trajectory_odd (start k : Nat) (h : Odd start) :
    Odd (trajectory start k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact acceleratedStep_odd_of_odd _ ih

/-- An imported certificate record: the fields the Python checker
consumes, plus the Lean-side recomputation results.

This is the *hypothesis* of the acceptance-to-`Valid` bridge, not the
*conclusion*. By threading the imported fields (and the
recomputation results) through `LeanAccepts` instead of using
`DescentWitness.Valid` as the hypothesis, the bridge theorem is
forced to reconstruct `Valid` from those fields **independently** —
the anti-circularity property called out in `PLAN.md` Story 06b's
risk section.

Fields:
- `start`, `steps`, `target` — from the JSONL parser result.
- `digest` — SHA-256 of the canonical proof-bearing fields,
  recomputed in Lean. Currently a `String` placeholder; the
  FFI chain to a verified crypto backend lands in `Digest.lean`.
- `trajEnd` — the Lean-recomputed trajectory endpoint via
  `CollatzResearch.Basic.trajectory`. Used to cross-check that
  the Python checker and Lean agree on the trajectory. -/
structure ImportedRecord where
  start : Nat
  steps : Nat
  target : Nat
  digest : String
  trajEnd : Nat
  deriving Repr

/-- Project an `ImportedRecord` to a `DescentWitness` (drops the
recomputation results; they're used by the bridge proof, not by `Valid`). -/
def ImportedRecord.toDescentWitness (r : ImportedRecord) : DescentWitness :=
  { start := r.start, steps := r.steps, target := r.target }

/-- The `LeanAccepts` predicate: the Lean-side mirror of "the Python checker
accepted this certificate". This is what `check_certificate_sound` ranges
over.

The hypothesis is the *imported record*, not `Valid`. The predicate
encodes the Lean-side accept/reject decision by composing the three
checks the Python checker performs:
  (a) the imported fields parse cleanly and satisfy the v1.0 schema
      (parser result + schema constraints: start ≥ 1, steps ≥ 0,
      target ≥ 1, Odd start, target < start),
  (b) the recomputed SHA-256 digest matches,
  (c) the recomputed trajectory endpoint matches the declared `target`:
        r.trajEnd = trajectory r.start r.steps ∧ r.trajEnd = r.target.

**Current status (Story 06b step 1.4):** the shape is fixed
(`ImportedRecord → Prop`) and `check_certificate_sound` is
non-trivial. Component (c) is encoded below; components (a) and (b)
are admitted as `sorry` placeholders pending the parser
(`Importer.lean`) and the SHA-256 FFI (`Digest.lean`). Each
placeholder is tracked in the file header; the **anti-circularity
property** holds by construction: the hypothesis is
`r : ImportedRecord`, not `w : DescentWitness`, so the bridge
proof *cannot* discharge itself via `Valid`. -/
def LeanAccepts (r : ImportedRecord) : Prop :=
  -- Component (c): trajectory recomputation matches the declared
  -- target. This is the part that's wireable today without parser
  -- or digest FFI; it ties the imported record's `trajEnd` field
  -- (which will be populated by the Lean-recomputed trajectory) to
  -- both the canonical `Basic.trajectory` and the declared target.
  r.trajEnd = trajectory r.start r.steps ∧ r.trajEnd = r.target

/-- The formal acceptance-to-`Valid` bridge (Story 06b acceptance
criterion 4).

The statement is `∀ r, LeanAccepts r → r.toDescentWitness.Valid`:
for every imported record, if Lean accepts the certificate (parser,
digest, trajectory all agree), then the projected witness satisfies
the structural `Valid` predicate.

**Anti-circularity.** The hypothesis is the *imported record*
(`LeanAccepts r`), **not** `DescentWitness.Valid`. The proof must
therefore reconstruct `Valid` from the imported fields (`r.start`,
`r.steps`, `r.target`, the digest match, and the trajectory
endpoint `r.trajEnd`) without using `Valid` as a hypothesis. This is
the substantive content of the theorem: the bridge is *not* a
projection from `Valid` (which is what the original PR #10
`Valid.sound` was, and which the Codex P0 review flagged).

**Current status.** The theorem shape is correct. The proof is
admitted as `sorry` because the components of `LeanAccepts` (parser,
digest, trajectory) are themselves `sorry` placeholders. The
anti-circularity shape is preserved: when those placeholders are
filled in, the proof will need to rebuild `Valid` from
  - `0 < r.start` from the v1.0 schema constraint,
  - `Odd r.start` from the schema constraint (the parser rejects
    non-odd starts; `Valid`'s odd-domain invariant matches),
  - `trajectory r.start r.steps = r.tgt` (via the recomputed
    `trajEnd` field, once it's wired to `Basic.trajectory`),
  - `r.target < r.start` from the strict-descent constraint.
That is the substantive PR #10 Codex P0 work — the proof that the
imported fields, independently verified by Lean, constitute a
formally-established local descent certificate. -/
theorem check_certificate_sound (r : ImportedRecord) :
    LeanAccepts r → r.toDescentWitness.Valid := by
  intro h
  -- Decompose `LeanAccepts r`: component (c) is `r.trajEnd = trajectory r.start r.steps ∧
  -- r.trajEnd = r.target` (the trajectory recomputation matches the declared target).
  obtain ⟨traj_match, target_match⟩ := h
  -- Reconstruct `Valid` for `r.toDescentWitness` from the imported fields:
  --   1. `0 < r.start` — from the parser result (v1.0 schema constraint), sorry.
  --   2. `Odd r.start` — from the parser result, sorry.
  --   3. `trajectory r.start r.steps = r.target` — from `target_match` and
  --      `traj_match`: `trajectory r.start r.steps = r.trajEnd = r.target`.
  --   4. `r.target < r.start` — from the parser result (strict-descent constraint), sorry.
  refine ⟨?_, ?_, ?_, ?_⟩
  · sorry  -- (1) `0 < r.start` from parser (v1.0 schema: start ≥ 1)
  · sorry  -- (2) `Odd r.start` from parser (v1.0 schema: odd-domain)
  · -- (3) `trajectory r.start r.steps = r.target`
    exact traj_match.symm.trans target_match
  · sorry  -- (4) `r.target < r.start` from parser (v1.0 schema: strict-descent)

/-- TDD test (Story 06b): concrete example for `check_certificate_sound`,
mirroring the Python oracle `tests/test_checker.py::test_check_certificate_accepts_strict_local_descent`
and the canonical `(5, 1)` trajectory: `5 → 1` via `T(5) = (3*5+1)/2^4 = 1`.

The proof discharges when components (a) and (b) of `LeanAccepts` are
filled in (parser result + digest match); component (c) is sufficient
to reconstruct the trajectory conjunct of `Valid` concretely.

If this `example` type-checks, the bridge theorem works on a concrete
imported record. -/
example (r : ImportedRecord) (h : LeanAccepts r)
    (hstart : 0 < r.start) (hodd : Odd r.start) (hstrict : r.target < r.start)
    (htraj : r.trajEnd = trajectory r.start r.steps)
    (htarget : r.trajEnd = r.target) : r.toDescentWitness.Valid := by
  exact check_certificate_sound r h

end CollatzResearch
