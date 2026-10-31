# ADR 0008: The Lean admission budget is an exact baseline

Status: accepted. The Lean admission budget records the exact number of
admitted proof holes per file, and CI rejects any deviation from it.

## Context

`scripts/check_sorry_budget.py` existed to "reject increases in tracked Lean
`sorry` declarations". It counted only lines matching `^\s*sorry\b`, which
missed every bullet-form hole (`· sorry`) and could not tell an admission
apart from the same word inside a comment or a string.

The gap was not theoretical. `Lean/CollatzResearch/Certificate.lean` held three
`· sorry` holes in `check_certificate_sound`; the checker scored that file as
zero admissions, so CI reported "Lean admission budget respected" while the
file sat above its recorded allowance. The recorded allowances for
`Dynamics.lean` and `Equivalence.lean` also outlived the sorries they were
written for, leaving headroom that new admissions could have consumed without
the gate noticing.

Separately, `docs/theorem-status.md` listed every theorem as `Checked` and had
no row for either theorem that still carries an admitted proof, so the ledger
read as if nothing were outstanding.

## Decision

- Count admission holes in code positions: `sorry`, `admit`, `sorryAx`,
  `axiom`, and `opaque` declarations. Strip Lean block comments (nested), line
  comments, and string literals before counting, so prose never counts. These
  five are reserved Lean keywords, so every occurrence of one in code is a
  declaration; matching them as words covers the `private axiom`,
  `protected axiom`, and `private opaque` modifier forms, which a line-anchored
  pattern would miss. `opaque` is included because it hides the value from the
  kernel: it is discharged through an `Inhabited`/`Nonempty` instance, and for
  a proposition `Nonempty p` is classically equivalent to `p`, so an opaque
  declaration can hide a proposition proof from review.
- Scan the code inside interpolated string holes (`s!"..."`). Those holes hold
  Lean expressions, so a `sorry` in one is a real admission that Lean itself
  reports; discarding the whole literal would hide it.
- Treat `docs/lean-sorry-budget.json` as an exact baseline. More holes than
  recorded is new proof debt and fails; fewer holes than recorded is a stale
  record and fails, because the baseline must be lowered in the same change
  that closed the holes.
- Record the remaining admitted proofs in `docs/theorem-status.md` with an
  explicit status, so the ledger distinguishes proved theorems from admitted
  ones.

## Consequences

- `Certificate.lean` is tracked at 3 admissions, `CoverageTree.lean` at 1, and
  `Importer.lean` at 2; the other tracked modules are at 0. Total admitted
  holes across the release-relevant modules: 6.
- Closing an admission now requires updating the budget file in the same
  change, which keeps the recorded debt honest instead of letting it drift.
- The budget schema moves to version 2 because the unit changed from
  line-anchored `sorry` lines to admission holes.
