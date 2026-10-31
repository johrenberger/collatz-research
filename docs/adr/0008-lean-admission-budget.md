# ADR 0008: The Lean admission budget is an exact baseline

Status: accepted. The Lean admission budget records the exact number of
admitted declarations per file, and CI rejects any deviation from it.

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

The first repair made the checker code-aware: it stripped comments and string
literals, counted bullet-form holes, and reconciled the recorded allowances to
an exact baseline of 3 / 1 / 2 holes. A later review found two remaining
defects in that repair.

**A lexical scan is not an oracle.** A custom elaborator can build Lean's
`sorry` term without the word appearing in the source at all:

```lean
open Lean Elab Term in
elab "redacted" : term => do
  let e ← Lean.Meta.mkSorry (Lean.mkConst ``True) (synthetic := false)
  pure e
```

Lean accepts the resulting declaration and reports it as using `sorry`; a
scan of the source text cannot see it. The same holds for a synthesised
`axiom` or `opaque` command. Any claim that a source scan detects *all*
admitted proofs is therefore false, and the gate may not be described that
way.

**The reserved-keyword claim was wrong.** The first repair counted `sorry`,
`admit`, `sorryAx`, `axiom`, and `opaque` as "reserved Lean keywords". Only
`sorry`, `axiom`, and `opaque` are reserved. `admit` and `sorryAx` are legal
user identifiers: `def admit : Nat := 1` and `namespace UserChosen def
`sorryAx : Nat := 1` are legal Lean programs. A word-boundary scan of those
two names therefore counts legitimate code as an admission.

Separately, `docs/theorem-status.md` listed every theorem as `Checked` and had
no row for either theorem that still carries an admitted proof, so the ledger
read as if nothing were outstanding.

## Decision

- **Ask Lean, do not read the source.** `sorry` and `sorryAx` admissions are
  counted from Lean's own report. Elaborating a file with `lake env lean
  --json <file>` makes Lean emit one `hasSorry` diagnostic for every
  declaration that references `sorryAx` -- the same signal it prints as
  "declaration uses `sorry`". This is authoritative: it sees a `sorry` that
  an elaborator synthesised, and it does not confuse a user identifier named
  `admit` with an admission.
- **Count declarations, not holes.** Lean reports one diagnostic per
  declaration, so the enforced unit is the *admitted declaration*. Three
  holes inside one declaration count as one admitted declaration. The
  admitted declaration is the unit that matters for the trust boundary: an
  admitted declaration can be used anywhere, and how many `sorry`s it
  contains does not change what it is trusted to prove. The hole count is
  recorded in prose in the module headers, not in the enforced budget.
- **Keep a lexical component only where Lean is silent.** Lean emits no
  diagnostic for `axiom` and `opaque` declarations. Those two *are* reserved
  Lean keywords, so a word-boundary match in a code position identifies the
  declaration, including the `private axiom`, `protected axiom`, and
  `private opaque` modifier forms. Comments and string literals are stripped
  before matching. This part of the gate remains lexical and is documented
  as such; a synthesised `axiom` command would not be detected by it.
- **`admit` and `sorryAx` are never counted lexically.** They are legal Lean
  identifiers. A real `sorryAx` use is caught by the Lean diagnostic.
- Treat `docs/lean-sorry-budget.json` as an exact baseline. More admitted
  declarations than recorded is new proof debt and fails; fewer than recorded
  is a stale record and fails, because the baseline must be lowered in the
  same change that closed the admissions.
- Record the modules that Lean cannot elaborate at all in the
  `not_elaborated` section of the budget, with the reason. Such a module is
  outside the trusted chain -- nothing can import a module that does not
  elaborate -- so only the lexical component applies to it. The list is
  checked in both directions: a module that newly stops elaborating fails the
  gate, and a recorded module that elaborates again fails the gate until its
  entry is removed.
- Record the remaining admitted proofs in `docs/theorem-status.md` with an
  explicit status, so the ledger distinguishes proved theorems from admitted
  ones.

## Consequences

- `Certificate.lean` is tracked at 1 admitted declaration (its
  `check_certificate_sound`, which contains 3 holes), `CoverageTree.lean` at
  1, and `Importer.lean` at 2; the other tracked modules are at 0. The
  recorded numbers fall from 6 holes to 4 declarations because the enforced
  unit is now the declaration. The set of admitted declarations is unchanged.
- Closing one of the three holes inside `check_certificate_sound` does not by
  itself lower the recorded budget; the declaration has to be closed. That is
  a real loss of granularity, and it is the price of a sound oracle: the hole
  count is not available from Lean's report.
- The gate now needs a working Lean toolchain and a successful Lean build.
  `lake env lean <file>` elaborates one file and loads its imports from the
  build cache, so the CI step runs after the Lean build, not before it. A
  file whose imports are not built fails the gate with an elaboration error
  rather than being skipped.
- The check costs one Lean elaboration per source file. Each elaboration
  loads the whole Mathlib environment, so the dominant cost is the
  environment load rather than the file content: the gate costs roughly as
  much as one more Lean build of the project. The `Lean CI / build` job
  already runs a full Lean build, so the added cost is proportional to that
  job rather than to the size of the source tree. `LEAN_ADMISSION_JOBS`
  controls how many files are elaborated at once (default 2, capped by the
  CPU count); each elaboration holds its own copy of the Mathlib
  environment, so raising it trades memory for wall-clock time.
- `Lean/CollatzResearch/BoundedInputCertificateParser.lean` does not parse
  under Lean 4.33 and nothing imports it, so it and its test module are
  recorded in `not_elaborated`. They carry no admissions, and the lexical
  component still covers them. Repairing them is separate work.
- The budget schema moves to version 3 because the unit changed from
  admission holes to admitted declarations, and because the `sorry` count now
  comes from Lean instead of from the source text.
