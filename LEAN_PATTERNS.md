# Lean Patterns

Compact project playbook for Lean work in `collatz-research`. It records
validated approaches, not a general Lean tutorial. Section IDs are stable
retrieval keys for OpenClaw/MiniMax.

## Global Rules (always load)

- Treat Lean's checked kernel as the only mathematical authority. Python,
  SMT, generated examples, and CI prose may guide a proof but never prove it.
- Read the target definition, its imports, theorem-status row, and the exact
  pinned Mathlib source before choosing proof tactics or lemma names.
- Preserve public declarations and their domain hypotheses. Never remove a
  pending theorem or replace it with a comment to satisfy an admission budget.
- A proof-closure PR adds no `sorry`/`admit` in its target dependency chain.
  A green build with admissions is compilation, not theorem completion.
- Lean validation runs in GitHub CI only. Do not run local `lake` commands.
- After two failed attempts on the same logical proof step, stop guessing:
  inspect the exact CI error and pinned source, then either narrow the lemma
  or escalate with the failed head SHA and evidence.

## Retrieval Policy

OpenClaw loads **Global Rules** plus only the pattern sections relevant to the
current Lean task. Load the whole file only for architecture or refactor work.
Retrieve by stable ID; do not inject unrelated patterns into routine proof
turns.

## P01 — Natural-number domains: `Nat` / `PNat` / `OddPNat`

**Use when:** defining map domains or carrying positivity/oddness through a proof.
**Preferred approach:** use `Nat` internally; make positivity and oddness
explicit propositions at theorem boundaries. Use `PNat`/`OddPNat` only where a
subtype eliminates repeated domain obligations without adding coercion noise.
**Primitives:** `Positive`, `Odd`, `Odd.pos`, `Nat.pos_iff_ne_zero`.
**Avoid:** assuming a `Nat` is positive; relying on `omega` to unfold `Positive`;
weakening an odd-domain theorem to include zero or even inputs.

**Escalate when:** a map's zero/even behavior conflicts with its intended
trajectory statement, or subtype coercions dominate the proof.

## P02 — Two-adic valuation and divisibility

**Use when:** reasoning about `twoAdicValuation`, `Nat.factorization 2`,
`ordCompl[2]`, or division by a power of two.
**Preferred approach:** first state the arithmetic fact needed in the project
domain: numerator nonzero/positive, a power divides it, then the quotient
property. Instantiate Mathlib lemmas explicitly when CI shows their arguments.
**Primitives:** `Nat.ordCompl_dvd n p`, `Nat.factorization_le_iff_dvd`,
`Nat.div_pos`, `Nat.pow_pos`, `Nat.ordCompl_div_pow_of_dvd` when verified
against the pinned source.
**Avoid:** guessing Mathlib names/signatures; treating `factorization` as a
definitionally transparent exponent; proving a whole trajectory theorem with a
single opaque factorization rewrite.

**Escalate when:** two source-verified lemma applications fail to elaborate, or
the missing step is an iteration lemma rather than a factorization fact.

## P03 — Function iteration and reachability

**Use when:** composing standard/accelerated steps, trajectories, or a finite
`ReachesOne` witness.
**Preferred approach:** expose a one-step shift/compose lemma first, then use
it to compose finite witnesses. State the intermediate state and step count
explicitly.
**Primitives:** `Function.iterate`, `trajectory_succ`, `standardTrajectory_succ`,
project reachability composition lemmas when present.
**Avoid:** inferring a trajectory theorem from one-step equivalence without
closure of the domain at every iterate; manually expanding long traces.

**Escalate when:** the intermediate state cannot be expressed by the existing
iteration API, or witness concatenation is missing.

## P04 — Strong-induction descent

**Use when:** a descent/ranking certificate gives a strictly smaller successor
and the goal is eventual reachability.
**Preferred approach:** strong-induct on the natural measure; split the base
case; extract `m < n`; apply the induction hypothesis to `m`; compose the
one-step/finite reachability witness.
**Primitives:** `Nat.strong_induction_on`, `Nat.strong_rec_on`, explicit
transitivity lemmas for reachability.
**Avoid:** induction on an unknown stopping time; recursive definitions without
an explicit decreasing measure; silently assuming a ranking condition applies
to exceptions.

**Escalate when:** the descent result is non-strict, its domain is incomplete,
or the target lacks a transitivity interface.

## P05 — Residue classes and modular arithmetic

**Use when:** proving partition coverage/disjointness, parity, or a branch
condition indexed by residues.
**Preferred approach:** keep a positive modulus hypothesis in scope; normalize
to canonical representatives with `%`; prove bounds and membership separately.
**Primitives:** `Nat.mod_lt`, `Nat.mod_eq_of_lt`, `List.mem_range`, project
`Residue`, `residue`, and `Partition` definitions.
**Avoid:** using `%` with an implicit zero-modulus convention; conflating
equality of representatives with congruence; making `omega` solve nonlinear
modular facts without a reduced hypothesis.

**Escalate when:** canonicalization and congruence are mixed in one goal or
residue coverage depends on an unproved modulus invariant.

## P06 — Affine symbolic representations

**Use when:** relating a branch word, symbolic executor, and affine map.
**Preferred approach:** prove structural composition first; carry explicit
divisibility hypotheses to apply the affine map; separate symbolic validity
from equality of evaluated naturals.
**Primitives:** `AffineMap.comp`, `BranchWord.toAffine`, `BranchWord.appliesTo`,
`BranchWord.execute`, `ring_nf` for normalized polynomial equalities.
**Avoid:** cancelling natural-number division without divisibility evidence;
using an affine identity as proof that a word is applicable.

**Escalate when:** a desired cancellation lemma is absent in pinned Mathlib or
the proof needs a new shared divisibility-combination lemma.

## P07 — Threshold inequalities and ranking functions

**Use when:** a certificate claims strict descent above a threshold.
**Preferred approach:** isolate the threshold predicate, prove all denominator
and positivity side conditions, normalize constants, then use `omega` only for
linear consequences.
**Primitives:** `omega`, `norm_num`, `Nat.div_pos`, explicit threshold/rank
definitions.
**Avoid:** hiding strictness in a solver call; applying a ranking lemma below
its threshold; mixing `Nat` subtraction with integer algebra without a bridge.

**Escalate when:** the obligation is nonlinear, depends on division rounding,
or requires an unrecorded bound from a certificate producer.

## P08 — Finite exceptions and coverage trees

**Use when:** a finite set/tree covers a root domain except for explicitly
handled leaves.
**Preferred approach:** make root-domain membership independent of the
algorithm being proved; state leaf verification, routing completeness, and
exception handling as distinct predicates; induct on bounded tree depth.

**Primitives:** `CoverageNode`, `CoverageTree`, `List.lookup`, list membership,
strong induction on remaining depth where applicable.

**Avoid:** defining completeness in terms of `descend` when proving properties
of `descend`; treating unique IDs as semantic certificates; dropping a leaf
case from a coverage claim.

**Escalate when:** a predicate assumes the desired routing conclusion, or a
depth measure is not available for the recursive call.

## P09 — Certificate-checker soundness

**Use when:** connecting JSON/certificate acceptance to a mathematical claim.

**Preferred approach:** separate untrusted parsing/production from a strict
checker and then from a Lean soundness theorem. Check schema version, canonical
encoding, digest coverage, malformed input, and recomputation independently.

**Primitives:** strict JSON parser, canonical serializer, schema validators,
Lean checker-soundness declarations.

**Avoid:** calling accepted Python output a theorem; trusting a producer's
claimed residue/trajectory/rank; accepting unknown schema versions.

**Escalate when:** acceptance depends on unchecked computation or the claimed
mathematical conclusion has no Lean soundness theorem.

## P10 — `native_decide` and decidability

**Use when:** a closed, finite, decidable proposition is too large for ordinary
reduction but is safe to evaluate in the accepted trust model.

**Preferred approach:** use it only for closed propositions or bounded finite
enumerations with transparent inputs; retain a symbolic theorem for general
claims.

**Primitives:** `by decide`, `native_decide`, `Decidable`, finite-list checks.

**Avoid:** using evaluation to establish an unbounded theorem; treating a test
vector as universal evidence; concealing a noncomputable or opaque dependency.

**Escalate when:** the proposition is parameterized, the evaluation boundary is
unclear, or the result would be used as a certificate-soundness proof.

## P11 — Coercions and arithmetic domains

**Use when:** a proof crosses `Nat`, subtypes, `Int`, or algebraic structures.

**Preferred approach:** keep the main proof in `Nat` when maps are natural;
introduce a coercion at one named boundary and immediately prove the required
nonnegativity/divisibility facts.

**Primitives:** `norm_num`, `omega`, `exact_mod_cast` only after checking the
target type, subtype `.val` and constructor obligations.

**Avoid:** coercion-driven rewrites across an entire proof; moving to `Int` to
avoid natural subtraction/division obligations; relying on inferred coercions
in a theorem intended for reuse.

**Escalate when:** casts obscure the invariant or a cancellation fact changes
meaning between `Nat` and `Int`.

## P12 — Mathlib source and API search

**Use when:** CI reports an unknown identifier, application mismatch, or
implicit-argument inference failure.

**Preferred approach:** read the pinned v4.33.0 Mathlib source first; copy the
exact declaration shape; record its path/URL and signature in the PR before a
rerun; make a minimal compiling helper before editing a larger theorem.

**Primitives:** GitHub source at the pinned revision, CI error signatures,
repository imports, `#check` only where allowed by project validation policy.

**Avoid:** name-guess loops, searching a newer Mathlib release, or changing a
proof architecture before establishing whether the problem is an API mismatch.

**Escalate when:** two source-backed formulations fail, an import is missing,
or the needed result is project-specific rather than in Mathlib.

## P13 — Escalation and PR hygiene

**Use when:** a proof attempt stops converging or a PR changes claim scope.

**Preferred approach:** report head SHA, exact CI error, failed formulations,
the target statement, source facts checked, and the smallest decision needed.
Keep a failed proof branch open only if it is explicitly preparatory and its
theorem-status/PR wording say so.

**Primitives:** GitHub CI logs, `docs/theorem-status.md`, story acceptance
criteria, review comments, checkpoint receipts.

**Avoid:** serial speculative CI pushes; adding `sorry` to a closure PR;
removing pending declarations; presenting an admission-budget pass as proof.

**Escalate when:** two logical attempts fail, a proof needs a new shared lemma,
or a proposed change weakens a statement/domain/trust boundary.

## Maintenance Policy

- Hard cap: **250 lines**. Replace or compress obsolete material; do not append
  an incident log.
- Add a pattern only when backed by compiling repository code or a
  Codex-resolved escalation validated in GitHub CI.
- After resolving a reusable Lean escalation, Codex proposes the smallest
  relevant update to this file; maintainers decide whether to commit it.
- Keep examples schematic unless a copied snippet is known to compile against
  the pinned toolchain. Update or remove API-specific entries when the pinned
  version changes.
