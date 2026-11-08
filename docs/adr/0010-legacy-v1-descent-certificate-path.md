# ADR 0010 — Retire the legacy v1.0 Lean descent-certificate path, relocating its proven content

- **Status:** Accepted (maintainer decision, 2026-11-07)
- **Decides:** NT-5 decision 3 in `docs/convergence-frontier.md` § 9
- **Work packet:** WP-CF-5
- **Supersedes:** nothing. Extends [ADR 0009](0009-reachability-evidence-tier.md) (the reachability evidence tier), which is unaffected.

## Context

The legacy v1.0 descent-certificate path spans two Lean modules:

| File | Admitted declaration | Notes |
|---|---|---|
| `Importer.lean` | `parseV1Record` | The v1.0 JSONL record parser body is a `sorry`. |
| `Importer.lean` | `parseJsonl` | The JSONL splitter body is a `sorry`. |
| `Certificate.lean` | `check_certificate_sound` | Three `sorry` holes for the parser-derived constraints `0 < r.start`, `Odd r.start`, `r.target < r.start`. |

The blocking dependency is real: `check_certificate_sound`'s anti-circularity argument rests on a SHA-256 digest of the proof-bearing fields, and only the Python side computes it (`python/collatz_research/canonical.py`, `compute_digest`). There is no `Digest.lean` in `main`. Completing the Lean side would mean writing a Lean SHA-256 implementation — a significant addition to the trusted computing base that belongs in its own story.

The Q5 routing-partition architecture bypasses this path entirely.

The three admitted declarations are not the whole cost of retiring it. `Certificate.lean` also carries **proven** content:

- `DescentWitness` (structure) and `DescentWitness.Valid` (predicate)
- `DescentWitness.Valid.ends_at`, `.strict_descent`, `.start_pos_odd` (all Checked)
- `DescentWitness.trajectory_odd` (Checked)

Deleting the files outright would discard these proven descent lemmas — a content loss, not merely a budget change.

## Decision

**Retire the legacy v1.0 Lean descent-certificate path, relocating the proven witness infrastructure rather than deleting it.**

Concretely:

1. `Lean/CollatzResearch/Importer.lean` and `Lean/CollatzResearch/Certificate.lean` are **removed**. This retires all three admitted declarations.
2. The **proven** witness infrastructure moves to a new module, `Lean/CollatzResearch/DescentWitness.lean`: the `DescentWitness` structure, the `DescentWitness.Valid` predicate, and the `ends_at` / `strict_descent` / `start_pos_odd` / `trajectory_odd` lemmas, with their statements unchanged. No proven descent lemma is lost.
3. The Python side of the v1.0 format is **untouched**: the format, its parser (`parser.py`), its checker (`checker.py`), and its certificate builder (`certificates.py`) all remain live and tested. Only the *Lean* v1.0 bridge is retired.

## Consequences

- The Lean release-relevant modules carry **one** admitted declaration after this change (`coverage_tree_soundness_orbit` in `CoverageTree.lean`), down from four. `docs/lean-sorry-budget.json` drops the `Importer.lean` (2) and `Certificate.lean` (1) rows and adds `DescentWitness.lean` (0).
- The Python differential test (`tests/test_checker_lean.py`) re-points its generated Lean fixture from `import CollatzResearch.Certificate` to `import CollatzResearch.Basic`, which is where `CollatzResearch.trajectory` is defined. `Basic.lean` imports only Mathlib, so there is no import cycle.
- `docs/theorem-status.md` drops the three retired admitted rows and retargets the five `DescentWitness` rows to `CollatzResearch.DescentWitness`.
- The surviving module makes no convergence, cycle-exclusion, or global descent claim. `Valid` remains a structural predicate about a declared witness; the lemmas remain projections from it plus oddness preservation along the trajectory.

## Alternatives considered

- **(a) Retire with relocation** — **chosen**, above.
- **(b) Retire by deletion** — rejected: it would drop four proven descent lemmas for no gain.
- **(c) Complete the path** (write a Lean SHA-256 module) — rejected as out of scope: a substantial addition to the trusted computing base that should be scoped as its own story, not as the tail of a disposition decision.
- **(d) Keep as is** — rejected: the budget keeps three admitted declarations for a path the current architecture bypasses, and the digest gap stays undocumented.

## Evidence

| Claim | How verified |
|---|---|
| The three admitted declarations | `docs/lean-sorry-budget.json` plus the `sorry` sites in the two removed files |
| No Lean SHA-256 module | `Lean/CollatzResearch/Digest.lean` absent; the Python digest is in `canonical.py` |
| The proven lemmas are unused outside the two files | `grep` over `Lean/`, `tests/`, `python/`, `scripts/` |
| `trajectory` lives in `Basic.lean`, which imports only Mathlib | `Basic.lean` head; no cycle with `DescentWitness.lean` |
| The Python v1.0 tooling remains live | `parser.py`, `canonical.py`, `checker.py`, `certificates.py` present and tested |
