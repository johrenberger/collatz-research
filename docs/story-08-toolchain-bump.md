# Story 08 — Toolchain bump (Lean 4 / Mathlib v4.19.0 → latest stable)

## Claim level

**Math claim: preparatory.** Story 08 establishes no new theorems; it
only bumps infrastructure (Lean toolchain + Mathlib version). No
existing theorem changes its claim level as a side effect of this
story.

**Implementation state: Phase 1 in progress.** PR #32
(`story-08-toolchain-bump`, opened 2026-08-16 ~20:12 GMT+2) is actively
executing Phase 1. The doc was originally drafted as a long-term plan
with a green-gate on the 02c/03c proof-bearing PR (`771cd3c`); that
gate was waived by explicit user directive (2026-08-17 ~05:00 GMT+2)
so the toolchain bump could proceed in parallel with 02c/03c. See
"Implementation log (PR #32)" below for the commit-by-commit causal
narrative.

## Background

Current pin (2026-08-16):

- `lean-toolchain`: `leanprover/lean4:v4.19.0`
- `lakefile.toml`: `mathlib.rev = "v4.19.0"`
- `lake-manifest.json`: pinned to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`

Latest Mathlib releases at the time of this doc:

| Tag | Released |
|---|---|
| `v4.34.0-rc1` | 2026-08-11 |
| `v4.33.0` | 2026-08-10 |
| `v4.33.0-rc2` | 2026-08-03 |
| `v4.32.2` | 2026-07-28 |
| `v4.32.1` | 2026-07-23 |

We are **~15 minor versions behind current**. v4.19.0 shipped in late
2024. The frame-of-reference drift is real: new lemmas have been
added, several lemmas have been renamed, some tactics have new
signatures, and Mathlib's preferred proof styles have evolved (e.g.,
greater use of `ordCompl` / `ordProj`, the `Finsupp`-style
factorization chains are deprecated in favor of `Nat`-based ones in
some areas).

## Why this matters

1. **Frame-of-reference drift (PRIMARY concern)**: as documented in the
   2026-08-16 session, my guesses for Mathlib lemma names during the
   02c/03c proof-bearing PR work (`Nat.odd_iff`, `Nat.factorization_pos_iff_dvd`)
   didn't exist on v4.19.0. Several attempts failed until I read the
   Mathlib source. Newer Mathlib versions are likely to have cleaner,
   more discoverable lemma names — the kind a non-source-inspecting
   workflow would find on the first try.

2. **Hidden cost on every PR**: each new proof currently requires
   `git clone` of Mathlib + `rg` over source files to find correct
   lemma names. This adds ~5–10 minutes per proof attempt and makes
   every "natural" formulation a multi-attempt exercise.

3. **Tech-debt multiplier**: each future Mathlib release moves the
   goalposts. Within a year, v4.19.0 will be 2+ years stale and the
   gap compounds. Catching up once a year keeps the workflow smooth.

4. **Mathlib upstream improvements**: the factorization API has been
   cleaned up between v4.19 and v4.34 (notably the `ordCompl` /
   `ordProj` infrastructure we ended up using). Newer Mathlib might
   have direct lemmas for "dividing by 2-adic valuation leaves an odd
   result" without manual definition unfolding.

## Objective

Bump the Lean 4 toolchain and Mathlib dependency to **the latest
stable Mathlib release at execution time**, updating the
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` accordingly
and adapting all project Lean sources to compile cleanly under the new
version with **zero new `sorry`/`admit`/`axiom`** introduced.

Target Mathlib at execution time: **the most recent stable `vX.Y.Z`**
tag on `leanprover-community/mathlib4` at the moment the bump PR
opens. (Prefer stable over `-rc` releases unless the stable release
is days away.)

## Scope

### In scope

- `lean-toolchain` bump
- `lakefile.toml` Mathlib `rev` + `require.git` update
- `lake-manifest.json` regeneration via `lake update`
- Compilation fixes in:
  - `Lean/CollatzResearch/Basic.lean`
  - `Lean/CollatzResearch/Dynamics.lean`
  - `Lean/CollatzResearch/Equivalence.lean`
  - `Lean/CollatzResearch/Certificate.lean`
  - `Lean/CollatzResearch/Affine.lean`
  - `Lean/CollatzResearch/CoverageTree.lean`
  - `Lean/CollatzResearch/CoverageTreeOrbitTests.lean`
  - `Lean/CollatzResearch/Importer.lean`
  - `Lean/CollatzResearch/Residues.lean`
- CI config alignment:
  - `.github/workflows/lean-ci.yml`
  - (if needed) `.github/workflows/nightly.yml`,
    `.github/workflows/python-ci.yml`, `.github/workflows/reproducibility.yml`
- `lake-manifest.json` regeneration
- `README.md` toolchain-table updates
- `MEMORY.md` toolchain-section updates

### Out of scope

- **No new mathematical features.** This is a maintenance bump; no
  theorems are added, removed, or strengthened.
- **No new sorry / admit / axiom.** The bump must preserve the
  current admission count exactly.
- **No claim-level changes.** All existing `preparatory` /
  `formally established` claims stay at their current level.
- **No performance optimization.**
- **No Python-side changes** unless a Mathlib dep is removed that
  Python was mirroring.
- **No lake-cache refactor.** The shared Lake cache workflow stays;
  only the `lake-manifest.json` is regenerated.

## Required changes (in execution order)

1. **Pre-flight (informational)**: note the current `lake-manifest.json`
   Mathlib commit hash so we can produce a diff if needed. Capture
   the existing CI green run IDs (post-02c/03c merge).

2. **Toolchain bump (infrastructure PR)**:
   - Update `lean-toolchain` from `v4.19.0` to a Lean 4 version
     compatible with the target Mathlib.
   - Update `lakefile.toml` Mathlib `rev` from `"v4.19.0"` to the
     target tag.
   - Run `lake update` (CI-only; not locally per project BDD
     discipline) to regenerate `lake-manifest.json`.
   - Commit as **infrastructure-only** (no Lean-source edits). Per
     the 2026-08-16 Codex-review pattern: separate infrastructure
     commits from proof commits for causal clarity.

3. **Breakage survey (read-only)**:
   - Trigger GitHub Lean CI on the infrastructure commit.
   - Collect the full build log; identify every Lean-source file
     that fails to compile.
   - Categorize each failure:
     - **Lemma renamed** (e.g., `Nat.odd_iff` renamed to `Nat.odd`)
     - **Lemma removed** (rare; Mathlib usually deprecates rather
       than removes)
     - **Signature changed** (argument order or implicitness)
     - **Import path changed** (a file moved)
     - **Tactic behavior changed** (e.g., `omega` improvements)
   - Update the per-file mapping table at the bottom of this doc
     as a planning aid.

4. **Source adaptation (one commit per file or logical group)**:
   - Fix each file's breakages in isolation.
   - Each commit message must:
     - List the Mathlib version that introduced each breakage
     - Cite the upstream Mathlib commit hash if relevant
     - Use `git grep` or `rg` on a sparse Mathlib checkout at the
       target version for the new lemma names
   - **Constraint**: zero new `sorry` / `admit` / `axiom`. The bump
     is purely mechanical; if a lemma genuinely no longer exists in
     the new Mathlib, escalate to PR description + open question,
     do **not** silently insert `sorry`.

5. **Validation**:
   - GitHub Lean CI green at the target version.
   - `lake build CollatzResearch.CoverageTree` succeeds.
   - `tests/test_coverage_tree.py` (the only file exercising Lean
     runtime behavior) still passes 77/77 (or current count + new
     tests added during the bump if any).
   - `scripts/check_sorry_budget.py` reports no new admissions.

6. **Documentation sync**:
   - `README.md`: update the toolchain table.
   - `MEMORY.md`: update the Open `Lean toolchain` line + the
     per-admission risk table if any lemma rename is notable.
   - This story doc: update the "Current pin" table at top to
     reflect the new version.

## Execution sequence (phased)

### Phase 1 — Infrastructure

Single commit touching only:

- `lean-toolchain`
- `lakefile.toml`
- `lake-manifest.json` (regenerated)

Push; wait for CI. **No Lean-source files touched in this phase.**

If CI fails on infrastructure (e.g., lake cache corruption, broken
cache disable), fix that first per the 2026-08-16 pattern (Codex
review #1 on PR #31): add an infrastructure-only CI patch.

### Phase 2 — Source adaptation

Iterate over the Lean-source files in dependency order
(`Basic.lean` → `Dynamics.lean` → `Equivalence.lean` →
`Certificate.lean` → `Affine.lean` → `CoverageTree.lean` →
`CoverageTreeOrbitTests.lean` → `Importer.lean` → `Residues.lean`).
For each file, **one commit per file** with the breakage list in
the commit body. **No combined "fix everything" commits**; per-commit
attribution keeps the diff navigable.

If a breakage is **unfixable** (lemma genuinely gone in the new
Mathlib), pause and open a PR conversation — do not insert `sorry`
to mask the issue.

### Phase 3 — Validation

- CI green on the full branch.
- `scripts/check_sorry_budget.py` confirms no new admissions.
- All existing Python tests pass.
- A spot-check of `Lakefile.toml`'s `defaultTargets` builds clean.

### Phase 4 — Merge

- Single PR or split PRs (infrastructure / per-file / docs). The
  preferred approach is **one PR per phase** for reviewability.
- Codex review of each PR (since the bump touches mathematical
  infrastructure, the project's standard Codex review applies).
- Merge into `agent/bootstrap-research-monorepo`.

## Non-goals

- **No mathematical claim changes.** All proofs at their current
  claim level (`preparatory` / `formally established`).
- **No new sorry / admit / axiom.**
- **No claim-level promotion** as a side effect (e.g., closing a
  "conjectured → formally established" gap is its own story).
- **No Python refactor** unless a Mathlib dep is removed.
- **No tooling changes beyond Lean/Mathlib** (e.g., not touching
  `uv` / `ruff` / `pytest` versions).

## Risks

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Mathlib `Nat.odd_iff` rename | High | Low | Use the lookup workflow (sparse Mathlib checkout + `rg`); the 02c/03c PR already established the pattern |
| `lake update` regenerates `lake-manifest.json` with hash conflicts | Medium | Medium | Commit `lake-manifest.json` separately; resolve via `lake update --self` if needed |
| Multiple files need simultaneous fixes | High | Medium | Phase 2's per-file commits keep the diff reviewable; if 1+ files need > 10 lines of change each, split into smaller PRs |
| New Mathlib introduces stricter `omega` checks | Low | Low | Re-verifiable locally (omega is a Mathlib internal) |
| Python `lake build` cache regression | Low | Medium | Disable `use-github-cache` per the 2026-08-16 infrastructure patch; Mathlib cache stays |
| Lean 4 minor version bumps require recompiling Mathlib (slow first CI run) | High | Low (time only) | First CI run will be slow (~10–20 min for full Mathlib rebuild); subsequent runs use cache |
| New Mathlib has stricter admission budget (e.g., new `sorry` lemmas introduced upstream) | Low | High | Phase 3's `check_sorry_budget.py` will catch this; escalate via PR comment |
| Bump breaks 07c-4 orbit routing theorem (`descend_orbit_complete`) | Low | High | Phase 3's per-file commits; if `descend_orbit_complete` regresses, isolate to a separate fix PR |

## Per-file expected breakages (provisional — verify in Phase 2)

Based on the 2026-08-16 session evidence:

| File | Likely breakage area |
|---|---|
| `Basic.lean` | `ordCompl` / `ordProj` notation might be re-exported differently; `Nat.mod_two_ne_zero` might be renamed |
| `Dynamics.lean` | `Odd.pos` should still exist; `omega` improvements might simplify existing `sorry`-free proofs |
| `Equivalence.lean` | `Nat.factorization_div` might have a slightly different signature |
| `Certificate.lean` | `acceleratedStep_odd_of_odd` no longer exists here (relocated to `Basic.lean` in PR #30 spec, per PR #30 architectural decision); expected to compile clean |
| `Affine.lean` | `Nat.mul_div_cancel_left_of_dvd` / `Int.mul_div_cancel_left_of_dvd` availability — depends on the 04b workstream |
| `CoverageTree.lean` | `OrbitRoute` inductive should be stable; `accelerated_orbit` definitions unchanged |
| `CoverageTreeOrbitTests.lean` | If executable specs change, this needs re-validation |
| `Importer.lean` | Low risk |
| `Residues.lean` | Low risk |

This table will be replaced with the actual breakage survey from
Phase 2 when the bump PR opens.

## Implementation log (PR #32)

**Branch**: `story-08-toolchain-bump` from `agent/bootstrap-research-monorepo` @ `abca1ea` (PR #30 / 02c/03c spec merged).
**Target**: Lean 4 `v4.33.0` + Mathlib `v4.33.0` (chosen 2026-08-16;
v4.34.0-rc1 avoided per stability preference).
**Open**: 2026-08-16 ~20:12 GMT+2.

### Commit sequence and CI outcomes

| # | SHA | Commit | Outcome |
|---|---|---|---|
| 1 | `abfde77` | toolchain + lakefile.toml bump | ❌ cache mismatch — cached `.olean` files were toolchain-keyed (`Lean.Util.Paths.olean` not built for v4.33.0) |
| 2 | `c5d2366` | disable `use-github-cache` + `use-mathlib-cache` | ❌ lake-manifest still pinned to v4.19.0 Mathlib commit; ~200 upstream errors |
| 3 | `4e3c135` | lake-manifest.json Mathlib entry → v4.33.0 (`db584cd6d…`) | ❌ transitive deps (aesop, batteries, plausible, …) still pinned to old revs; build halted before Mathlib was reached |
| 4 | (this commit) | lake-manifest.json transitive-dep revs → v4.33.0-compatible; spec doc claim + status sync | pending |

### Root-cause narrative

Each failure was a **stale-cache** or **stale-manifest** issue, not a
source-code issue. The original `lake update` (run locally on
2026-08-16) failed with a working-copy conflict on `lake-manifest.json`
and never produced a usable regeneration. Subsequent manual edits then
addressed deps one layer at a time:

1. **Toolchain bump** (commit 1) invalidated cached `.olean` files
   (cached artifacts are toolchain-specific).
2. **Caches off** (commit 2) made lake fetch source per the
   lake-manifest, which still pointed at v4.19.0 → v4.19.0 Mathlib
   source compiled against v4.33.0 stdlib → ~200 upstream errors.
3. **Mathlib entry fixed** (commit 3) made lake fetch v4.33.0 Mathlib
   but the transitive deps (aesop, batteries, etc.) still pointed at
   commits that pre-dated Lean v4.33.0 stdlib changes → build halted
   on Aesop.Check / Batteries.Data.String.Basic before Mathlib was
   ever reached.
4. **Commit 4** (this) updates the transitive-dep revs to the
   commits Mathlib's own `v4.33.0` `lake-manifest.json` references.

### Working-tree state at commit 4

Mathlib line unchanged from commit 3. Transitive-dep revs (all
inherited from Mathlib's `v4.33.0` manifest):

```
plausible        77e08edd…  →  b7eb3304aeae
LeanSearchClient 25078369…  →  5f4d51b81cbd
importGraph      e6a9f0f5…  →  16f02aa76428
proofwidgets     c4919189…  →  4be2e3d5087e
aesop            5d50b08d…  →  3448c0bcc5ce
Qq               fa4f7f15…  →  92c15be17b7c
batteries        f5d04a9c…  →  4488d40d070b
Cli              02dbd02b…  →  6130a47896ce   (inputRev: main → v4.33.0)
```

These revs appeared in the working tree between commit 3 and commit 4,
likely from a `lake update` that ran in an intermediate bot session
(2026-08-16 ~22:30 — 2026-08-17 ~05:20 GMT+2). The `lake update`
modified `lake-manifest.json` but never committed cleanly.

### Next steps

If commit 4 CI goes green → merge PR #32, start Phase 2 (source
adaptation, per-file per the existing plan above).

If commit 4 CI surfaces `CollatzResearch.*` errors → Phase 2 begins
immediately; iterate per-file per the existing plan; the per-file
expected-breakages table above becomes the starting checklist.

### 02c/03c parallel

PR `#story-02c-03c-proofs` (head `771cd3c`, failed CI 31969… at
2026-08-16 19:58) is the proof-bearing PR for the 02c/03c sorries.
It runs on the **pre-bump** toolchain (v4.19.0) and is independent
of PR #32. If PR #32 merges first, the proof-bearing PR will need
its own Phase 2 re-validation under v4.33.0; if 02c/03c merges first,
PR #32 may need a rebase.

## Status

**Started 2026-08-16.** Doc drafted in response to the frame-of-
reference drift observed during the 02c/03c proof-bearing PR work
(2026-08-16 session). PR #32 opened the same day and entered
Phase 1 (infrastructure-only). See "Implementation log (PR #32)"
above for the commit-by-commit narrative. **Phase 1 status**:
4th commit pending; Phase 2 (source adaptation) pending.

## Follow-on work

After this bump lands, consider:

- **Annual cadence**: schedule a toolchain bump every ~6 months.
  Could be tracked via `nightly.yml` alerts that warn when Mathlib
  is > N releases behind `nightly`.
- **CI signal**: add a step in `lean-ci.yml` that prints the Mathlib
  commit hash and warns if it's > 6 months old.
- **`.elan` toolchain management**: pin `lean-toolchain` via
  `lean-toolchain` file (already done); consider using
  `lean-release/lean4:nightly` for a fast-feedback channel.

## Acceptance criteria

The bump PR is acceptable when:

1. `lean-toolchain` is the latest stable Lean 4 release for the
   target Mathlib.
2. `lakefile.toml` Mathlib `rev` matches the target Mathlib tag.
3. `lake-manifest.json` is regenerated and committed.
4. **All existing Lean files compile without new `sorry`/`admit`/`axiom`**.
5. GitHub Lean CI is green on the final commit.
6. `tests/test_coverage_tree.py` passes 100% (count may increase
   if new tests are added; count must not decrease).
7. `scripts/check_sorry_budget.py` reports no new admissions.
8. `MEMORY.md` and `README.md` reflect the new toolchain.
9. Codex review approves the final PR.

**Close criterion**: PR merged into `agent/bootstrap-research-monorepo`;
this story doc updated with the actual breakage summary and
resolution.