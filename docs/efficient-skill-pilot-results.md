# Efficient-skill pilot results

**Status: partial; no performance variant selected.** This run establishes a
reproducible implementation candidate and checks its local contracts, but it
does not establish token or latency savings. The acceptance targets remain
unmeasured.

## Setup and scope

- Pilot base: `e2a8ebae78f4039c0650f0723a23c10002212fd0` on
  `feature/r03-descent-to-convergence`.
- The replay checkout was isolated at `/tmp/collatz-efficient-skill-pilot/checkout`
  with a separate temporary OpenClaw home/state directory and Python environment.
  No production OpenClaw database or configuration was read or modified. No PR,
  review, push, or merge operation was performed.
- Runtime reported by the CLI: OpenClaw `2026.10.10 (7dc3350)`. The active
  controller route was `openai/gpt-6-luna`; the checked-in independent-review
  dispatcher pins `openai/gpt-6.1-terra` at `high` effort. Pricing and per-model
  cost data were unavailable. Project-local skill inventory: 19 `SKILL.md`
  files. No Gateway or reviewer model was invoked during replay.
- No representative historical packet fixture set or sealed holdout was
  available. Replay episodes: **0**; development/validation/holdout split: not
  run. Existing repository regression tests served only as local checks, not as
  substitutes for replay episodes. No unrelated dirty-file cases were sampled.

## Baseline evidence

The checkout was clean at the base SHA. Commands ran in the isolated checkout;
complete raw logs are retained under
`/tmp/collatz-efficient-skill-pilot/evidence/` and are not committed.

| Gate | Baseline result |
|---|---|
| `make format-check` | Failed before changes: `extract.py` and `tests/test_extract.py` would be reformatted. |
| `make lint` | Failed before changes: 29 errors in the formal-math extractor and its tests. |
| `make test` | 385 passed, 14 failed in 173.98s. Failures included 12 Lean-backed checker cases, the sorry-budget check, and fresh axiom-manifest measurement. |
| `make lean` | Not completed. A fresh dependency build was manually interrupted after several minutes (331/339 targets had appeared in the first attempt); this is not a pass or a failure result. |
| `make cert-test` | Not run separately. Coverage was verified: `make ci` invokes the full `pytest` suite, whose configured discovery includes both checker files named by `cert-test`. |

The 14 baseline test failures and interrupted Lean build were not repaired as
part of this pilot. The failures prevent a clean before/after full-gate
comparison.

## Variants and changes

1. **A — baseline:** unchanged base above.
2. **B — policy/state contracts:** isolated commit `b158de0` (`Align skill
   budgets and recovery contracts`). Review rounds now count total receipts,
   including the initial review: default 2, protocol ceiling 3. The SQL schema
   and one-time migration agree. Reviewer route/effort and continuation-handle
   instructions match the dispatcher. The state/dispatch audit found no
   executable formal-math state store or composite-budget dispatcher; the
   skills now label these as contracts, not runtime-enforced facts. Strategy
   IDs are distinct from error signatures; rollback preserves cumulative RCS,
   budgets, and attempt history. Parallel aggregate usage is informational and
   excluded from leaf sums.
3. **C — executable gate:** isolated commit `d6216c2` (`Add executable full
   validation gate`). `scripts/full_validate.py` runs `make ci` once, fails
   closed on nonzero exit/timeout, and writes raw output to a log path instead
   of stdout. It does not separately re-run `cert-test` because coverage in the
   full pytest suite was checked.
4. **D — concise operational call site:** isolated commit `5e6a099` (`Use the
   executable full validation gate`). The validation skills call the tested
   helper for final validation and retain narrow target checks for repair.

The three implementation commits were carried onto the feature branch as
`a140f39`, `145c0df`, and `826f5ba`. `826f5ba` is the current implementation
checkpoint, **not a metrics-selected performance winner**.

## Validation after changes

- B focused policy/schema/migration and reviewer-resumption checks:
  **17 passed** (`tests/test_formal_skill_contracts.py tests/test_review_resume.py`).
- C executable-helper checks: **5 passed** (`tests/test_full_validate.py`),
  including success, nonzero exit, timeout, missing `make`, and certificate-test
  coverage. Ruff lint/format checks on the new helper and tests passed.
- D combined focused checks: **22 passed** across the formal-skill contracts,
  helper, and reviewer-resumption tests. Ruff lint/format and `git diff --check`
  passed for the scoped changes.
- The current implementation candidate's full gate was invoked once:
  `python3 scripts/full_validate.py --log-dir /tmp/collatz-efficient-skill-pilot/evidence/selected-gate --timeout-seconds 60`.
  It failed closed with exit 2 at the same pre-existing format check, before
  lint, tests, Lean, or axiom audit ran. The raw log is in that `selected-gate`
  directory.

## Limitations and decision

No per-episode token, cached-token, reasoning-token, billed-cost, tool-call,
latency, outcome, or failure-category measurements exist. Sample size is zero,
so p50/p95 latency and uncertainty are not estimable. The 20% token-reduction
target and no-p95-regression target were **not evaluated**. There is no basis to
claim efficiency improvement or to transfer any general accuracy threshold to
formal correctness.

The policy clarification and fail-closed gate helper are implemented and their
focused tests pass, but the pilot remains partial until the baseline gates are
repaired or classified on a supported host, a representative secret-free
fixture set is split into development/validation/sealed holdout, and controlled
model replays produce comparable usage and latency metrics. No holdout result
is claimed.
