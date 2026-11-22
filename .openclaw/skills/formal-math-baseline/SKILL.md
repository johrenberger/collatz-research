---
name: formal-math-baseline
description: "Capture the last-known-good Lean/Python build state before any modification; required first state on `formal-math-engineering`."
---

# Formal Math Engineering — BASELINE State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has transitioned to `BASELINE`.

BASELINE is **mandatory before any modification**. Capture the last-known-good state so the controller can recover if a repair attempt breaks the build.

> Every primitive in this state is `effect_label = "deterministic"` and MUST route through `formal-math-effect-dispatch`. The orchestrator must not run `make ci`, `make lean`, `make test`, `lean`, `pytest`, or `ruff` directly in its reasoning context.

## Required Output: `baseline`

```yaml
baseline:
  base_branch: ""
  current_branch: ""
  git_commit: ""
  git_status: ""
  lean_build: pass | fail
  python_tests: pass | fail
  ci: pass | fail
  existing_sorry_count: 0
  target_test_status: ""
  timestamp: ""
```

## Required Persistence

```text
LAST_GREEN_COMMIT
LAST_GREEN_LEAN_BUILD
LAST_GREEN_PYTHON_TEST
LAST_GREEN_CI
CURRENT_EXPERIMENT_START
```

Persist these as named references in the persistent runtime state.

## Baseline Definition for Projects with Pre-Existing Sorry

```text
No regressions relative to baseline and no unapproved new proof debt.
```

Do NOT require historical proof debt to be eliminated unless the story owns it.

## Transition

After BASELINE is captured and persisted, transition to `IMPLEMENT` (or to the first work packet's IMPLEMENT).

Do NOT proceed to `IMPLEMENT` until `LAST_GREEN_*` are recorded and the baseline YAML is persisted.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"BASELINE"` |
| write | `current_sub_state` | `"capture_last_green"` |
| write | `last_green_commit` | str (LAST_GREEN_COMMIT) |
| write | `proof_debt_baseline` | int (existing sorry/admit count) |
| write | `trust_boundary_baseline_json` | TrustBoundary (JSON) |
| write | `trust_boundary_current_json` | TrustBoundary (JSON, initially = baseline) |
| write | `state_updated_at` | iso8601 |
| write | `current_rcs` | `0.0` (reset at baseline) |
| write | `current_strategy_id` | `null` |
| write | `current_strategy_attempt_count` | `0` |
| write | `current_hypothesis_json` | `null` |
| checkpoint (χ) on exit | — | — |
| read | `branch`, `work_packet_id` | str |
