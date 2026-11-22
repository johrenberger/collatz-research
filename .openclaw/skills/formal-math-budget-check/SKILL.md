---
name: formal-math-budget-check
description: "Compute the Repair Cost Score and decide whether repair continues, reassesses structurally, escalates to Codex, or hard-stops."
---

# Formal Math Engineering — BUDGET_CHECK State

> Agent-driven. Use when the `formal-math-engineering` profile is active and a repair hypothesis has been formed.

BUDGET_CHECK enforces the Repair Cost Score (RCS) thresholds. It determines whether further repair is allowed, or whether the controller must transition to structural reassessment, Codex review, or hard stop.

> **Effect label:** RCS arithmetic and threshold comparison are `deterministic` — performed by the orchestrator via EFFECT_DISPATCH on a typed reading of `dispatch_log`. Any narrative interpretation of "what does this RCS level mean for this work packet" is `op_LLM`. The numeric state stays in the typed record; only the policy *decision* is model-attended.

## Repair Cost Score (RCS)

```text
RCS = 4.0 · Lean validation failures
    + 2.0 · Python unit/integration test failures
    + 1.0 · Python lint/type/static failures
    + 4.0 · distinct normalized error signatures
    + 2.0 · repair attempts
    + 0.5 · tool actions after first failure
    + 2.0 · estimated token usage in thousands after first failure
```

A single event must NOT be double-counted as both a Lean and Python validation failure.

## Thresholds

```yaml
repair_budget:
  structural_reassessment_at: 12
  independent_review_at: 24
  hard_stop_at: 32
  same_strategy_attempt_limit: 2
```

### Structural reassessment at RCS ≥ 12

STOP source editing. Perform read-only structural analysis. Only these transitions are allowed afterward: `REPLAN`, `RESTORE_GREEN`, `INDEPENDENT_REVIEW`.

### Independent review at RCS ≥ 24

Checkpoint valid progress, generate the diagnostic artifact, restore a safe state when needed, and invoke Codex as independent reviewer.

### Hard stop at RCS ≥ 32

No further implementation by MiniMax unless Codex supplies a materially new reviewed strategy and the controller explicitly grants a post-review budget.

### Same-strategy attempt limit: 2

Minor tactic reordering does NOT count as a new strategy. Materially same strategy × 2 failed attempts → BLOCK. Require different strategy or reassessment.

## Strategy History Tracking

```yaml
strategy_history:
  - strategy_id: S1
    target: "Lean/CollatzResearch/Affine.lean:AffineMap.comp_apply_eq"
    attempts: 2
    result: failed
```

Persist strategy history in the runtime state. A new context window must NOT reset retry counts or make an exhausted strategy appear new.

**Stage 1 addition:** strategy_history is also keyed against `dispatch_log` rows so that any `failure_signature` repeating across cycles is matched deterministically. Two `dispatch_result`s with the same `failure_signature.fingerprint` after normalisation count as the same strategy. The dispatcher computes fingerprints on append.

## Same Target + Materially Same Strategy + 2 Failed Attempts → Block Strategy

```text
CONTROLLER RULE: same target + materially same strategy + 2 failed attempts
                       => block strategy
                       => require structural reassessment or a materially different strategy
```

## Post-Review Budget (if Codex supplies an alternate strategy)

```yaml
post_review_budget:
  max_rcs: 12
  reset_error_history: false
  reset_strategy_history: false
```

Historical failures remain visible. Do NOT erase evidence because a reviewer was invoked.

## Transitions Out of BUDGET_CHECK

- `RCS < 12 && strategy not blocked → IMPLEMENT`
- `RCS ≥ 12 → structural reassessment; source editing stops`
- `RCS ≥ 24 → SAVE_DIAGNOSTIC → RESTORE_GREEN → CODEX_REVIEW`
- `RCS ≥ 32 → HARD STOP`
- Same strategy × 2 failed attempts → BLOCK strategy; require different strategy or reassessment

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"BUDGET_CHECK"` |
| write | `current_sub_state` | `"compute_rcs"` |
| write | `current_rcs` | float (recomputed) |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) on exit | — | — |
| read | `last_validation_exit_code`, `last_validation_json` | (derive failure counts and distinct signatures) |
| read | `current_strategy_id`, `current_strategy_attempt_count` | (detect same-strategy block) |
