---
name: formal-math-codex-escalate
description: "Invoke Codex as an independent reviewer when RCS >= 24, three proof strategies have failed, or a high-risk structural diagnosis needs second-opinion validation."
---

# Formal Math Engineering — CODEX_REVIEW State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has determined that Codex independent review is required (RCS ≥ 24, or 3 materially different failed proof strategies, or high-risk structural diagnosis).

Codex is an **independent reviewer**, not a continuation of MiniMax's repair loop. Codex must not be used to launder MiniMax hypotheses back into the workflow.

> **Stage 1 routing:** the Codex review invocation itself is `effect_label = "code_review"`. It MUST be dispatched via `formal-math-effect-dispatch` with `tools_allow = [read, browser, exec:gh PR view, exec:gh api]` (per `collatz-pr-review-gate`). The reviewer MUST be spawned with a different model alias from the orchestrator (per `collatz-pr-review-gate`: `openai/gpt-5.6-terra`). One-shot; no follow-ups; parent sees only the typed review record.

## When to Invoke Codex

- `RCS ≥ 24` (per BUDGET_CHECK thresholds)
- 3 materially different failed proof strategies against the same target
- High-risk structural diagnosis needing independent validation
- Trust-boundary change (FFI, native code, external verifier)

## Required Context to Provide Codex

```text
- story definition
- current work packet
- diagnostic artifact (from SAVE_DIAGNOSTIC)
- current git diff
- last-green revision
- failing validation output
- relevant Lean/Python files
- MiniMax hypotheses and rejected strategies
- trust-model constraints
```

Do NOT summarize MiniMax's "current approach is right." Codex must diagnose from evidence.

## Required Codex Output (one primary outcome)

```yaml
review_outcome:
  - MINIMAX_STRATEGY_VALID
  - ALTERNATE_STRATEGY_REQUIRED
  - STORY_DECOMPOSITION_REQUIRED
  - SPECIFICATION_DEFECT
  - DEPENDENCY_OR_ENVIRONMENT_DEFECT
  - ARCHITECTURE_DECISION_REQUIRED
  - MATHEMATICAL_DECISION_REQUIRED
```

Codex should diagnose before proposing edits.

## Invocation Method

Codex invocation method may vary by OpenClaw installation. The current OpenClaw installation does not surface an explicit Codex CLI in the tools surfaced to this agent. The intended invocation pattern (per the workflow spec) is to spawn an independent review pass with the context above. If the installed OpenClaw version does not support a direct Codex invocation, surface the gap in the final report and fall back to:

1. Generate the diagnostic artifact.
2. Stop source editing.
3. Escalate to `HUMAN_GATE` with the artifact and the context Codex would need.

## Post-Review Behavior

If Codex supplies a concrete alternate strategy:

```yaml
post_review_budget:
  max_rcs: 12
  reset_error_history: false
  reset_strategy_history: false
```

Historical failures remain visible. Do NOT erase evidence because a reviewer was invoked.

Do NOT automatically let MiniMax repeat a previously exhausted strategy merely because Codex review occurred.

## Transitions

- If Codex returns `MINIMAX_STRATEGY_VALID` → transition to `IMPLEMENT` (continue with the validated strategy).
- If Codex returns `ALTERNATE_STRATEGY_REQUIRED` → transition to `IMPLEMENT` with the new strategy (under post-review budget).
- If Codex returns `STORY_DECOMPOSITION_REQUIRED` → transition to `PLAN_UPDATE` (re-plan the story).
- If Codex returns `SPECIFICATION_DEFECT` / `DEPENDENCY_OR_ENVIRONMENT_DEFECT` / `ARCHITECTURE_DECISION_REQUIRED` / `MATHEMATICAL_DECISION_REQUIRED` → transition to `HUMAN_GATE` with the Codex outcome as decision context.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"CODEX_REVIEW"` |
| write | `current_sub_state` | `dispatch_reviewer \| interpret_outcome` |
| write | `current_hypothesis_json` | `null` (cleared pending Codex's verdict) |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) on exit | — | — |
| read | `current_hypothesis_json` (pre-Codex snapshot) | RepairHypothesis |
| read | `last_validation_json` | ValidationResult |
| read | `last_validation_exit_code` | int |
| read | `current_rcs`, `current_strategy_id`, `current_strategy_attempt_count` | (pass to Codex as context) |
