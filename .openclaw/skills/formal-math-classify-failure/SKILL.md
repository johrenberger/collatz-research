---
name: formal-math-classify-failure
description: "Assign exactly one failure class (LOCAL/STRUCTURAL/etc.) to a validation failure before any repair attempt."
---

# Formal Math Engineering — CLASSIFY_FAILURE State

> Agent-driven. Use when the `formal-math-engineering` profile is active and VALIDATE has produced a failure.

Every failed validation is assigned **exactly one** primary class before any further action.

> **Effect label:** classification itself is `effect_label = "op_LLM"`. Normalisation of the failure signature (excluding volatile fields) is `deterministic` — performed by the dispatcher before the orchestrator sees the record. This split is what prevents raw compiler/test transcripts from polluting model reasoning context.

## Failure Classes (one each)

```yaml
failure_types:
  LOCAL:
    description: isolated syntax, type, tactic, or small implementation defect

  STRUCTURAL:
    description: theorem/proof/code structure is incorrect or materially incomplete

  DEPENDENCY:
    description: API, library, version, import, or tool behavior differs from assumptions

  SOURCE_INTEGRITY:
    description: stale reads, encoding, line drift, concurrent mutation, merge state, or source mismatch

  DESIGN:
    description: implementation requires a consequential architecture or trust decision

  UNKNOWN:
    description: root cause has not been established
```

## Transitions

```text
LOCAL              -> REPAIR
STRUCTURAL        -> REASSESS
DEPENDENCY        -> INVESTIGATE
SOURCE_INTEGRITY  -> REFRESH_SOURCE
DESIGN             -> DESIGN_REVIEW
UNKNOWN           -> INVESTIGATE
```

`UNKNOWN` must **never** mean "try another change." It must mean "investigate the root cause."

## Failure Signature (normalized before persisting)

```yaml
failure_signature:
  tool: lean | pytest | ruff | lake | make | other
  category: ""
  symbol: ""
  target: ""
  normalized_message: ""
```

Ignore volatile fields (exact line numbers after edits, metavariable IDs, whitespace, nondeterministic paths).

**New in Stage 1:** the dispatcher performs volatile-field stripping before writing the row to `dispatch_log`. The orchestrator sees only the normalised record. If the orchestrator needs the raw failure output for diagnosis (e.g., for the diagnostic artifact at `RCS ≥ 24`), it MUST explicitly re-dispatch as `code_review` against the saved raw artifact and never paste raw output back into the running context.

## Lean-Specific Failure Modes

For Lean failures, classify into one of:

```text
definitional_reduction
coercion
typeclass_resolution
rewrite_direction
theorem_shape
missing_lemma
unsupported_api
tactic_limitation
malformed_statement
```

Capture: exact goal, local hypotheses, expected type, actual type, relevant expanded definitions, imported theorem/lemma versions.

## Multi-Failure Interpretation

Multiple materially different signatures against the same target consume repair budget aggressively — they indicate an unstable mental model of the implementation, not just a hard problem.

## Hypothesis Required Before Repair

After classification, before any edit, write:

```yaml
repair_hypothesis:
  failure: ""
  proposed_root_cause: ""
  evidence: []
  proposed_change: []
  files_affected: []
  expected_result: ""
  falsification_condition: ""
  strategy_id: ""  # stable repair-approach identity; do not derive from the error fingerprint
```

## Transition

After classification + hypothesis → transition to the appropriate REPAIR / REASSESS / INVESTIGATE / REFRESH_SOURCE / DESIGN_REVIEW sub-action. Do NOT skip the classification step.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"CLASSIFY_FAILURE"` |
| write | `current_sub_state` | the active classification (LOCAL / STRUCTURAL / …) |
| write | `current_hypothesis_json` | RepairHypothesis (the new one being formed) |
| write | `current_strategy_id` | str |
| write | `current_strategy_attempt_count` | `0` (reset on a new strategy_id) |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) after writing the new hypothesis | — | — |
| read | `last_validation_json` | ValidationResult |
| read | `last_validation_exit_code` | int |
| read | `current_strategy_id` | str (to detect "same strategy" → block at attempt 2) |
