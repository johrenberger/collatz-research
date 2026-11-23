---
name: formal-math-diagnostic
description: "Save a portable Markdown diagnostic artifact capturing the full failed-experiment state for human or Codex review without re-running anything."
---

# Formal Math Engineering — SAVE_DIAGNOSTIC State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has determined that a diagnostic artifact must be generated (RCS ≥ 24, Codex review requested, human escalation requested, or hard-stop threshold reached).

SAVE_DIAGNOSTIC captures the full state of the failed experiment into a portable Markdown artifact that a human or Codex can review without re-running anything.

> **Stage 1 routing:** the artifact is composed of:
>
> - `dispatch_log` rows (typed records) — `deterministic` collection + `op_LLM` schema assembly
> - last green commit, current commit, current diff — `deterministic`
> - failing Lean/Python context — `deterministic` reads of saved files
> - narrative diagnosis summary — `op_LLM`
>
> The orchestrator NEVER inlines the raw diff into the running context. The artifact is written to disk via an `op_LLM` EFFECT_DISPATCH call (with declared `tools_allow = ["write", "apply_patch"]` for the diagnostic path) and read back only by the next `code_review` leaf (Codex), also via the dispatcher.

## Required Output Location

```text
.openclaw/diagnostics/<STORY-ID>/escalation-<NNN>.md
```

`<NNN>` is a zero-padded sequence number. The directory is created on demand.

Do NOT commit diagnostics to the repository by default.

## Required Schema

```markdown
# Execution Diagnostic

## Story
Story ID:
Branch:
Current commit:
Last green commit:
Work packet:

## Objective

## Current Status
Completed:
Incomplete:
Blocked:

## Acceptance Criteria Status
- [ ]

## Repair Budget
Repair Cost Score:
Threshold:
Lean failures:
Python failures:
Distinct error signatures:
Repair attempts:
Tool actions:
Estimated tokens:

## Failure Timeline

### Attempt 1
Strategy:
Hypothesis:
Change:
Command:
Failure signature:
Result:

## Current Diff
Summary:
Files changed:
Relevant diff excerpts:

## Lean State
Lean version:
Mathlib revision:
Target theorem:
Goal:
Local context:
Outstanding sorry/admit:

## Python State
Relevant tests:
Reference implementation:
Counterexample results:

## Structural Diagnosis
Root cause:
Invalidated assumptions:
Current strategy viability:

## Alternatives

### Option A
Description:
Benefits:
Risks:

### Option B
Description:
Benefits:
Risks:

## Recommended Next Action

## Decision Required
None | Technical review | Architecture | Mathematical specification | Trust boundary

## Commands to Reproduce
```bash
# commands
```
```

## Capture Steps (in order)

```text
1. Read git status, branch, commit hash (current and LAST_GREEN).
2. Compute the RCS from the runtime state (failures, distinct signatures, repair attempts, tool actions, tokens).
3. List all repair attempts and their strategy IDs.
4. Read the failing Lean goal + local context (for Lean failures).
5. Read the relevant Python test/reference implementation (for Python failures).
6. Read the current git diff vs. the last-green commit.
7. Write the artifact to .openclaw/diagnostics/<STORY-ID>/escalation-<NNN>.md.
```

## Transitions

After SAVE_DIAGNOSTIC completes → transition to `RESTORE_GREEN` (if needed) then to the appropriate escalation target:
- `RCS ≥ 24 && Codex available → CODEX_REVIEW`
- `RCS ≥ 32 || no Codex || design decision needed → HUMAN_GATE`

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"SAVE_DIAGNOSTIC"` |
| write | `current_sub_state` | `compose_artifact` |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) on exit (artifact is the durable record; the working state points to it) | — | — |
| read | `work_packet_id` | str |
| read | `last_validation_json`, `last_validation_exit_code` | ValidationResult |
| read | `current_hypothesis_json` | RepairHypothesis |
| read | `current_rcs`, `current_strategy_id`, `current_strategy_attempt_count` | (failure history rollup) |
