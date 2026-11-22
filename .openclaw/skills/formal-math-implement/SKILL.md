---
name: formal-math-implement
description: "Apply a bounded work packet exactly as specified — no silent scope expansion — when the controller has transitioned to IMPLEMENT."
---

# Formal Math Engineering — IMPLEMENT State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has transitioned to `IMPLEMENT`.

IMPLEMENT operates on **exactly one bounded work packet**. No silent scope expansion.

> Edit primitives (`apply_patch`, edit on Lean or Python source) carry `effect_label = "op_LLM"` and `trust_boundary_change = true` whenever Lean/Python source is modified. They MUST be routed through `formal-math-effect-dispatch` with declared `tools_allow` (the file under edit) and a `c_max` budget. Refusal is allowed (and required) on budget overrun.

## Required Output: `current_packet`

```yaml
current_packet:
  id: "WP-1"
  objective: ""
  allowed_files:
    - "Lean/CollatzResearch/Certificate.lean"
  expected_validation:
    - "make lean"
    - "make cert-test"
  max_scope_expansion: none
```

## Mandatory Pre-Edit Checks (Read-Before-Write)

Before modifying any existing source file:

```text
1. Verify current branch        (EFFECT_DISPATCH deterministic: git status, git branch --show-current, git rev-parse HEAD)
2. Inspect git status           (EFFECT_DISPATCH deterministic: git status)
3. Read the exact target file from disk   (EFFECT_DISPATCH deterministic: read)
4. Capture the target symbol and surrounding definitions  (EFFECT_DISPATCH deterministic or op_LLM depending on depth)
5. Verify no unexpected concurrent modification (EFFECT_DISPATCH deterministic: git status check)
```

The result row for each `dispatch_result` is the only thing the orchestrator reads back. The orchestrator must NOT inline the read file content into its reasoning context unless the leaf was declared `op_LLM` — and even then, only the targeted symbol, not the entire file.

For source-integrity-sensitive failures (encoding, hidden characters, line drift), inspect exact bytes.

Do NOT patch source using stale line-number assumptions.

## Scope Expansion Rule

If a new dependency is discovered or the packet needs to touch files outside `allowed_files`, STOP and transition to `PLAN_UPDATE` or `DEPENDENCY` classification. Do NOT silently expand scope.

## Lean-Specific Repair Discipline

- No tactic rotation without causal hypothesis. `simp → aesop → omega → ring → norm_num → rw → exact?` is prohibited.
- After 2 failed attempts with the same proof strategy: STOP tactic substitution; RE-READ theorem and dependencies; REASSESS theorem shape / reducibility / required lemmas.
- After 3 materially different failed proof strategies against the same target: generate diagnostic artifact; invoke independent review.

## Hypothesis Required Before Every Edit After Failure

```yaml
repair_hypothesis:
  failure: ""
  proposed_root_cause: ""
  evidence: []
  proposed_change: []
  files_affected: []
  expected_result: ""
  falsification_condition: ""
  strategy_id: ""
```

If the next result falsifies the hypothesis, close it as false. Do NOT mutate another nearby line without forming a new hypothesis.

## Transition

After IMPLEMENT completes (or hits a failure), transition to `VALIDATE`. Do NOT skip validation.

If IMPLEMENT hit a failure: transition to `CLASSIFY_FAILURE` first, then through the budget chain, before any retry.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"IMPLEMENT"` |
| write | `current_sub_state` | `"apply_patch"` |
| write | `current_head_sha` | str (after a successful patch) |
| write | `current_strategy_id` | str (echo of hypothesis.strategy_id) |
| write | `current_strategy_attempt_count` | int (incremented per attempt) |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) after every successful `make ci` | — | — |
| read | `work_packet_id` | str |
| read | `current_hypothesis_json` | RepairHypothesis |
| read | `trust_boundary_current_json` | TrustBoundary (to detect `DESIGN` change) |
