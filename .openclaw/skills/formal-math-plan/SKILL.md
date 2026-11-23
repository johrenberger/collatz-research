---
name: formal-math-plan
description: "Decompose a story into bounded work packets without modifying source; required output is a `plan:` YAML."
---

# Formal Math Engineering — PLAN State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has transitioned to `PLAN`.

PLAN decomposes the story into bounded work packets. No source changes yet.

> **Stage 1 routing:** reading the story source / repo layout is `deterministic` (read-only file inspection). Decomposing the story into `work_packets` is `op_LLM` and routes through `formal-math-effect-dispatch` with a `c_max` budget; the typed return is the `plan` YAML, not free-form prose. The orchestrator never re-derives the decomposition from chat context after a `dispatch_result`.

## Required Output: `plan`

```yaml
plan:
  mathematical_goal: ""
  computational_evidence_goal: ""
  formalization_goal: ""

  work_packets:
    - id: "WP-1"
      objective: ""
      type: proof | python | parser | ffi | infrastructure | test
      dependencies: []
      allowed_files: []
      validation: []
      risk: low | medium | high
      trust_boundary_change: false

  critical_path: []
  expected_checkpoints: []
  known_design_decisions: []
```

## Split Rule

If one proposed work packet includes materially different mechanisms (e.g., Lean proof + FFI + parser + cryptography), split it.

## Decomposition for Story 06b (canonical example)

```text
WP-06B-A Lean acceptance/parser-result bridge
WP-06B-B Digest/SHA-256 trust and implementation decision
WP-06B-C Trajectory equality/match proof
WP-06B-D Integrated check_certificate_sound theorem
WP-06B-E Story-specific tests and anti-circularity validation
```

## Transition

After PLAN completes, transition to `BASELINE`. Persist `plan` to the persistent runtime state.

Do NOT proceed to `BASELINE` until each work packet has explicit `objective`, `type`, `dependencies`, `allowed_files`, `validation`, `risk`, and `trust_boundary_change`.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"PLAN"` |
| write | `current_sub_state` | `"decompose"` |
| write | `work_packet_id` | str (the active packet) |
| write | `state_updated_at` | iso8601 |
| checkpoint (χ) on exit | — | — |
| read | `branch`, `current_head_sha` | str |
