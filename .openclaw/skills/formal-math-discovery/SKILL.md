---
name: formal-math-discovery
description: "Read-only repository reconnaissance before any modification; capture branch, HEAD, remotes, and Lean/Python environment."
---

# Formal Math Engineering — DISCOVERY State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has transitioned to `DISCOVERY`.

DISCOVERY is **read-only**. No source changes, no proof attempts, no formatter rewrites, no dependency updates, no speculative fixes.

## Required Commands

> All commands in this state are `deterministic` primitives. They MUST be routed through `formal-math-effect-dispatch` with `effect_label = "deterministic"`. They MUST NOT be performed inline in the model's reasoning context.

```bash
git status
git branch --show-current
git rev-parse HEAD
git remote -v
```

Also inspect as relevant:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
pyproject.toml
Makefile
docs/theorem-status.md
docs/trust-model.md
docs/architecture.md
story-specific Lean files
story-specific Python files/tests
```

## Required Output: `lean_context`

For every Lean target collect (the act of *collecting* this is `deterministic`; the *interpretation* of which fields matter is `op_LLM` if needed downstream):

```yaml
lean_context:
  theorem: ""
  namespace: ""
  imports: []
  referenced_definitions: []
  nearby_lemmas: []
  reducibility_dependencies: []
  lean_version: ""
  mathlib_revision: ""
```

The orchestrator persists `lean_context` to the runtime state via an EFFECT_DISPATCH `op_LLM` write — but never re-declares the verbatim stdout. The orchestrator sees a typed record, not raw `lake env` output.

## Forbidden During DISCOVERY

```text
- source changes
- proof attempts
- formatter rewrites
- dependency updates
- speculative fixes
```

## Transition

After DISCOVERY completes, transition to `PLAN`. Persist the `lean_context` to the persistent runtime state (`/data/.openclaw/state/openclaw.sqlite`) keyed by the story ID.

Do NOT proceed to `PLAN` until DISCOVERY output is recorded and `lean_context` is captured for every Lean target in the work packet.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"DISCOVERY"` |
| write | `current_sub_state` | `"read_env"` |
| write | `state_entered_at` / `state_updated_at` | iso8601 |
| write | `branch` | str |
| write | `base_commit` | str (set on first discovery) |
| write | `current_head_sha` | str |
| checkpoint (χ) on exit | — | — |
| **no reads** | — | — |
