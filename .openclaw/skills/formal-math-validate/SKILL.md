---
name: formal-math-validate
description: "Run the narrowest meaningful Lean/Python validation gate first, then progressively broader gates up to `make ci`."
---

# Formal Math Engineering — VALIDATE State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has transitioned to `VALIDATE`.

VALIDATE runs the narrowest meaningful gate first, then progressively broader gates.

> **Effect-label routing (mandatory):** every command below is `effect_label = "deterministic"` and MUST be routed through `formal-math-effect-dispatch`. The dispatcher returns a typed `dispatch_result` with `exit_code`, `failure_signature`, and a small summary — never the raw compiler/test transcript. The orchestrator reads only the typed record, not stdout.

## Recommended Validation Order

```text
1. target-specific Lean/Python test or file build
2. affected subsystem tests
3. make lean and/or make test
4. make cert-test when certificate logic is affected
5. make ci before story completion
```bash
# Canonical: FULL_VALIDATE.v1 — see formal-math-extracted-full_validate-v1
call(FULL_VALIDATE.v1)
```

Use `make ci` as the full project gate. Use narrower targets for work-packet-level validation.

Per-leaf `c_max` for VALIDATE (default — overridable per work packet):

```yaml
validate_c_max:
  format-check:   { tokens: 0, wallclock_seconds: 30 }
  lint:           { tokens: 0, wallclock_seconds: 60 }
  test:           { tokens: 0, wallclock_seconds: 600 }
  lean:           { tokens: 0, wallclock_seconds: 900 }
  cert-test:      { tokens: 0, wallclock_seconds: 600 }
  ci:             { tokens: 0, wallclock_seconds: 1500 }
```

The dispatcher refuses to launch a leaf whose declared `c_max` is below the tool's expected runtime. If `make lean` overruns its `c_max`, the dispatcher emits `failure_signature { tool:"make", category:"timeout", … }` and the controller transitions to `CLASSIFY_FAILURE → INVESTIGATE`.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"VALIDATE"` |
| write | `current_sub_state` | `format_check \| lint \| test \| lean \| cert_test \| ci` |
| write | `last_validation_json` | ValidationResult |
| write | `last_validation_exit_code` | int |
| write | `state_updated_at` | iso8601 |
| write | `proof_debt_current` | int (re-counted on each `make lean` run) |
| checkpoint (χ) on every result | — | — |
| read | `work_packet_id` | str |

## Branch Resolution

Resolve the current GitHub default branch at runtime. Do not hard-code `main`. At the time of the workflow spec generation, the default branch was `agent/bootstrap-research-monorepo`.

## Transition (Pass)

On `make ci` (or narrower appropriate gate) pass → transition to `CHECKPOINT`.

## Transition (Fail)

On any validation failure → transition to `CLASSIFY_FAILURE`. Do NOT retry the validation, do NOT skip directly to IMPLEMENT edits.

The mandatory rule from the spec:

> "A validation failure may **never** transition directly from `VALIDATE` back to arbitrary `IMPLEMENT` edits."

## Validation Output Is Evidence Only

Per invariant #1: compiler/test output is evidence only — never directly controls the next edit. Use the failure output to feed `CLASSIFY_FAILURE` state, not to auto-trigger an edit.
