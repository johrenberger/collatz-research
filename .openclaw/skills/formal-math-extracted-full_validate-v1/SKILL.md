---
name: formal-math-extracted-full_validate-v1
description: "Canonical FAOP extracted via L2/L5 from the formal-math skills library. Replaces inlined reconstructions at the call sites listed in `formal-math-extractor`'s catalog."
---

# Formal Math Engineering — Extracted `FULL_VALIDATE.v1`

> L2/L5 auto-extracted by `formal-math-extractor`. The procedure below is the single canonical form. All inlined reconstructions at the listed call sites have been replaced with `call(FULL_VALIDATE.v1)`.

## Procedure

```bash
python3 scripts/full_validate.py
```

The helper runs `make ci` once, fails closed on any nonzero result or timeout,
and writes complete output to a log outside stdout. `make ci` includes the full
pytest suite; `cert-test` is covered by the two checker test files collected by
that suite and is not invoked a second time. During repair, use the narrow
checks in `formal-math-validate`; this helper is the final gate.

## Inputs / Outputs

```yaml
inputs:
  - repository root
  - optional log directory
outputs:
  - exit code
  - concise pass/fail summary
  - path to complete log
```

## Effect Label

`deterministic` (default — override per call site if needed).

## c_max

```yaml
c_max:
  tokens: 0
  wallclock_seconds: 1800
```

## Call Sites (rewritten)

The following skills previously inlined this procedure; they now reference `FULL_VALIDATE.v1`:

- `formal-math-validate`
