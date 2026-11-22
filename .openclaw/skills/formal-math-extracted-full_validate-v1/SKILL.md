---
name: formal-math-extracted-full_validate-v1
description: "Canonical FAOP extracted via L2/L5 from the formal-math skills library. Replaces inlined reconstructions at the call sites listed in `formal-math-extractor`'s catalog."
---

# Formal Math Engineering — Extracted `FULL_VALIDATE.v1`

> L2/L5 auto-extracted by `formal-math-extractor`. The procedure below is the single canonical form. All inlined reconstructions at the listed call sites have been replaced with `call(FULL_VALIDATE.v1)`.

## Procedure

```bash
make format-check
make lint
make test
make lean
make cert-test
make ci

```

## Inputs / Outputs

```yaml
inputs:
  - (declared by the call site; this FAOP is reusable)
outputs:
  - (declared by the call site)
```

## Effect Label

`deterministic` (default — override per call site if needed).

## c_max

```yaml
c_max:
  tokens: 0
  wallclock_seconds: 60
```

## Call Sites (rewritten)

The following skills previously inlined this procedure; they now reference `FULL_VALIDATE.v1`:

- `formal-math-validate`
