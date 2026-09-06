# ADR 0007: Symbolic affine map representation

Status: accepted.

## Context

Story 04 introduces the symbolic affine executor: the accelerated Collatz
map `T(n) = (3n + 1) / 2^{ν₂(3n + 1)}` and its iterations need an
algebraic representation that supports composition and exact arithmetic.

The natural mathematical representation is:

- A **branch word** `[k₁, k₂, ..., kₘ]` where each `kᵢ` is the two-adic
  valuation at step `i`.
- A single **affine map** `(Aₘ, Bₘ, Kₘ)` over ℤ representing the
  composition: `n ↦ (Aₘ * n + Bₘ) / 2^Kₘ` where `Kₘ = k₁ + ... + kₘ`.

The implementation choice is between:

**Option 1: Rational coefficients.**
Use `Fraction` (Python) / `Rat` (Lean). The single `T`-step is
`(a = 3/2^k, b = 1/2^k)`. Composition is rational multiplication.

**Option 2: Integer coefficients with explicit denominator exponent.**
Use `int` (Python) / `�` (Lean) for `a, b`, and a separate `k : ℕ` for
the denominator exponent. The map is `n ↦ (a * n + b) / 2^k`.

## Decision

Use **Option 2: integer coefficients with explicit denominator exponent.**

Reasons:

1. **Divisibility is a precondition, not part of the data.** Two affine
   maps are "compatible" if the inner map's output divides evenly into
   the outer map's expected input. Tracking the denominator exponent
   separately keeps the divisibility check at apply-time, not at the
   map-construction level.
2. **Composition formula is exact-arithmetic.** With Option 2:
   `(a₁, b₁, k₁) ∘ (a₂, b₂, k₂) = (a₁ * a₂, a₁ * b₂ + b₁ * 2^k₂, k₁ + k₂)`.
   All operations are integer arithmetic; no rational normalization is
   needed. With Option 1, composition requires reducing fractions,
   which can grow the numerator/denominator without bound.
3. **Python `int` and Lean `ℤ` are already arbitrary-precision.** Both
   representations support this. The denominator is `2^k`, not a
   general integer, so the structure stays small.
4. **The charter's "arbitrary-precision integers only; never round
   rational coefficients" constraint (PLAN.md, Story 04 note) is
   satisfied.** No floating point; no silent truncation.

## Consequences

- **AffineMap is a triple `(a, b, k)`**, not a pair of rationals.
- **`apply` validates divisibility.** If `2^k ∤ (a*n + b)`, raise an
  error rather than silently truncate. Python uses `>>` after the
  divisibility check (faster than `//` for non-negative integers);
  Lean uses `Int.ediv` and the caller carries the divisibility proof
  obligation.
- **Composition associativity is provable by `ring`.** No new Mathlib
  infrastructure is needed.
- **`appliesTo` checks the per-step valuation match.** This is the
  bridge from symbolic (branch word) to concrete (Collatz trajectory).

## Note on generalization

If a future story needs the composed rational form `(a/2^k, b/2^k)` as
a single object (e.g., for symbolic manipulation outside of the Collatz
domain), this ADR should be revisited. For the Collatz trajectory, the
explicit denominator exponent is the right representation.
