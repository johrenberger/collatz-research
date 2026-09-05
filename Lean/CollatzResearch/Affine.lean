import Mathlib
import CollatzResearch.Basic

/-!
# Symbolic affine executor

The accelerated Collatz map `T(n) = (3n + 1) / 2^{ν₂(3n + 1)}` and its
iterations can be represented as affine maps over �. This module:

1. Defines `AffineMap` as a triple `(a, b, k)` representing
   `n ↦ (a * n + b) / 2^k`.
2. Defines composition: `(a₁, b₁, k₁) ∘ (a₂, b₂, k₂) =
   (a₁ * a₂, a₁ * b₂ + b₁ * 2^k₂, k₁ + k₂)`.
3. Proves composition is associative and has identity laws.
4. Defines `BranchWord := List ℕ+` (a sequence of positive valuations).
5. Defines the affine map induced by a branch word (left-fold compose
   over single-step maps).
6. Defines `appliesTo`: a word applies to `n` iff `n` is positive odd
   and each step's valuation matches `ν₂(3nᵢ + 1)`.
7. Defines `execute` and states the semantic theorem
   `execute_eq_toAffine_apply` (cons case pending — see "Proof status").

This module makes no convergence, cycle-exclusion, or global descent
claim. It is the symbolic-executor foundation for Story 05 (residue
partitions and certificate schema).

See ADR-0007 for the design decision on the integer (vs. rational)
representation with explicit denominator exponent.

**Proof status (2026-08-10, Story 04):**
- Definitions: complete.
- Structural algebra (`comp_assoc`, `comp_id_left`, `comp_id_right`):
  proved by `ring`.
- Semantic theorems (`comp_apply_eq`, `execute_eq_toAffine_apply`):
  stated; cons case of `execute_eq_toAffine_apply` admitted via `sorry`
  pending a Mathlib divisibility lemma (see ADR-0007 and the PR #8
  body). Marked **preparatory** in `docs/theorem-status.md`.
-/

namespace CollatzResearch

/-- An affine map `n ↦ (a * n + b) / 2^k` over `ℤ`.

The divisibility condition `2^k ∣ (a * n + b)` is a precondition on the
input `n`, not a property of the map itself. The `apply` function uses
`Int.ediv` (Euclidean division); the caller is responsible for the
divisibility precondition when applying to integer values. -/
structure AffineMap where
  a : ℤ
  b : ℤ
  k : ℕ

/-- The identity affine map `n ↦ n`. -/
def AffineMap.id : AffineMap := ⟨1, 0, 0⟩

/-- The single-step affine map for a given **positive** two-adic
valuation `k ≥ 1`: `n ↦ (3n + 1) / 2^k`. Valid on the positive odd
domain when `k = ν₂(3n + 1)`.

Uses `ℕ+` (the positive-naturals subtype) so the API rejects `k = 0`
at the type level. This aligns with Python's `AffineMap.step(k)`,
which raises `ValueError` for `k < 1`. -/
def AffineMap.step (k : ℕ+) : AffineMap :=
  ⟨3, 1, k⟩

/-- Apply the affine map. Uses `Int.ediv`; the divisibility precondition
is a caller obligation. -/
def AffineMap.apply (m : AffineMap) (n : ℤ) : ℤ :=
  (m.a * n + m.b) / (2 ^ m.k : ℤ)

/-- Compose two affine maps: `(m₁ ∘ m₂).apply n = m₁.apply (m₂.apply n)`. -/
def AffineMap.comp (m₁ m₂ : AffineMap) : AffineMap :=
  { a := m₁.a * m₂.a
    b := m₁.a * m₂.b + m₁.b * (2 ^ m₂.k : ℤ)
    k := m₁.k + m₂.k }

theorem AffineMap.comp_assoc (m₁ m₂ m₃ : AffineMap) :
    (m₁.comp m₂).comp m₃ = m₁.comp (m₂.comp m₃) := by
  cases m₁; cases m₂; cases m₃
  simp only [AffineMap.comp]
  ring

@[simp] theorem AffineMap.comp_id_left (m : AffineMap) :
    AffineMap.id.comp m = m := by
  cases m
  simp only [AffineMap.comp, AffineMap.id]
  ring

@[simp] theorem AffineMap.comp_id_right (m : AffineMap) :
    m.comp AffineMap.id = m := by
  cases m
  simp only [AffineMap.comp, AffineMap.id]
  ring

/-- Apply-level composition equality under explicit divisibility
hypotheses.

This is the semantic companion to the structural composition
formula in `AffineMap.comp`. It says that when the intermediate
division by `2^m₂.k` is exact, applying the composed map equals
composing the applications.

**Proof status (2026-09-05, v1' — Codex-reviewed, fixes per PR #71 review):**

Source-verified lemma names per `docs/lean-api-discipline.md` P12
(read the pinned v4.33.0 Lean 4 core source at `lean4/src/Init/Data/
Int/DivMod/{Bootstrap,Lemmas}.lean`):

- `Int.mul_ediv_cancel' {a b : Int} (H : a ∣ b) : a * (b / a) = b`
  (Bootstrap.lean:312) — divisibility-based cancellation lemma.
  Used in Step 1 with hypothesis `h₂ : 2^m₂.k ∣ (m₂.a * n + m₂.b)`.
- `Int.mul_ediv_mul_of_pos {a : Int} (b c : Int) (H : 0 < a) :
  (a * b) / (a * c) = b / c` (Lemmas.lean:576) — ediv cancellation-
  across-factors. Used in Step 4 with `a := 2^m₂.k` (positivity
  discharged by `by positivity`).
- `Int.pow_add` — Lean core lemma for `Int` power addition
  (`(a : Int) ^ (b + c) = (a ^ b : Int) * (a ^ c : Int)`). Used in
  Step 3 to factor `2^(m₁.k + m₂.k) = 2^m₁.k * 2^m₂.k`.
- `Int.mul_comm` — standard commutativity rewrite, used in Step 3 to
  reorder the factors for the cancellation lemma.

**Note on `h₁`:** the divisibility hypothesis
`h₁ : 2^m₁.k ∣ (m₁.a * ((m₂.a * n + m₂.b) / 2^m₂.k) + m₁.b)` is
preserved as a semantic precondition (mirrors `appliesTo`-style
exact-divisibility obligations on the RHS) but is **not used** by
this v1' proof — the ediv equality holds regardless of exactness
via `Int.mul_ediv_mul_of_pos`'s floor-quotient semantics. Kept for
potential downstream v2 (`execute_eq_toAffine_apply`) usage; remove
in a separately reviewed API change if it ends up unused there too.

**Proof structure:**
1. `have h₃` — distribute first via `ring` (so the
   `2^m₂.k * ((m₂.a * n + m₂.b) / 2^m₂.k)` redex is exposed), then
   rewrite via `Int.mul_ediv_cancel' h₂`. The divisibility hypothesis
   `h₂` is the witness for the inner division being exact.
2. Rewrite the LHS numerator via `ring` (distributivity bridge) +
   `h₃`.
3. Factor denominator via `Int.pow_add` + `Int.mul_comm` to get
   `(2^m₂.k * X) / (2^m₂.k * 2^m₁.k)` where `X` is the RHS numerator.
4. Cancel common factor via `Int.mul_ediv_mul_of_pos _ _
   (by positivity : 0 < (2 ^ m₂.k : ℤ))`.

The proof has **not yet been CI-verified** (awaiting v1' push +
GitHub Lean CI run). The two Codex reviews on PR #71 v1 caught two
P0 issues (Step 1 redex not exposed; Step 2 used nonexistent
`Int.ofNat_pow`); both are fixed in this v1'. After CI green, the
follow-up commit will update `docs/theorem-status.md`
(`comp_apply_eq` row: Pending → Checked) and
`docs/lean-sorry-budget.json` (`Affine.lean` allowance: 4 → 3). -/
theorem AffineMap.comp_apply_eq (m₁ m₂ : AffineMap) (n : ℤ)
    (h₂ : (2 ^ m₂.k : ℤ) ∣ (m₂.a * n + m₂.b))
    (h₁ : (2 ^ m₁.k : ℤ) ∣
            (m₁.a * ((m₂.a * n + m₂.b) / (2 ^ m₂.k : ℤ)) + m₁.b)) :
    (m₁.comp m₂).apply n = m₁.apply (m₂.apply n) := by
  -- Unfold `AffineMap.apply` and `AffineMap.comp` to expose the
  -- numerator/denominator structure.
  unfold AffineMap.apply AffineMap.comp
  -- Step 1: establish the LHS numerator identity.
  -- First distribute (via `ring`) so the
  -- `2^m₂.k * ((m₂.a * n + m₂.b) / 2^m₂.k)` redex is exposed, then
  -- rewrite via `Int.mul_ediv_cancel' h₂` (source-verified
  -- Bootstrap.lean:312). The divisibility hypothesis h₂ is the witness
  -- for the inner division being exact.
  have h₃ : (2 ^ m₂.k : ℤ) *
             (m₁.a * ((m₂.a * n + m₂.b) / (2 ^ m₂.k : ℤ)) + m₁.b) =
           m₁.a * (m₂.a * n + m₂.b) + m₁.b * (2 ^ m₂.k : ℤ) := by
    rw [show (2 ^ m₂.k : ℤ) *
              (m₁.a * ((m₂.a * n + m₂.b) / (2 ^ m₂.k : ℤ)) + m₁.b)
            = m₁.a * ((2 ^ m₂.k : ℤ) *
                  ((m₂.a * n + m₂.b) / (2 ^ m₂.k : ℤ)))
              + m₁.b * (2 ^ m₂.k : ℤ) by ring]
    rw [Int.mul_ediv_cancel' h₂]
  -- Step 2: rewrite the LHS numerator via distributivity bridge
  -- (`ring`) + `h₃`. The LHS numerator is
  -- `m₁.a * m₂.a * n + (m₁.a * m₂.b + m₁.b * (2 ^ m₂.k : ℤ))`,
  -- which equals `m₁.a * (m₂.a * n + m₂.b) + m₁.b * (2 ^ m₂.k : ℤ)`
  -- by ring (distributivity), which is the RHS of h₃.
  rw [show m₁.a * m₂.a * n + (m₁.a * m₂.b + m₁.b * (2 ^ m₂.k : ℤ))
          = m₁.a * (m₂.a * n + m₂.b) + m₁.b * (2 ^ m₂.k : ℤ) by ring]
  rw [← h₃]
  -- Step 3: factor denominator 2^(m₁.k + m₂.k) = 2^m₁.k * 2^m₂.k via
  -- `Int.pow_add` (Lean core lemma for `Int` powers); reorder via
  -- targeted `Int.mul_comm (2 ^ m₁.k : ℤ) (2 ^ m₂.k : ℤ)` so the
  -- rewrite does not match an unintended numerator multiplication.
  rw [Int.pow_add]
  rw [Int.mul_comm (2 ^ m₁.k : ℤ) (2 ^ m₂.k : ℤ)]
  -- Step 4: cancel common factor 2^m₂.k via `Int.mul_ediv_mul_of_pos`
  -- (source-verified Lemmas.lean:576). Positivity discharged by
  -- `by positivity` since m₂.k : ℕ implies 2^m₂.k ≥ 1.
  rw [Int.mul_ediv_mul_of_pos _ _ (by positivity : 0 < (2 ^ m₂.k : ℤ))]

/-- A branch word: a list of **positive** two-adic valuations. -/
abbrev BranchWord := List ℕ+

/-- The empty branch word. -/
def BranchWord.empty : BranchWord := []

/-- The affine map induced by a branch word: left-fold of
`AffineMap.step` composed with `AffineMap.id`.

The composed map applies the steps in the order they appear in the
list: the first valuation's step runs first, then the second, etc.
The recursion is built in reverse so the composition convention
`m₁.comp m₂` (= "apply m₂ first, then m₁") produces the correct
left-to-right order. -/
@[simp] def BranchWord.toAffine : BranchWord → AffineMap
  | [] => AffineMap.id
  | k :: rest => (BranchWord.toAffine rest).comp (AffineMap.step k)

/-- A branch word applies to input `n` (a positive odd integer) when
each step's valuation matches `ν₂(3n� + 1)`. -/
@[simp] def BranchWord.appliesTo : BranchWord → ℕ → Prop
  | [], n => n > 0 ∧ n % 2 = 1
  | k :: rest, n =>
    n > 0 ∧ n % 2 = 1 ∧
    twoAdicValuation (3 * n + 1) = k ∧
    BranchWord.appliesTo rest (Nat.div (3 * n + 1) (2 ^ (k : ℕ)))

/-- Execute the branch word on input `n`, returning the final integer.

This is the operational counterpart of `BranchWord.toAffine`. The
result equals `(BranchWord.toAffine word).apply n` when `appliesTo`
holds (see `BranchWord.execute_eq_toAffine_apply` below). -/
def BranchWord.execute : BranchWord → ℕ → ℕ
  | [], n => n
  | k :: rest, n =>
    BranchWord.execute rest (Nat.div (3 * n + 1) (2 ^ (k : ℕ)))

/-- Executing a branch word equals applying its induced affine map,
when the word applies to the input.

The empty case is trivial by `rfl`. The cons case requires:
1. The divisibility lemma `2^k ∣ (3*n + 1)` from
   `twoAdicValuation (3*n + 1) = k` (Mathlib).
2. `AffineMap.comp_apply_eq` (above).
3. An induction on `BranchWord`.

Cons case admitted via `sorry`; marked **preparatory** in
`docs/theorem-status.md`. -/
theorem BranchWord.execute_eq_toAffine_apply (word : BranchWord) (n : ℕ)
    (_h : BranchWord.appliesTo word n) :
    BranchWord.execute word n = (BranchWord.toAffine word).apply n := by
  induction word with
  | nil =>
    simp [BranchWord.execute, BranchWord.toAffine, AffineMap.id, AffineMap.apply]
  | cons k rest ih =>
    -- Cons case: by `comp_apply_eq` and the divisibility induced by
    -- `appliesTo`. Admitted pending Mathlib lemma check.
    sorry

/-- TDD test (Story 04b): concrete application of `comp_apply_eq` mirroring
the Python oracle `tests/test_affine.py::test_affine_compose_apply_compatible`.

`AffineMap.step 2` (T at k=2) composed with `AffineMap.step 1` (T at k=1),
applied to `n=3`. The intermediate value `T(3) = 5` is valid for `T at k=2`.

If this `example` type-checks, `comp_apply_eq` discharges on this concrete
input; if not, the proof is incomplete. -/
example : ((AffineMap.step 2).comp (AffineMap.step 1) |>.apply (3 : ℤ)) = ((AffineMap.step 2).apply ((AffineMap.step 1).apply (3 : ℤ))) := by
  sorry

/-- TDD test (Story 04b): concrete application of `execute_eq_toAffine_apply`
on the canonical 5 → 1 trajectory.

The branch word `[4]` represents the single step T at k=4
(ν₂(3*5+1) = ν₂(16) = 4), which sends 5 → 1. The empty case is
trivial; the cons case exercises the same proof machinery as the
general theorem. -/
example : BranchWord.execute [4] 5 = (BranchWord.toAffine [4]).apply 5 := by
  sorry

end CollatzResearch
