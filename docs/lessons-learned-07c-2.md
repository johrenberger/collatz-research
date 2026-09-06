# Lessons Learned — Story 07c-2 Promotion (PRs #36 → #48 → #49)

**Status:** Arc complete (MERGED 2026-08-21).
**Scope:** 3 PRs, ~7 calendar days (2026-08-14 to 2026-08-21).
**Outcome:** `coverage_tree_soundness_full` formally established at `29c41e0`; M4 Finite coverage Path A chain (5/5 admissions) closed.

This document captures the architectural decisions, CI cycle, and reusable patterns from the 07c-2 promotion arc, so future contributors can avoid the same pitfalls and reuse the working patterns.

---

## 1. Arc overview

### PR #36 — spec (squash-merged at `57b6d37`, 2026-08-18T02:12Z)

Docs-only PR (1 file: `docs/story-07c-2-promotion.md`; 116+/92−). Re-scoped from an unconditional companion-theorem approach to a **conditional `LeafReachesOne`** path per Codex P0 review on PR #34 (2026-08-18T00:22Z). The v1 form would have amounted to the global Collatz theorem under only `ValidTree ∧ IsComplete` — a tree-soundness bridge cannot entail `ReachesOne x` for every `x > 0` under any valid complete tree.

### PR #48 — Codex P2 follow-ups from PR #47 (squash-merged at `9447a7a`, 2026-08-21T01:08:43Z)

Regression examples + status hygiene. Established the squash-merge + P2-follow-up PR cycle that became the model for the 07c-2 promotion as well.

### PR #49 — 07c-2 promotion (squash-merged at `29c41e0`, 2026-08-21T14:05:30Z)

Implements the conditional `LeafReachesOne` + `coverage_tree_soundness_full` companion theorem per spec PR #36 v2. 2 files: `Lean/CollatzResearch/CoverageTree.lean` (+37/−3), `docs/theorem-status.md` (+2 rows). CI green on second attempt (run `32441161350`); Codex approved at run 191 (~1.5h after final push).

---

## 2. Architectural decisions

### 2.1 Conditional `LeafReachesOne` as explicit semantic hypothesis

The unconditional form would claim `ReachesOne x` for every `x > 0` under any valid complete tree — that **IS** the Collatz theorem, not a bridge. The conditional form makes the semantic gap explicit:

```lean
-- v2 (this promotion)
def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l
```

`hLeaf` is the per-leaf semantic hypothesis: every verified leaf must carry a certificate that "any `x` landing here reaches 1." The tree routes (`coverage_tree_soundness`) and the leaf carries the semantic certificate (`LeafReachesOne`). No false claim about the global Collatz theorem.

### 2.2 `coverage_tree_soundness` left untouched

The existing theorem (CoverageTree.lean line 281) still concludes only `∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l`. PR #49 only **adds** a companion theorem. No claim that the original theorem's conclusion became stronger.

### 2.3 `coverage_tree_soundness_orbit` stays `sorry`

The orbit-aware variant at CoverageTree.lean line 378 remains `sorry`. Out of scope for the 07c-2 promotion; separate orbit-aware routing workstream.

### 2.4 No import cycle

`oddness` (the `acceleratedStep_odd_of_odd` theorem) lives in `Basic.lean` (low-level, Mathlib-only). `Certificate.lean` migration in scope closes the existing admission by relocation, not duplication. The 5 closed lemmas from PRs #37/#38/#46/#47 are all in `Dynamics.lean` + `Equivalence.lean`, no import cycle with `Certificate.lean`.

---

## 3. CI cycle (2 attempts)

### 3.1 Attempt 1 — `b177f12` (CI run `32440755672`) ❌

Error:

```
error: Lean/CollatzResearch/CoverageTree.lean:359:45:
Application type mismatch: The argument hdesc has type
  descend t x = some l of sort Prop but is expected to have type
  ℕ of sort Type in the application
  hLeaf l hl hver hdesc
```

The original proof was:

```lean
  obtain ⟨l, hl, hver, hdesc⟩ := coverage_tree_soundness t hv hic x hx
  exact ⟨l, hl, hver, hdesc, hLeaf l hl hver hdesc⟩
```

### 3.2 Root cause — `def f : Prop := body` is opaque-as-function

`LeafReachesOne` is a `def` returning `Prop` with body `∀ x, descend t x = some l → ReachesOne x`. When Lean reduces `LeafReachesOne t l` and applies `(hLeaf l hl hver) hdesc` as a forall application, it substitutes the binder `x := hdesc`. But `hdesc : Prop` (a proof of `descend t x = some l`), not `ℕ`. So Lean errors with the confusing "expected ℕ" message.

The error message is misleading — Lean IS reducing `LeafReachesOne t l`, but it's applying the result as a forall (substituting `x := hdesc`) instead of as an implication (applying the implication to `hdesc`).

### 3.3 Attempt 2 — `bdc89a8` (CI run `32441161350`) ✅

Fix: use `refine` + `intro` to explicitly introduce the forall binders:

```lean
  obtain ⟨l, hl, hver, hdesc⟩ := coverage_tree_soundness t hv hic x hx
  refine ⟨l, hl, hver, hdesc, ?_⟩
  intro x' hdesc'
  exact hLeaf l hl hver x' hdesc'
```

The `intro x' hdesc'` gives Lean the binder types it needs (`x' : ℕ`, `hdesc' : descend t x' = some l`) to apply `hLeaf l hl hver` correctly (unifies on the implication `descend t x' = some l → ReachesOne x'`, not on the forall binder `x`).

Duration: 2m 4s, all 7 steps ✅.

---

## 4. Codex review process

Codex reviewed PR #49 at run 191 (2026-08-21T13:48:47Z, ~1.5h after final push). Verdict: **approve**.

> *"Conditional theorem is correctly scoped and kernel-checked. Does not derive `ReachesOne x` from `ValidTree t ∧ IsComplete t`; only transports an explicit per-leaf certificate. Avoids the invalid global-convergence implication identified in the earlier review."*

Two non-blocking P2 follow-ups (for PR #50 candidate):

1. **Name/scope clarity**: rename `coverage_tree_soundness_full` → "conditional semantic-leaf soundness" in PR title + public docs (discoverability improvement).
2. **Compile-checked regression example**: add small `CoverageTreeOrbitTests.lean` executable spec invoking the theorem with a concrete structural tree + explicit `hLeaf` provider (preserves argument order, makes conditional certificate boundary executable in the public API).

Codex also noted: *"Treat `LeafReachesOne` construction/validation as the next substantive semantic workstream, not as completed by this companion theorem."* — i.e., Q3 (structured `LeafCertificate`) is the real next step, not these P2 items.

---

## 5. Reusable patterns

### 5.1 `def f : Prop := body` is opaque-as-function (THE pattern)

**Symptom**: confusing "Application type mismatch" where the expected type is `ℕ` but actual is `Prop` (or any non-numeric sort).

**Cause**: a `def` returning `Prop` whose body is `∀ x, P x → Q x` is NOT directly applicable as a function. Lean reduces `f args` to the body but applies it as a forall (substituting `x := argument`), not as an implication (applying the implication to `argument`).

**Fix**: explicitly introduce the forall binders via `refine` + `intro`:

```lean
refine ⟨l, hl, hver, hdesc, ?_⟩
intro x' hdesc'
exact hLeaf l hl hver x' hdesc'
```

**When to apply**: any time you have `def Foo (args) : Prop := ∀ x, body` and need to apply `Foo args` as a function in a proof.

**Captured in skill**: `toolchain-bump-discipline` (Phase 2 Lean-specific patterns section).

### 5.2 Squash-merge + P2-follow-up PR cycle

**Pattern**: Codex non-blocking P2 items become a separate PR after merge.

- PR #48 was Codex P2 follow-ups from PR #47.
- PR #50 candidate is Codex P2 follow-ups from PR #49.

**Why**: ship the approved claim fast; bundle P2 polish separately. Avoids blocking the main claim on minor discoverability/naming/test improvements.

### 5.3 Conditional semantic hypothesis

**Rule**: bridge lemmas connecting structural property → global claim need explicit per-instance semantic hypothesis. Always check: "if my hypothesis list were empty or trivially satisfied, would my conclusion entail a known open problem?" If yes, the bridge is invalid.

**Anti-pattern** (Codex P0 rejected at PR #34):

```lean
-- WRONG: under only ValidTree t ∧ IsComplete t, this would amount to
-- the global Collatz theorem.
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         ReachesOne x
```

**Correct pattern**:

```lean
-- RIGHT: explicit per-leaf certificate is the semantic hypothesis
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l
```

**Captured in skill**: `safe-code-editing` (Section 10.2 "Scope discipline" subsection).

---

## 6. Open Q3 follow-up

Per spec PR #36 v2 (`docs/story-07c-2-promotion.md` Q3), the next substantive workstream is **defining a structured `LeafCertificate` type** that carries the per-leaf semantic content + proof.

**Why**: the current `leafProperty : String` is an opaque token. To prove `LeafReachesOne t l` for some concrete `l`, the leaf needs a structured certificate that proves "x reaches 1 within this leaf's interval" for any `x` that lands at this leaf.

**Pattern candidate** (sketch):

```lean
inductive LeafCertificate where
  | interval (period lo hi : Nat) (h : ∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x)
  | -- ... other certificate shapes (e.g., descentWitness, orbitRoute, ...) ...
```

The semantics: a leaf certificate carries a proof that any `x` in its declared residue interval reaches 1.

The 5 closed lemmas from PRs #37/#38/#46/#47 are still relevant prerequisites for the certificate construction (especially `acceleratedStep_equiv_standardStep` and `acceleratedTrajectory_reaches_one_implies_standard`) — they'll be used in the certificate construction.

---

## 7. References

- **Spec PR #36**: `docs/story-07c-2-promotion.md` (squash-merged 2026-08-18T02:12Z at `57b6d37`)
- **PR #48 (P2 follow-ups from PR #47)**: squash-merged 2026-08-21T01:08:43Z at `9447a7a`
- **PR #49 (07c-2 promotion)**: squash-merged 2026-08-21T14:05:30Z at `29c41e0`
- **CoverageTree.lean**: line 129 (new `LeafReachesOne` def), line 352 (new `coverage_tree_soundness_full` theorem)
- **theorem-status.md**: `LeafReachesOne` row + `coverage_tree_soundness_full` row
- **Skills updated**:
  - `toolchain-bump-discipline` — added Phase 2 Lean-specific patterns (PR #32 + PR #49) + `def f : Prop := body` opaque-as-function pattern
  - `safe-code-editing` — added Section 10.2 "Scope discipline" subsection (avoid implicit open-problem claims)
- **Codex PR #49 P2 follow-ups** (for PR #50 candidate):
  1. Rename `coverage_tree_soundness_full` → "conditional semantic-leaf soundness"
  2. Add compile-checked regression example in `CoverageTreeOrbitTests.lean`

---

## 8. Git archeology (commit trail)

For forensic / reproducibility purposes:

| PR | SHA | Author | Notes |
|---|---|---|---|
| #36 | `57b6d37` (squash) | OpenClaw | Spec: conditional `LeafReachesOne` path |
| #48 | `9447a7a` (squash) | OpenClaw | P2 follow-ups from PR #47 (regression examples + status hygiene) |
| #49 attempt 1 | `b177f12` | OpenClaw | Initial promotion — Prop-vs-ℕ application mismatch on attempt 1 |
| #49 attempt 2 | `bdc89a8` | OpenClaw | Fix: `refine` + `intro` to unfold forall binders explicitly |
| #49 squash | `29c41e0` | gh pr merge --squash | Final merged state at `agent/bootstrap-research-monorepo` |

CI runs:
- `32440755672` — attempt 1 (failed at `Build CoverageTree target` step)
- `32441161350` — attempt 2 (all 7 steps ✅, 2m 4s)
- Codex review run 191 — APPROVED 2026-08-21T13:48:47Z