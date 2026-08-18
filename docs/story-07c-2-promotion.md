# Story 07c-2 — `coverage_tree_soundness_full` promotion (preparatory → formally established)

Status: **v2 spec, re-scoped per Codex P0 review on PR #34 (2026-08-18T00:22Z).** Conditional `LeafReachesOne` form replaces unconditional `coverage_tree_soundness_full`.

## Context

M4 Finite coverage requires closing the `coverage_tree_soundness` � Collatz trajectory gap. The current `coverage_tree_soundness` (CoverageTree.lean:281) proves tree descent succeeds:

```lean
theorem coverage_tree_soundness (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l
```

Its docstring explicitly defers `ReachesOne x`: *"this theorem intentionally does not conclude `ReachesOne x`; that would require a proof connecting tree descent to the Collatz trajectory."*

### Project state at master `cd1272b` (post PR #35 audit)

- **1 admission closed** by PR #31 (merged 2026-08-17T22:11:12Z): `Basic.lean::acceleratedStep_odd_of_odd` (relocated from Certificate.lean, proved). See `docs/theorem-status.md`.
- **4 Dynamics/Equivalence sorries still pending** (NOT closed by PR #31):
  - `Dynamics.lean::standardStep_positive` (line 80)
  - `Dynamics.lean::acceleratedStep_positive_of_odd` (line 96)
  - `Equivalence.lean::acceleratedStep_equiv_standardStep` (line 60)
  - `Equivalence.lean::acceleratedTrajectory_reaches_one_implies_standard` (line 92)
- **Certificate.lean parser-related sorries** (lines 198, 199, 202) — over-budget (allows 1, has 3); pre-existing, out of scope for 02c/03c.
- **Affine.lean sorries** (lines 115, 174, 185, 195) — Story 04b workstream, separate.
- **`coverage_tree_soundness_orbit` sorry** (line 344) — orbit-aware routing workstream, separate.

The 1 closed admission establishes one prerequisite: `Odd (acceleratedStep n)` when `Odd n`. The 4 pending Dynamics/Equivalence sorries are themselves prerequisites for the 07c-2 promotion (per the Codex P0 review).

## Claim (v2 — re-scoped per Codex P0 #1)

**Claim level target:** formally established.

### v1 error (P0): unconditional form was rejected

```lean
-- v1 (REJECTED by Codex P0): unsound overclaim
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descend t x = some l ∧
         ReachesOne x
```

Codex P0 review rejected v1 because under only `ValidTree ∧ IsComplete`, the conclusion yields `ReachesOne x` for every `x > 0` for any valid complete tree (e.g., a one-leaf tree) — that **IS** the Collatz theorem, not a tree-soundness bridge. A tree-soundness bridge cannot entail the global convergence claim without additional leaf-level semantics.

### v2 (this revision): conditional semantic-leaf form

Two new definitions + one companion theorem, all conditional on leaf-level semantics:

```lean
-- v2: conditional semantic-leaf predicate
def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

-- v2: companion theorem with explicit leaf-semantic hypothesis
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧ LeafReachesOne t l
```

The conditional `hLeaf` is the semantic hypothesis: every verified leaf must carry a certificate that "any `x` landing here reaches 1". The proof of `coverage_tree_soundness_full` is then:

1. Apply `coverage_tree_soundness` to get `descend t x = some l` with `verified t l`.
2. Extract `LeafReachesOne t l` from `hLeaf l hl hver`.
3. Conclude.

This is correct: the tree routes (`coverage_tree_soundness`) and the leaf carries the semantic certificate (`LeafReachesOne`). No false claim about the global Collatz theorem.

No new `sorry` / `admit` / `axiom`. The existing `coverage_tree_soundness` is left **untouched**. `coverage_tree_soundness_orbit` (line 344, `sorry`) is **OUT OF SCOPE** — orbit-aware routing workstream.

## The actual work: structured leaf-certificate semantics (Q3)

The conditional form makes the semantic gap explicit. The work shifts from "prove `ReachesOne x`" (impossible without the Collatz theorem) to **defining and proving the leaf semantics**.

### Required: a structured certificate type

`leafProperty : String` carries no semantic content — it's an opaque `String` that could be anything. To prove `LeafReachesOne t l`, the leaf needs a **structured certificate** that proves "x reaches 1 within this leaf's interval" for any `x` that lands at this leaf.

A candidate (to be designed in a separate spec story):

```lean
-- Sketch: structured certificate that proves "x → 1 within this interval"
inductive LeafCertificate where
  | interval (period lo hi : Nat) (h : ∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x)
  | -- ... other certificate shapes ...
```

The semantics: a leaf certificate carries a proof that any `x` in its declared residue interval reaches 1.

### Why this matters

The current `leafProperty : String` is an opaque token. To prove `LeafReachesOne`, we need either:

1. **Structured certificates** (preferred): replace `leafProperty` with a certificate type that carries the semantic content + the proof.
2. **Proof-carrying strings**: parse the string into a structured form and re-prove the semantics from the parsed form. Harder, error-prone.
3. **External oracle**: assume the leaf semantics from an external source (Python's `tree.py`, etc.). Requires formal integration.

### Open question for Codex review (Q3 design)

This is the actual new story: **define the structured leaf-certificate type, prove the parsing/proof-construction logic, integrate with `coverage_tree_soundness_full`**.

The 5 closed lemmas from PR #31 are still relevant prerequisites (especially `acceleratedStep_odd_of_odd`, `acceleratedStep_equiv_standardStep`, `acceleratedTrajectory_reaches_one_implies_standard`) — they'll be used in the certificate construction. But the bridge is at the certificate level, not at the unconditional tree level.

## Lemma inventory (1 closed, 4 pending — corrected per audit)

Per `docs/theorem-status.md` (corrected post-PR #35 audit) and `docs/lean-sorry-budget.json`:

| # | Location | Status | Statement (informal) |
|---|---|---|---|
| 1 | `Basic.lean::acceleratedStep_odd_of_odd` | ✅ Checked | `Odd (acceleratedStep n)` when `Odd n` |
| 2 | `Dynamics.lean::standardStep_positive` | ❌ Pending | `standardStep n > 0` for all `n` |
| 3 | `Dynamics.lean::acceleratedStep_positive_of_odd` | ❌ Pending | `acceleratedStep n > 0` when `Odd n` |
| 4 | `Dynamics.lean::acceleratedStep_equiv_standardStep` | ❌ Pending | `acceleratedStep n` ≡ `standardStep n` (under odd condition) |
| 5 | `Equivalence.lean::acceleratedTrajectory_reaches_one_implies_standard` | ❌ Pending | `accelerated_orbit` reaches 1 → `standardTrajectory` reaches 1 |

The 4 pending lemmas are prerequisites for the structured certificate construction in Q3. They can be closed as part of 02c/03c (separate workstream) OR as part of the Q3 story itself.

## Out of scope (explicit)

- `coverage_tree_soundness_orbit` sorry at CoverageTree.lean:344 — orbit-aware routing workstream (separate).
- Certificate.lean parser-related sorries (lines 198/199/202) — pre-existing over-budget condition, separate audit pass.
- Affine.lean sorries — Story 04b workstream.
- New `sorry` / `admit` / `axiom` — forbidden by 07c-2 promotion criteria.
- `coverage_tree_soundness` modification — preserved untouched.
- The unconditional Collatz theorem — out of scope; 07c-2 is the tree-soundness bridge only.

## Implementation outline

1. **Spec-doc-stage Codex review** (THIS DOC, v2) — validate the conditional form + Q3 design direction.
2. On Codex approval: define structured `LeafCertificate` type + parsing/proof logic.
3. Prove `LeafReachesOne` from the certificate.
4. Implement `coverage_tree_soundness_full` using `coverage_tree_soundness` + `hLeaf` hypothesis.
5. Push to PR.
6. CI validates the Lean build (sole Lean gate per project BDD discipline).
7. Codex review of the actual code.
8. Merge on CI green + Codex sign-off.

Per-file discipline: `CoverageTree.lean` + (new file for the certificate type) + `tests/` for executable specs.

## Risks

- **R1 (HIGH):** The structured certificate design is the central new work. Spec-stage Codex review is meant to validate the design before implementation.
- **R2 (MEDIUM):** The 4 pending Dynamics/Equivalence lemmas need closure as part of the certificate work. This is a substantial formal-verification effort.
- **R3 (LOW):** v4.33.0 Mathlib API drift could affect new code. Mitigation: CI is the validation gate; iterate on failure.

## Codex review handoff template (v2)

```
## Story 07c-2 — coverage_tree_soundness_full promotion (v2 re-scope)

**Claim:** Add companion theorem `coverage_tree_soundness_full` with
conditional semantic-leaf hypothesis:
  LeafReachesOne t l := ∀ x, descend t x = some l → ReachesOne x
  coverage_tree_soundness_full uses hLeaf : ∀ l ∈ t.leaves,
    verified t l → LeafReachesOne t l as explicit hypothesis.
Uses 1 closed lemma from PR #31 (acceleratedStep_odd_of_odd) plus
the 4 pending Dynamics/Equivalence lemmas (closed as part of
this workstream or prerequisite PR). No new sorry/admit/axiom.

**Files:** CoverageTree.lean (companion theorem only),
            new certificate module (TBD name) for LeafCertificate,
            docs/story-07c-2-promotion.md (this doc).
**Base:** master at cd1272b (post-PR #35 audit).

**Specific review questions (v2):**
1. Is the conditional `LeafReachesOne` form sound? (v1 unconditional
   was rejected as a category error — does v2 fix it?)
2. Is the structured leaf-certificate design (Q3) the right
   approach? Or is there a better alternative?
3. Should the 4 pending Dynamics/Equivalence lemmas be closed as
   part of 07c-2, or as a prerequisite PR?
4. Is the out-of-scope boundary for coverage_tree_soundness_orbit
   correct?

**Lean validation gate:** GitHub Lean CI on the PR. No local lake.
**Per-stop rule:** standard pause at 2nd failure on same logical edit.
```

## Implementation log

- `d95caff` — spec v1 draft (companion-theorem approach) — REJECTED by Codex P0 review
- (this commit) — spec v2 re-scope (conditional `LeafReachesOne` + Q3 design)
