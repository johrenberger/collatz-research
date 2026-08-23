# Lessons Learned — Story Q4 Bounded-Orbit Certificates (PRs #55 → #56 → #57 → #58)

**Status:** Arc complete (MERGED 2026-08-23).
**Scope:** 4 PRs, ~2 calendar days (2026-08-22 to 2026-08-23).
**Outcome:** `coverage_tree_soundness_orbit_cert` companion theorem formally established at `21262fb`; Q4 bounded-orbit data-side arc fully closed (spec + foundation + data layer + companion theorem).

This document captures the architectural decisions, the recurring CI cycle lesson (3rd time this pattern hits in Q4), and reusable patterns from the Q4 arc, so future contributors can avoid the same pitfalls and reuse the working patterns.

---

## 1. Arc overview

### PR #55 — spec (squash-merged at `4f670ec`, 2026-08-22T16:05:40Z)

Docs-only PR (1 file: `docs/story-q4-bounded-orbit-certificates.md`; ~574 lines). The spec went through 4 commits before landing v3:

- **v1 `eaae6e8`** (REJECTED by Codex run 21843 P1×2+P2). Critical mistake: `routed_implies_claim : descendOrbit t x 0 = some l → claim.Holds x` was about the **original input `x`** — the same uninhabitable boundary Q3 v3 explicitly avoided. Under current `descend`/`descendOrbit` semantics, the preimage of a nonempty leaf is periodic, so it cannot be contained in `{x | x = n}` or `{x | x ≤ K}`. Also missing the `ReachesOne (accelerated_orbit x k) → ReachesOne x` composition lemma.
- **v2 `a24e914`** redesigned around `orbit_hits_claim` shape: certificate asserts `∃ k, claim.Holds (accelerated_orbit x k)` — claim is about an **orbit state**, not the original input. New `FiniteOrbitClaim` type (`.empty` / `.singleton n` / `.bounded K`; `.interval` excluded by construction) + `IsFiniteClaim : LeafClaim → Prop` helper + foundation lemmas `accelerated_orbit_compose` + `orbit_predecessor_reaches_one`.
- **v2.1 `62932fc`** proactively amended (aligned `wellFormed : claim.IsFinite` with Codex sketch, dropped YAGNI `toLeafClaim` lifting). **SELF-EVALUATION FAILURE**: missed run-21848 P1 routing-relation mismatch. Codex run-21858 re-rejected.
- **v3 `028904f`** (final): introduces new `OrbitLeafReachesOne t l := ∀ x, descendOrbit t x 0 = some l → ReachesOne x` predicate so the companion theorem conclusion matches the routing evidence. Drops the tautological `wellFormed` field + `IsFinite` predicate per run-21858 P2. Re-scopes companion theorem prose as "parallel orbit-routing theorem" (NOT a refinement of `coverage_tree_soundness_full` / `coverage_tree_soundness_cert` which certify the different `descend`-based relation). Adds API-shape regression `applyResidueReaches` + `applyOrbitReaches` with strictly different routing-hyp types. Splits implementation into 4 PRs per Codex run-21858 "right execution order".

### PR #56 — orbit foundation (squash-merged at `a7f834a`, 2026-08-22T20:05:46Z)

First implementation PR. 3 files / +130 lines. Implements the v3 spec's foundation: `@[simp] theorem accelerated_orbit_succ` companion to `accelerated_orbit_zero` (needed by `accelerated_orbit_compose` induction); `theorem accelerated_orbit_compose : accelerated_orbit x (k + k') = accelerated_orbit (accelerated_orbit x k) k'` (closes the placeholder `sorry` from PR #55 spec sketch; proof by induction on `k'`); `theorem orbit_predecessor_reaches_one : ReachesOne (accelerated_orbit x k) → ReachesOne x` (proof via `obtain ⟨k', hk'⟩ := h_reaches; exact ⟨k + k', by rw [accelerated_orbit_compose, h_eq, hk']⟩`); `def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop := ∀ x, descendOrbit t x 0 = some l → ReachesOne x` (parallel to `LeafReachesOne`); compile-checked def-equality scenario.

CI cycle: 3 attempts. **v1 `7a3fc1d`** RED on `Function expected at ReachesOne` (placed `orbit_predecessor_reaches_one` BEFORE `def ReachesOne`). **v2 `5bb48d7`** moved past `ReachesOne` but RED on `Unknown identifier descendOrbit` (placed `OrbitLeafReachesOne` BEFORE `def descendOrbit`). **v3 `cf3b045`** GREEN. **v4 `94e5ee9`** Codex P2 cleanups.

### PR #57 — data layer (squash-merged at `2e858af`, 2026-08-23T18:35:53Z)

First data-layer PR. 3 files / +429 lines. Implements `FiniteOrbitClaim` inductive (`.empty` / `.singleton n` / `.bounded K`; `.interval` excluded by construction); `namespace FiniteOrbitClaim` with `Holds : FiniteOrbitClaim → Nat → Prop` (per-constructor dispatch), `Holds.decidable` instance, `IsFiniteClaim : LeafClaim → Prop` (returns `True` for finite constructors, `False` for `.interval`), `IsFiniteClaim.decidable` instance; `BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type` structure with `claim : FiniteOrbitClaim` (data) + `orbit_hits_claim` (orbit-state-relative routing-to-claim obligation) + `claim_reaches_one` (reachability obligation). **NO `wellFormed` field** per Q4 v3 (finite-shape restriction enforced at the type level by `FiniteOrbitClaim`'s constructor set, not by a per-certificate guard). New `FiniteOrbitClaimTests.lean` with 13 compile-checked regression scenarios.

CI cycle: 3 attempts. **v1 `84eab24`** RED on 4 instance-synthesis errors at lines 541-544 (`Decidable (IsFiniteClaim LeafClaim.empty)`, etc.). Equations-form `inferInstance` doesn't propagate the `IsFiniteClaim` unfold before instance resolution — bare `inferInstance` (without explicit type annotation) sees the unreduced motive `Decidable (IsFiniteClaim .empty)` and tries to find an instance for that unreduced type, failing because no such instance exists (only `Decidable True` and `Decidable False` are core instances). **v2 `5078ae3`** GREEN — switched to `cases c with` + explicit `(inferInstance : Decidable True/False)` form (matching `LeafClaim.WellFormed.decidable`). **v3 `8b01552`** Codex P2 cleanups (polymorphic obligation projections scenarios 14+15; docstring trim; "data-only" → "proof-carrying data" trust boundary).

### PR #58 — companion theorem + BDD (squash-merged at `21262fb`, 2026-08-23T19:06:43Z)

First companion-theorem PR. 3 files / +180/-107 cumulative. Implements `theorem coverage_tree_soundness_orbit_cert (t : CoverageTree) (hv : ValidTree t) (hic : IsComplete t) (hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l) (x : Nat) (hx : x > 0) : ∃ l, l ∈ t.leaves ∧ verified t l ∧ descendOrbit t x 0 = some l ∧ OrbitLeafReachesOne t l` (parallel to `coverage_tree_soundness_cert`, NOT a refinement). 5-line 4-step composition: `descend_orbit_complete` provides orbit-aware routing + `OrbitRoute` witness → `cert.orbit_hits_claim` lifts routing to orbit-state claim (`∃ k, claim.Holds (accelerated_orbit x' k)`) → `cert.claim_reaches_one` derives `ReachesOne (accelerated_orbit x' k)` → `orbit_predecessor_reaches_one` closes via orbit-predecessor closure lemma. Concludes `OrbitLeafReachesOne t l` (NEW Q4 v3 predicate, defined over `descendOrbit`), NOT `LeafReachesOne t l` (defined over `descend`). New `CoverageTreeOrbitTests.lean` scenarios 11 + 12 (executable spec for the theorem + `applyResidueReaches` / `applyOrbitReaches` API-shape regression with strictly different routing-hyp types).

CI cycle: 3 attempts. **v1 `b283456`** RED on `Unknown identifier descend_orbit_complete` (885:41). Theorem USES `descend_orbit_complete` (line ~934) but was placed BETWEEN `coverage_tree_soundness_cert` (line ~820) and `coverage_tree_soundness_orbit` (line ~849). I checked the wrong boundary — looked at the `coverage_tree_soundness_cert` + `coverage_tree_soundness_orbit` pair but MISSED that `descend_orbit_complete` is BETWEEN them. **v2 `b1a2f6c`** GREEN — moved theorem + docstring past `descend_orbit_complete`. **v3 `6e1c6c5`** Codex P2 cleanups (trust-boundary wording + theorem-status drift; transient CI history moved from production Lean comments to PR discussion).

---

## 2. Architectural decisions

### 2.1 Parallel predicate (`OrbitLeafReachesOne` parallel to `LeafReachesOne`)

The Q4 v3 conclusion type matches the Q4 v3 routing evidence. `LeafReachesOne` is defined over the residue-only router `descend`; `OrbitLeafReachesOne` is defined over the orbit-aware router `descendOrbit`. They are **NOT interchangeable** — they certify different routing relations. The companion theorem `coverage_tree_soundness_orbit_cert` concludes `OrbitLeafReachesOne` (not `LeafReachesOne`), and the proof constructs orbit-routing evidence throughout. The v2 spec's mistake (concluding `LeafReachesOne t l` over `descendOrbit` routing) was kernel-rejected as a routing-relation mismatch (Codex run-21848 P1 on PR #55).

```lean
-- Q3 v4 typed-cert (residue-only routing)
def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

-- Q4 v3 typed-cert (orbit-aware routing, NEW)
def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descendOrbit t x 0 = some l → ReachesOne x

-- Q4 v3 companion theorem — parallel orbit-routing theorem
theorem coverage_tree_soundness_orbit_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         OrbitLeafReachesOne t l := by
  obtain ⟨l, hl, hver, hdesc, hroute⟩ := descend_orbit_complete t hv hic x hx
  obtain cert := hCert l hl hver
  refine ⟨l, hl, hver, hdesc, ?_⟩
  intro x' hdesc'
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x' hdesc'
  exact orbit_predecessor_reaches_one x' k (accelerated_orbit x' k) rfl
         (cert.claim_reaches_one _ hk)
```

The two companion theorems (`coverage_tree_soundness_cert` and `coverage_tree_soundness_orbit_cert`) certify DIFFERENT routing relations and are PARALLEL, not refinements. They share the same input structure (`ValidTree t`, `IsComplete t`, per-leaf certificate hypothesis, `x > 0`) but conclude different leaf-level predicates over different routers.

### 2.2 Orbit-state-relative claim shape (`orbit_hits_claim : ∃ k, claim.Holds (accelerated_orbit x k)`)

The certificate's `orbit_hits_claim` field asserts the routed input's **orbit** reaches a state satisfying the claim, NOT that the original input satisfies the claim. This is structurally different from Q3 v4's `LeafCertificate.routed_implies_claim` (which is about the original input `x` directly). The orbit-state-relative shape is what makes finite claims constructively inhabitable under `descendOrbit` — the original input `x` may not be in `.singleton n` or `.bounded K`, but its orbit at some step `k` may be. Combined with `orbit_predecessor_reaches_one : ReachesOne (accelerated_orbit x k) → ReachesOne x` (built on `accelerated_orbit_compose`), this is the actual Q4 mechanism: orbit-state reachability lifts back to original-input reachability via orbit-predecessor closure.

```lean
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)  -- orbit-state-relative
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y  -- membership predicate only
```

### 2.3 NO `wellFormed` field (Q4 v3 vs Q3 v4)

Per Q4 v3 (Codex run-21858 P2): the finite-shape restriction is enforced at the **type level** by `FiniteOrbitClaim`'s constructor set (which excludes `.interval`). The v2.1 spec had a `wellFormed : claim.IsFinite` field carried on `BoundedOrbitCertificate`; Codex rejected it as a tautological obligation for symmetry with `LeafCertificate.WellFormed`. Q4 v3 uses `IsFiniteClaim : LeafClaim → Prop` as a separate reusable predicate (in `namespace FiniteOrbitClaim`) for code that needs to discriminate between finite vs `.interval` `LeafClaim` values — but that predicate is NOT carried as a certificate field. The certificate itself is proof-carrying data: a data field plus kernel-checked proof fields.

### 2.4 NO mutual exclusion with `LeafCertificate`

A leaf can carry both `LeafCertificate t l` (Q3 v4, residue-only routing) and `BoundedOrbitCertificate t l` (Q4 v3, orbit-aware routing) as **independent views** of its semantic content. They conclude different leaf-level predicates (`LeafReachesOne t l` vs `OrbitLeafReachesOne t l`) and certify different routing relations (`descend` vs `descendOrbit`). A leaf's two certificates are independent — neither excludes nor implies the other. External code can use either or both.

### 2.5 Sort rationale (`: Type` for `BoundedOrbitCertificate`, `: Prop` for the companion theorem)

`BoundedOrbitCertificate t l` is `: Type`-valued (proof-carrying data bundle) because the `claim : FiniteOrbitClaim` data field requires `Type`-valued sort (Lean 4 elaboration rejects `Type`-valued fields in `: Prop` structures). The two obligation fields are still `Prop`s and kernel-checked; only the outer sort is `Type`. API-shape regression via `def boundedCertificateClaim {t l} (c : BoundedOrbitCertificate t l) : FiniteOrbitClaim := c.claim` (Prop → Type elimination; mirrors PR #54's `def certificateClaim`). Mirrors `LeafCertificate` (Q3 v4).

`coverage_tree_soundness_orbit_cert` is `: Prop`-valued (conclusion is `Prop`-valued existential; no data fields to force `: Type`). Mirrors `coverage_tree_soundness_cert` (Q3 v4 typed-cert variant) and `coverage_tree_soundness_full` (07c-2 promotion).

---

## 3. CI cycle — the recurring lesson (3rd time this pattern hits in Q4)

The Q4 implementation arc hit the same root cause three times across PRs #56 → #57 → #58, each surface a different facet of the same underlying failure: **didn't verify the elaboration graph before committing**. Position-sensitive edits require checking the file's full forward-reference graph (every consumer after every dep), not skim the new code added.

| PR | Surface | Root cause | Fix |
|---|---|---|---|
| **PR #56 v1** `7a3fc1d` | Forward-reference cascade | Placed `orbit_predecessor_reaches_one` (uses `ReachesOne` in type sig) BEFORE `def ReachesOne`. Errors: `Function expected at ReachesOne` (172:52 + 173:4), cascading `Unknown identifier descendOrbit` (212:7), cascading `Type mismatch` on def-equality scenario (766:81). | Moved past `def ReachesOne` (v2 `5bb48d7`). |
| **PR #56 v2** `5bb48d7` | Forward-reference cascade | Moved past `ReachesOne` but placed `OrbitLeafReachesOne` (uses `descendOrbit` in body) BEFORE `def descendOrbit`. Errors: `Unknown identifier descendOrbit` (224:7), `Type mismatch` (778:81). | Moved past `def descendOrbit` (v3 `cf3b045`). |
| **PR #57 v1** `84eab24` | Equations-form `inferInstance` elaboration order | Equations-form `\| .empty => inferInstance \| ...` doesn't propagate the `IsFiniteClaim` unfold before invoking `inferInstance`. Bare `inferInstance` sees the unreduced motive `Decidable (IsFiniteClaim .empty)` and tries to find an instance for that unreduced type, failing. Errors: 4 instance-synthesis errors at lines 541-544. | Switched to `cases c with` + explicit `(inferInstance : Decidable True/False)` form (v2 `5078ae3`). |
| **PR #58 v1** `b283456` | Forward-reference cascade (theorem-before-dep) | Theorem USES `descend_orbit_complete` (line ~934) placed BETWEEN `coverage_tree_soundness_cert` (line ~820) and `coverage_tree_soundness_orbit` (line ~849). I checked the wrong boundary — looked at the `coverage_tree_soundness_cert` + `coverage_tree_soundness_orbit` pair but MISSED that `descend_orbit_complete` is BETWEEN them. Error: `Unknown identifier descend_orbit_complete` (885:41) + `Tactic 'rcases' failed` (885:9). | Moved theorem + docstring past `descend_orbit_complete` (v2 `b1a2f6c`). |

**Lesson**: three surface-level differences, same underlying failure mode. Two docstring-anchored fixes for the SAME pattern in the SAME PR (PR #56 v1→v2→v3) is the kind of failure that signals the editor didn't check the file's def order at commit time.

The docstring for `IsFiniteClaim.decidable` (PR #57 v2) and `coverage_tree_soundness_orbit_cert` (PR #58 v2) both carry paragraph-length placement / elaboration notes explaining the v1→v2 evolution for the next editor. These are durable rules, not transient history — they belong in the production Lean docstrings per the lean-api-discipline skill.

---

## 4. Codex review process

Codex reviewed PR #55 at run 21843 (2026-08-22T14:59:50Z), then re-reviewed at run 21848 (2026-08-22T15:09:09Z), then again at run 21858 (2026-08-22T15:42:40Z). The v3 spec resolved all 3 reviews' P1 + P2 fixes. The 4-PR split (`#56` foundation → `#57` data → `#58` theorem → `#59` lessons) was Codex's run-21858 resolution of "the right execution order": foundation + compile-checked scenarios first, then data type/certificate, then companion theorem, then lessons doc.

Codex reviewed PR #56 at run 191 (2026-08-21T13:48:47Z, actually run 5000660618 — 2026-08-22T17:18:57Z): **Verdict: approve** + 2 P2 nits (polymorphic apply-the-theorem scenario for `accelerated_orbit_compose`; trim docstring placement paragraphs).

Codex reviewed PR #57 at run 5386901696 (2026-08-23T16:11:49Z): **Verdict: approve** + 3 P2 fixes (polymorphic obligation projections for `orbit_hits_claim` + `claim_reaches_one`; trim transient implementation history from source+test docstrings; preserve trust-boundary wording "data-only" → "proof-carrying data").

Codex reviewed PR #58 at run (2026-08-23T16:57:17Z): **Verdict: approve** + 2 P2 fixes (trust-boundary wording + theorem-status drift; transient CI history out of production Lean comments).

---

## 5. Self-evaluation method lesson (from PR #55 v2.1 self-evaluation failure)

The PR #55 v2.1 self-evaluation failure (`62932fc`) is a separate, distinct lesson from the CI cycle lesson (Section 3):

**Failure mode**: v2.1 was a proactive amendment aligning `wellFormed : claim.IsFinite` with Codex's earlier sketch and dropping YAGNI `toLeafClaim` lifting. I synthesized the latest Codex review (run 21843 P1×2+P2) against the v1 baseline and called the amendment good. I **missed the run-21848 P1 routing-relation mismatch** that had been posted between my v2 and v2.1 reviews.

**Lesson**: future self-evaluation MUST scan ALL pending Codex reviews on the PR, not just synthesize the latest one against an earlier baseline. If there's a pending Codex review on the PR between my last review-read and my new commit, I need to re-read it explicitly before declaring the next iteration ready. v2.1 missed run-21848 P1; v3 caught it (proactively re-read all pending reviews before declaring v3 ready).

**Captured in skill**: this is the same class of lesson as Section 3's "position-sensitive edits" — both are about verifying state before acting, not after. Section 3 is elaboration-graph verification (the file's def order); Section 5 is review-state verification (the PR's pending Codex reviews). Different surfaces, same underlying discipline: check ALL relevant state before declaring the next iteration ready.

---

## 6. Reusable patterns

### 6.1 Parallel-predicate design for routing-relation changes

When a theorem conclusion changes routing relation (residue-only vs orbit-aware, single-step vs multi-step, etc.), introduce a parallel predicate rather than overloading the existing predicate or generalizing via indexed types. The new predicate makes the routing-relation change explicit in the type signature and prevents accidental interchange.

```lean
-- v1 mistake (overloading): conclude LeafReachesOne t l over descendOrbit — kernel-rejected routing-relation mismatch
-- v3 fix (parallel predicate): introduce OrbitLeafReachesOne t l parallel to LeafReachesOne t l

def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descendOrbit t x 0 = some l → ReachesOne x
```

**When to apply**: any time you're tempted to conclude `Foo t l` where `Foo` was defined for a different router than the one used in the proof. Add a parallel predicate and conclude that.

### 6.2 Orbit-state-relative claim shape for finite-claim certificates

For certificates about finite `LeafClaim` shapes (`.empty`, `.singleton n`, `.bounded K`), assert the claim about an **orbit state**, not the original input. The claim `∃ k, claim.Holds (accelerated_orbit x k)` is what makes finite claims constructively inhabitable under `descendOrbit`.

**When to apply**: any time you have a `LeafClaim.Holds` predicate referenced in an obligation field, AND the leaf is routed by `descendOrbit` (or any orbit-reducer), use the orbit-state-relative shape with `accelerated_orbit x k`. Pair with an orbit-predecessor closure lemma (`ReachesOne (accelerated_orbit x k) → ReachesOne x`) to close the proof.

### 6.3 Position verification before commit (read file def order, not just new code)

Before committing any position-sensitive edit (new def/theorem/instance that references other defs/theorems/instances in the same file), read the file's full def order, not just the new code added. Specifically check:
1. Every consumer in the new code's body — what's its def position in the file?
2. Every type signature referenced in the new code — what's its def position?
3. Is every consumer/type-position BELOW the new code's insertion point? If not, → forward-reference cascade; move the new code past its latest consumer.

Two docstring-anchored forward-reference fixes for the SAME pattern in the SAME PR is the kind of failure that signals the editor didn't check def order at commit time. When you find yourself in this situation, **stop and re-read the file from the top**.

### 6.4 Equations-form `inferInstance` requires explicit type annotation OR `cases c with` form

Equations-form `| .empty => inferInstance | ...` doesn't unfold a `def` predicate before invoking `inferInstance`, so bare `inferInstance` (without explicit type annotation) sees the unreduced motive and tries to find an instance for that unreduced type — failing because no such instance exists (only `Decidable True` and `Decidable False` are core instances).

**Two fixes**:

```lean
-- Fix 1: explicit type annotation on each branch
instance IsFiniteClaim.decidable (c : LeafClaim) :
    Decidable (IsFiniteClaim c) :=
  | .empty => (inferInstance : Decidable True)
  | .singleton _ => (inferInstance : Decidable True)
  | .bounded _ => (inferInstance : Decidable True)
  | .interval _ _ _ => (inferInstance : Decidable False)

-- Fix 2: cases c with form (matches LeafClaim.WellFormed.decidable)
instance IsFiniteClaim.decidable (c : LeafClaim) :
    Decidable (IsFiniteClaim c) := by
  cases c with
  | empty => exact (inferInstance : Decidable True)
  | singleton _ => exact (inferInstance : Decidable True)
  | bounded _ => exact (inferInstance : Decidable True)
  | interval _ _ _ => exact (inferInstance : Decidable False)
```

**When to apply**: any equations-form `Decidable` instance where the motive involves a `def` that needs to be unfolded before instance resolution. Fix 2 is more reliable (matches the project's `LeafClaim.WellFormed.decidable` style).

### 6.5 API-shape regression via `def` projection (not `#check`)

For `: Type`-valued proof-carrying data bundles, add a `def` projection that performs a `Prop → Type` elimination:

```lean
-- Q3 v4 (PR #54)
def certificateClaim {t : CoverageTree} {l : CoverageLeaf}
    (c : LeafCertificate t l) : LeafClaim :=
  c.claim

-- Q4 v3 (PR #57)
def boundedCertificateClaim {t : CoverageTree} {l : CoverageLeaf}
    (c : BoundedOrbitCertificate t l) : FiniteOrbitClaim :=
  c.claim
```

A future PR flipping the sort to `: Prop` will fail to typecheck this def (no dependent elimination from `Prop` into `Type`). `#check` alone is documentation; `def` is a regression guard.

### 6.6 API-shape regression for routing-hyp differentiation

For theorems with strictly different routing-hypothesis types, add parallel `def` projections that take each routing-hyp type:

```lean
-- Q4 v3 (PR #58)
def applyResidueReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : LeafReachesOne t l) (x : Nat) (hdesc : descend t x = some l) :
    ReachesOne x :=
  h x hdesc

def applyOrbitReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : OrbitLeafReachesOne t l) (x : Nat) (hdesc : descendOrbit t x 0 = some l) :
    ReachesOne x :=
  h x hdesc
```

The two functions require strictly different routing-hypothesis types (`descend t x = some l` vs `descendOrbit t x 0 = some l`). Passing the wrong hypothesis at a call site surfaces a Lean type error. This is the executable-spec-layer guard against the v2 routing-relation mismatch (Codex run-21858 P2 review on PR #55).

### 6.7 Trim transient history from production Lean docstrings

After the PR cycle is closed (CI green + Codex approved), trim transient implementation history from the production Lean docstrings. Move the iteration history (v1→v2→v3 evolution, "lesson recorded" paragraphs, "cautionary tale" references) to the PR discussion (issue comment on the PR) or to a separate `NOTES.md` file. Keep only:
- Semantic contracts (what the def/theorem means, not how it was built)
- Placement requirements (which defs must be in scope, NOT the cautionary tale of past misplacement)
- Sort rationale (`: Type` vs `: Prop`, NOT the historical justification for the choice)
- Companion API-shape regression pointers (concise `def projection`, NOT the elaborate justification)

### 6.8 Hypothesis-bearing theorems with explicit `hCert` parameter

For companion theorems that depend on per-leaf certificates, take the certificate hypothesis as an **explicit** parameter (no default, no `by sorry`):

```lean
-- Q3 v4 (PR #54) + Q4 v3 (PR #58) pattern
theorem coverage_tree_soundness_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → LeafCertificate t l)
    (x : Nat) (hx : x > 0) : ... := ...

theorem coverage_tree_soundness_orbit_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)
    (x : Nat) (hx : x > 0) : ... := ...
```

The `hCert` parameter is **explicit** (no default) per the project's "no new sorry" discipline (PR #51 P1). The per-leaf certificate construction (the actual proofs of `orbit_hits_claim` + `claim_reaches_one` for Q4; `routed_implies_claim` + `claim_reaches_one` for Q3) is the next substantive workstream — not the companion theorem itself.

Executable spec scenarios mirror the parameter shape with `example (hv := by native_decide) (hc := by native_decide) (hCert : ∀ l ∈ ..., verified t l → BoundedOrbitCertificate t l) : ... := by exact ... ` — the `hCert` is still explicit in the `example` parameter list, preserving the "no new sorry" discipline.

---

## 7. Conclusion

The Q4 bounded-orbit arc delivered `coverage_tree_soundness_orbit_cert` as a parallel orbit-routing companion theorem to Q3 v4's `coverage_tree_soundness_cert`. The architectural innovation is the parallel-predicate design (`OrbitLeafReachesOne` alongside `LeafReachesOne`) paired with the orbit-state-relative claim shape (`orbit_hits_claim : ∃ k, claim.Holds (accelerated_orbit x k)`) — together these make finite `LeafClaim` claims (`.empty` / `.singleton n` / `.bounded K`) constructively inhabitable under orbit-aware routing.

The recurring CI cycle lesson (3rd time the same underlying failure mode hit in Q4 across PRs #56 → #57 → #58) is captured for future bounded-orbit work and any future position-sensitive Lean edits: verify the file's full forward-reference graph before committing, not just the new code added. Three surface-level differences (consumer-before-dep def, equations-form `inferInstance` elaboration order, theorem-before-dep) all share the same root cause — didn't verify the elaboration graph before committing.

The Q4 data-side arc (spec + foundation + data layer + companion theorem) is fully closed at `21262fb`. Remaining external-certificate work (constructive construction of `BoundedOrbitCertificate t l` from external sources, Python↔Lean translation layer) is a separate Q5+ workstream, deferred.

See `docs/story-q4-bounded-orbit-certificates.md` for the v3 spec (~574 lines); `docs/lessons-learned-07c-2.md` for the parallel Q3 lessons-learned doc.