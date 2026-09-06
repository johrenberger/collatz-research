# Lessons Learned — Meta Synthesis Across All Arcs (02c/03c + 07c-2 + Q3 + Q4 + Q5)

**Status:** Meta doc; companion to `docs/lessons-learned-07c-2.md` (PR #50, 07c-2 arc), `docs/lessons-learned-q4-bounded-orbit.md` (PR #59, Q4 arc), and `docs/lessons-learned-q5-external-certificates.md` (Q5 arc). All arc-specific lessons-learned docs in master at `437225f` (pre-Q5) + Q5 additions via this PR.

**Scope:** Cross-cutting synthesis across 5 arcs (17 PRs total: 02c/03c PRs #30–#48, 07c-2 PRs #36 + #49–#51, Q3 PRs #52–#54, Q4 PRs #55–#59, Q5 PRs #61–#69). Q5 PRs MERGED 2026-08-28 through 2026-09-04; PR #64 retitled post-merge to reflect v2b partial state (Lemmas 5–6 REMOVED per Codex P0).

**Outcome:** 12 cross-cutting patterns + actionable insights for Q6+ and future verifier / soundness / routing-partition workstreams. Use this doc when starting a new arc or when a pattern recurs across arcs.

This document captures patterns that emerged across multiple arcs, so future contributors can avoid the same pitfalls and reuse the working patterns at the meta-level. For arc-specific lessons (e.g., the Q4 parallel-predicate design or the 07c-2 conditional theorem pattern), see the per-arc docs (linked above).

---

## 1. Arc overview

### 1.1 02c/03c — M4 Finite coverage Path A (PRs #30–#48)

The dynamics/equivalence arc closed the 5/5 admission chain required for the M4 Finite coverage claim:
- `acceleratedStep_odd_of_odd` (PR #31, Certificate.lean::acceleration_step_odd relocation)
- `standardStep_positive` (PR #37, parity-case split with `decide` + `omega`; uses `Nat.div_pos` dividend-bound then divisor-positivity per Mathlib v4.33.0)
- `acceleratedStep_positive_of_odd` (PR #38, `ordCompl`-based; odd-domain signature retained for API compat even though proof establishes the stronger `∀ n, 0 < acceleratedStep n`)
- `acceleratedStep_equiv_standardStep` (PR #46, 4-`rw` composition of `standardTrajectory_succ_shift` + `standardStep_of_odd` + `standardTrajectory_pow_div`; divisibility witness via `Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity) |>.mpr (le_refl _)`; final `rw [acceleratedStep, twoAdicValuation]` closes by `rfl`)
- `acceleratedTrajectory_reaches_one_implies_standard` (PR #47, induction on `m`; base `m = 0` via `trajectory_zero` + `standardTrajectory_zero`; inductive rewrites `trajectory n (k+1) = 1` via new `trajectory_succ_shift` to `trajectory (acceleratedStep n) k = 1`, applies IH with `acceleratedStep_odd_of_odd n h_odd`, composes via new `standardTrajectory_compose` to produce witness `m' = (1 + ν₂(3n+1)) + r`)

Reusable artifacts from this arc:
- `accelerated_orbit_compose : accelerated_orbit x (k + k') = accelerated_orbit (accelerated_orbit x k) k'` (PR #56 built on this for the Q4 mechanism)
- `orbit_predecessor_reaches_one : ReachesOne (accelerated_orbit x k) → ReachesOne x` (PR #56 built on this for the Q4 companion theorem's close step)
- Mathlib v4.33.0 signature migrations: `String.split → Std.Iter String.Slice`, `norm_num → Mathlib.Tactic.NormNum`, `Nat.pow_pos` new signature (proof first, base inferred) — captured in `toolchain-bump-discipline` skill Phase 2 checklist.

### 1.2 07c-2 — Conditional `LeafReachesOne` + `coverage_tree_soundness_full` (PRs #36 + #49–#51)

The 07c-2 promotion arc established the conditional companion theorem:
- `LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop := ∀ x, descend t x = some l → ReachesOne x` (PR #49)
- `coverage_tree_soundness_full` (PR #49, conditional companion theorem; takes explicit per-leaf `hLeaf` hypothesis)
- `def f : Prop := body` is opaque-as-function lesson (PR #49 CI cycle: v1 `b177f12` RED on "Application type mismatch"; v2 `bdc89a8` GREEN with `refine` + `intro`)
- Lessons-learned doc (PR #50) — establishes the per-arc doc structure
- Public-facing name "conditional semantic-leaf soundness" + explicit-parameter regression scenario 8 (PR #51, removed `hLeaf := by sorry` default per Codex P1)

Reusable patterns from this arc:
- **Conditional companion theorem pattern** (every companion theorem in 07c-2 / Q3 / Q4 takes an explicit per-leaf certificate hypothesis — no false claim about global Collatz convergence)
- **Public-facing name discovery** (PR #51 public-facing rename + theorem-status public-facing name updates)

### 1.3 Q3 — Structured `LeafCertificate` (PRs #52–#54)

The Q3 arc introduced the proof-carrying data architecture:
- `LeafClaim` inductive type (PR #53, `.empty` / `.singleton n` / `.bounded K` / `.interval period lo hi`)
- `LeafClaim.Holds : LeafClaim → Nat → Prop` predicate (PR #53, per-constructor dispatch)
- `LeafClaim.WellFormed : LeafClaim → Prop` (PR #53, `.interval` requires `period > 0 ∧ lo ≤ hi ∧ hi < period`)
- `parse_leaf_claim` (PR #53, structural decoder gated on `WellFormed l`)
- `LeafCertificate (t : CoverageTree) (l : CoverageLeaf) : Type` (PR #54, `: Type`-valued data bundle with `claim : LeafClaim` + `well_formed : claim.WellFormed` + `routed_implies_claim` + `claim_reaches_one`)
- `coverage_tree_soundness_cert` (PR #54, companion theorem with explicit `hCert` hypothesis)
- API-shape regression via `def certificateClaim {t l} (c : LeafCertificate t l) : LeafClaim := c.claim` (PR #54, Prop → Type elimination guard)

Reusable patterns from this arc:
- **Proof-carrying data + companion theorem pattern** (Q4 v3 mirrored this with `BoundedOrbitCertificate` + `coverage_tree_soundness_orbit_cert`)
- **`: Type` sort rationale** (data field forces `Type`; obligation fields remain `Prop` and kernel-checked)
- **Explicit-type decidability instance** (PR #53 v2 fix: `cases c with` + explicit `(inferInstance : Decidable True/False)` form — pattern reused in PR #57 v2)
- **Sort rationale flip from `: Prop` to `: Type`** (PR #54 v1→v2: Lean 4 elaboration rejected `Type`-valued field in `: Prop` structure; flipped to `: Type`)

### 1.4 Q4 — Bounded-orbit certificates (PRs #55–#59)

The Q4 arc delivered the parallel orbit-routing companion theorem:
- `OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop := ∀ x, descendOrbit t x 0 = some l → ReachesOne x` (PR #56)
- `FiniteOrbitClaim` inductive type (PR #57, `.empty` / `.singleton n` / `.bounded K`; `.interval` excluded by construction)
- `IsFiniteClaim : LeafClaim → Prop` (PR #57, returns `True` for finite constructors, `False` for `.interval`)
- `BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type` (PR #57, NO `wellFormed` field per Q4 v3)
- `coverage_tree_soundness_orbit_cert` (PR #58, companion theorem with explicit `hCert` hypothesis; concludes `OrbitLeafReachesOne` not `LeafReachesOne`)
- `applyResidueReaches` + `applyOrbitReaches` (PR #58, API-shape regression for routing-hyp differentiation)
- Lessons-learned doc (PR #59)

Reusable patterns from this arc:
- **Parallel predicate design** (`OrbitLeafReachesOne` alongside `LeafReachesOne` — when the routing relation changes, introduce a parallel predicate)
- **Orbit-state-relative claim shape** (`orbit_hits_claim : ∃ k, claim.Holds (accelerated_orbit x k)` — finite claims as certificate contracts, not original-input structural matches)
- **Position verification before commit** (3x forward-reference cascade lesson in this arc alone)
- **The 4-PR split** (Q4 v3 run-21858 resolution: spec → foundation → data → theorem → lessons)
- **Be precise about established vs deferred** (Q4 v2 overclaimed "constructively inhabitable"; precise wording: "expressible as an orbit-state-relative certificate contract")

### 1.5 Q5 — External-certificates + bounded-input + routing-partition (PRs #61–#69)

The Q5 arc delivered the external-certificate infrastructure + bounded-input integration + routing-partition sub-arc:
- **PR #61** (spec): Q5 v5 spec — external-certificate inhabitation via Python search + Lean verifier. Defines trust boundary (Python UNTRUSTED, Lean TCB), the 4-PR split, the bounded-input vs unbounded-input scope distinction.
- **PR #62** (verifier): `BoundedInputCertificateWire` + `BoundedInputCertificateData` + `decodeBoundedInputCertificateData` + `checkBoundedCertificate` (Bool verifier) + `checkCertWitness` (5-conjunct single-witness checker). 5 versions before final merge (v1→v2→v3→v4→v5).
- **PR #63** (producer + parser): Python external generator + hand-rolled Lean JSON parser + parser-rejection tests. Closes the producer side of the trust boundary.
- **PR #64** (bounded-input integration): 16 commits — v1 → v2a → v2b.0 plan → v2b.1 (Lemmas 1–2 + 5 helper predicates) → v2b.2 (Lemma 3 + 2 bridging lemmas) → v2b.3 (Lemma 4) → v2b.4 (Lemma 5, REMOVED per Codex P0) → v2b.5 (Lemma 6, REMOVED per Codex P0) → v2b.6 (tests, trimmed) → sorry-budget tracker (REVERTED) → Codex P0/P1 fixes → WP-2/3/4 polish → repair integration tests. Retitled post-merge to `v2b partial — bounded-input infrastructure + soundness-chain helpers (Lemmas 1–4); soundness theorem (Lemmas 5–6) REMOVED per Codex P0; re-attempt requires architectural decision`.
- **PR #66** (hotfix): restore concrete `CertWitness` representation after a prior commit abstracted it away.
- **PRs #67–#69** (routing-partition sub-arc): certificate design → acceptance facts → RP-5 conditional routing-partition reachability. Parallel architecture established to address the per-leaf vs single-leaf quantification mismatch identified as a blocker for Lemma 5 re-attempt.

Reusable patterns from this arc:
- **Wire/checked split** (PR #62 v4) — `BoundedInputCertificateWire` is the wire payload; `BoundedInputCertificateData` is the checked bundle (wire + `length_ok` proof); `decodeBoundedInputCertificateData` is the trust boundary. Mirrors the proof-carrying-data pattern at the verifier boundary.
- **List-position identity** (PR #62 v3) — witness at index `i` carries canonical input `i + 1`. Reconstructed via `List.get` with the `length_ok` proof. Avoids storing canonical input as a Lean function field.
- **The 5-PR split** (extension of Q4 v3's 4-PR) — when integration tests need a concrete representation that an earlier commit abstracted away, insert a hotfix PR between the data and integration PRs. Hotfix is 1-PR scope, additive, no scope expansion.
- **Per-PR squash-merge with descriptive commit messages** (PR #64's 16-commit squash) — clean history even when many commits ship in one PR. Each commit message names the sub-arc + intent.
- **The actor pattern** (`app-dev-discovery-bot` shipped 12 commits in 48h with one Codex P0 rejection) — observation documented in `lessons-learned-q5-external-certificates.md` §3; **not promoted to a META pattern** (single-arc observation; see header note).
- **Reviewer-pivot not reviewer-launder** (Codex P0 on v2b.4) — the correct response to an independent rejection is structural restructure, not budget extension or hypothesis softening.

---

## 2. The 12 cross-cutting patterns

These patterns emerged across multiple arcs. Each pattern references the arcs + PRs where it was established and gives an actionable insight for future work.

### 2.1 The "no new sorry" discipline (every arc)

Pre-existing sorries tracked as project state (6 at master: 2 in `Affine.lean` from Story 04, 1 in `CoverageTree.lean::coverage_tree_soundness_orbit` PR #36 spec, 3 in `Certificate.lean` lines 198/199/202). Every PR maintains the Lean admission budget via the `Enforce Lean admission budget` CI step.

**Pattern**: companion theorems use **explicit per-leaf certificate hypotheses (no default, no `by sorry`)** to preserve this. Pattern established in 07c-2 (`hLeaf` per-leaf certificate hypothesis in `coverage_tree_soundness_full`; PR #51 v1→v2 removed `hLeaf := by sorry` default per Codex P1), reused in Q3 (`hCert : ∀ l ∈ t.leaves, verified t l → LeafCertificate t l` in `coverage_tree_soundness_cert`), reused in Q4 (`hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l` in `coverage_tree_soundness_orbit_cert`).

**Actionable insight**: any companion theorem that depends on per-leaf data should take the data hypothesis as an **explicit** parameter, never with a `by sorry` default. The Lean admission budget step will catch any new admission, but explicit parameters preserve the discipline even before the CI runs.

### 2.2 Proof-carrying data + companion theorem pattern (Q3 v4 + Q4 v3)

`: Type`-valued data bundle with `claim : LeafClaim` (or `FiniteOrbitClaim`) data field + `: Prop`-valued companion theorem that takes the bundle as explicit `hCert` hypothesis.

**Sort rationale**:
- Data bundle is `: Type` because of the data field (Lean 4 elaboration rejects `Type`-valued fields in `: Prop` structures)
- Companion theorem is `: Prop` (conclusion is `Prop`-valued existential; no data fields to force `: Type`)
- Obligation fields are `Prop`s and kernel-checked; only the outer sort is `Type`

**Companion theorem's standard 3-5 step composition**:
1. Obtain structural routing + witness (`coverage_tree_soundness` for Q3 residue-only; `descend_orbit_complete` for Q4 orbit-aware)
2. Obtain certificate from hypothesis (`hCert l hl hver`)
3. Compose via obligation fields (`routed_implies_claim` for Q3; `orbit_hits_claim` for Q4)
4. Close via foundation lemma (`claim_reaches_one` lifts to `ReachesOne`)

**Actionable insight**: any new companion theorem should follow this 4-step composition pattern. Use parallel predicates (Pattern 2.3) when the routing relation changes.

### 2.3 Parallel predicate design (Q4 v3 lesson)

When the routing relation changes (residue-only vs orbit-aware, single-step vs multi-step, etc.), introduce a parallel predicate rather than overloading the existing predicate or generalizing via indexed types. The new predicate makes the routing-relation change explicit in the type signature and prevents accidental interchange.

**Example**:
```lean
-- v1 mistake (overloading): conclude LeafReachesOne t l over descendOrbit — kernel-rejected routing-relation mismatch
-- v3 fix (parallel predicate): introduce OrbitLeafReachesOne t l parallel to LeafReachesOne t l

def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descendOrbit t x 0 = some l → ReachesOne x
```

**When to apply**: any time you're tempted to conclude `Foo t l` where `Foo` was defined for a different router than the one used in the proof. Add a parallel predicate and conclude that.

### 2.4 Position verification before commit (Q4 3x lesson + 02c/03c PR #46 3x)

Three surface-level differences, same underlying failure mode: didn't verify the file's full forward-reference graph (every consumer after every dep) before committing. Two docstring-anchored fixes for the SAME pattern in the SAME PR is the kind of failure that signals the editor didn't check def order at commit time.

**Surface manifestations**:
- **PR #56 v1 → v2 → v3** (Q4 foundation): consumer-before-dep def (`ReachesOne`, then `descendOrbit`)
- **PR #57 v1 → v2** (Q4 data layer): equations-form `inferInstance` elaboration order (different surface, same failure mode)
- **PR #58 v1 → v2** (Q4 companion theorem): theorem-before-dep cascade (`descend_orbit_complete`)
- **PR #46 v1 → v2 → v3** (02c/03c): helper-lemma position (similar pattern in dynamics/equivalence proofs)

**Actionable insight**: before committing any position-sensitive edit (new def/theorem/instance that references other defs/theorems/instances in the same file), read the file's full def order, not just the new code added:
1. Every consumer in the new code's body — what's its def position in the file?
2. Every type signature referenced in the new code — what's its def position?
3. Is every consumer/type-position BELOW the new code's insertion point? If not → forward-reference cascade; move the new code past its latest consumer.

**When you find yourself in this situation, stop and re-read the file from the top.**

### 2.5 Self-evaluation must scan ALL pending Codex reviews (PR #55 v2.1 lesson)

Different surface from Pattern 2.4, same underlying discipline: check ALL relevant state before declaring iteration ready. v2.1 missed run-21848 P1 because I synthesized the latest Codex review against the v1 baseline instead of scanning all pending reviews between v1 and v2.1.

**Actionable insight**: future self-evaluation MUST scan ALL pending Codex reviews on the PR, not just synthesize the latest one against an earlier baseline. If there's a pending Codex review on the PR between my last review-read and my new commit, I need to re-read it explicitly before declaring the next iteration ready.

### 2.6 Multi-iteration convergence is a signal (Q4 3x + 02c/03c PR #46 3x)

Three v1→v2→v3 commits hitting the same root cause = stop and check the elaboration graph before further iteration. Don't "try one more thing" — re-read the file.

**Actionable insight**: when you find yourself at v3+ in a single PR cycle hitting the same root cause, the meta-pattern is wrong. The right response is to STOP and re-read the file from the top, not to iterate further.

### 2.7 The 4-PR split works (Q4 v3 run-21858 resolution)

"Spec → Foundation → Data → Theorem → Lessons" isolates fixes per PR, reduces risk per commit, and lets Codex review each stage independently. The Q4 arc ran 5 PRs cleanly with this order. The lessons PR is conditional on whether notable patterns emerge (Q4 had 3 — position verification, parallel predicate, equation-form `inferInstance` — so the lessons PR was justified).

**Actionable insight**: for any new bounded-orbit workstream or future companion-theorem arc:
1. PR #N: spec doc (architectural decisions, execution order, dependencies)
2. PR #N+1: foundation lemmas + compile-checked scenarios (the smallest building blocks)
3. PR #N+2: data types + companion theorems (the structural middle layer)
4. PR #N+3: companion-theorem + BDD scenarios (the integration layer)
5. PR #N+4 (conditional): lessons-learned doc (if notable patterns emerged)

### 2.8 Trim transient history from production Lean docstrings (PR #56/57/58 v3)

After the PR cycle is closed (CI green + Codex approved), trim verbose v1→v2→v3 evolution paragraphs and "lesson recorded" notes. Move iteration history to PR discussion. Keep only durable rules (placement requirements, sort rationale, API-shape regression pointers). This pattern was enforced by Codex P2 #2 on 3 consecutive Q4 PRs.

**Actionable insight**: post-merge cleanup should include:
- Trim verbose v1→v2→v3 evolution paragraphs
- Move "lesson recorded" notes to PR discussion
- Keep only: placement requirements, sort rationale, API-shape regression pointers, durable design choices

The trim policy is captured as Pattern 2.8's sibling in `lessons-learned-q4-bounded-orbit.md` § 6.7 ("Trim transient history from production Lean docstrings").

### 2.9 Be precise about established vs deferred (Q4 lessons-learned P1 fix)

Docs overclaimed "constructively inhabitable" when Q4 only established the certificate contract. Precise wording:
- **NOT**: "the orbit-state-relative shape makes finite claims constructively inhabitable under `descendOrbit`"
- **YES**: "the orbit-state-relative shape **expresses** finite claims **as an orbit-state-relative certificate contract** (∃ k, claim.Holds (accelerated_orbit x k) + claim_reaches_one), not ruled out by the original-input structural mismatch. **Constructive inhabitation remains a future Lean-proof / certificate-checker workstream** — no certificate inhabitant, checker, or Python-to-Lean bridge was constructed in Q4."

**Actionable insight**: when writing summary docs, distinguish "established" (kernel-checked theorem proved in this arc) from "deferred" (workstream acknowledged but not yet implemented). The "no global Collatz convergence" boundary applies to docs too — overclaim propagates into reviewer expectations.

### 2.10 Conditional companion theorem pattern (07c-2 + Q3 + Q4)

All companion theorems take an explicit per-leaf certificate hypothesis (`hCert : ∀ l ∈ t.leaves, verified t l → Certificate t l`). The conditional form makes the semantic gap explicit — no false claim about global convergence. The proof is a 3-5 step composition (per Pattern 2.2).

**Actionable insight**: any companion theorem should take an explicit per-leaf certificate hypothesis. The conditional form is the only correct form — the unconditional form would amount to the global Collatz theorem under only `ValidTree t ∧ IsComplete t`, which a tree-soundness bridge cannot entail.

### 2.11 Hypothesis-bearing proof obligations (every arc)

Per-leaf certificate construction (the actual proofs of `routed_implies_claim` + `claim_reaches_one`, or `orbit_hits_claim` + `claim_reaches_one`) is **external** — supplied by the caller at certificate construction time (Python oracle, finite-trajectory checker, manual construction). The companion theorem doesn't prove any new global Collatz result; it only transports the per-leaf certificate.

**Trust boundary**:
- Lean proves the structural routing + companion theorem logic
- External computation (Python, Lean-impl checker) provides the trajectory evidence
- Python tests in `tests/test_coverage_tree.py` are **UNTRUSTED RUNTIME EVIDENCE**, not formal Lean substitution (per MEMORY.md note)
- Restoring the direct Lean D1 regression is a separate workstream (per 07c-3 deferred discriminator)

**Actionable insight**: when designing companion theorems, the proof obligations MUST be hypothesis-bearing. The tree-soundness bridge cannot prove the per-leaf Collatz result; it only transports a certificate hypothesis to a conclusion.

### 2.12 Lean CI is the sole validation gate (every arc)

No local `lake` commands run — Lean validation runs only in GitHub CI. The "no new sorry" discipline is enforced by the `Enforce Lean admission budget` step. Trust boundary: Lean proves the structural routing; external computation provides the trajectory evidence.

**Actionable insight**: do not run `lake build` locally to validate PR cycles. Let the GitHub Lean CI run and verify. Local lake commands bypass the admission budget step (which is a GitHub-only check).

**Note on the actor pattern (Q5)**: META's section count is intentionally **12 cross-cutting patterns**, not 13. The actor pattern observation (autonomous multi-commit sub-arc with sub-arc-boundary review) is documented in `lessons-learned-q5-external-certificates.md` §3 as a single-arc observation, not promoted to a META pattern. META conventions reserve §2 for patterns that reference 2+ arcs and arc-specific lessons; a single-arc observation does not meet the threshold for promotion. When/if a second arc demonstrates the pattern independently, the observation can be elevated.

---

## 3. Actionable insights for Q6+ (post-Q5)

The Q4 v3 spec (`docs/story-q4-bounded-orbit-certificates.md` § "Out of scope") explicitly defers external-certificate inhabitation to Q5+. The certificate contract is **already defined** in master — `BoundedOrbitCertificate t l` at `437225f`. Q5+ just needs to construct inhabitant instances.

**Note (Codex review feedback on PR #60, 2026-08-23):** § 3 was substantively revised in v2 to address three architectural refinement points — search-outside-Lean / verify-inside-Lean trust boundary, per-leaf availability pattern, and scope to concrete generated tree / bounded certificate dataset. The original v1 § 3 ("Two viable paths: Path A / Path B") left an implementation-equivalence gap in Path A that the new architecture closes.

### 3.1 Recommended Q5 architecture: search outside Lean, verify inside Lean

Per Codex review feedback on PR #60, the recommended Q5 architecture is a pipeline where Python handles search/generation (fast iteration, easy to debug) and Lean handles verification (kernel-checked, trusted):

```
Python search/generator → serialized proof artifact → small Lean verifier
                       → verifier soundness theorem → BoundedOrbitCertificate
                       → existing companion theorem
```

**Why not the naive Path A** (Python checker + Lean `checker_sound` theorem certifying the Python implementation is sound): the Lean theorem `checker_sound py_checker → ...` would require an implementation-equivalence proof between the Python implementation and the Lean specification. That proof is hard to get right, and an unverified implementation-equivalence gap leaks into the trusted computing base.

**Correct architecture** (per Codex review on PR #60):
- **Python search/generator**: emits deterministic, serialized trajectory certificates (e.g., JSON-encoded list of `(input, steps, witness)` per claim).
- **Small Lean verifier**: parses the serialized certificate + checks `∀ claim, checkTrajectory c = true → ReachesOne n` (a `Decidable` predicate on serialized certificates).
- **Verifier soundness theorem**: `checkTrajectory c = true → ReachesOne n` (kernel-checked).
- **`BoundedOrbitCertificate` construction**: `cert.orbit_hits_claim` and `cert.claim_reaches_one` populated from the verified serialized certificate.
- **Existing companion theorem**: `coverage_tree_soundness_orbit_cert` applies unchanged.

**Trust boundary**: Python can be buggy without entering the trusted computing base. Only the small Lean verifier + verifier soundness theorem need to be trusted. Python's role is reduced to generating candidates; verification is entirely in Lean.

### 3.2 Per-leaf availability (Codex feedback #2 on PR #60)

Avoid the naive shape `∀ x > 0, ∃ l, BoundedOrbitCertificate t l` — that doesn't relate `x` to the selected leaf; one reusable certified leaf could satisfy it for every `x`.

**Correct shape**: prove per-leaf availability separately, then compose with existing routing:
- `per_leaf_available : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l`
- Compose with `descend_orbit_complete` + `coverage_tree_soundness_orbit_cert`

OR include the actual `descendOrbit t x 0 = some l` witness in the existential:
- `∀ x > 0, ∃ l, descendOrbit t x 0 = some l ∧ BoundedOrbitCertificate t l`

The first shape (per-leaf + compose) is cleaner — it separates the per-leaf certificate construction from the routing.

### 3.3 Avoid universal acceptance criterion (Codex feedback #3 on PR #60)

If every selected leaf of every valid complete tree automatically receives an inhabited `BoundedOrbitCertificate`, the conditional boundary that correctly prevents the companion theorem from becoming a global Collatz result may disappear.

**Scope Q5 to a concrete generated tree / bounded certificate dataset**:
- A concrete `depthTwoTree` (or similar finite tree) is generated and verified
- Lean verifies each finite certificate (per-leaf via the verifier soundness theorem)
- Those verified instances are composed with `coverage_tree_soundness_orbit_cert` to close the per-`x` theorem for THAT specific tree

The universal-`∀ t`-quantified theorem stays conditional (assumes `hCert`). The Q5 acceptance criterion is "the verified certificate dataset for THIS specific tree", not "all valid complete trees".

### 3.4 Per-shape proof obligations

Per the Q4 v3 spec table:

| Claim | `orbit_hits_claim` (per-shape) | `claim_reaches_one` (per-shape) | Q5+ scope |
|---|---|---|---|
| `.empty` | `False` | Vacuously (from `False` premise) | Trivial |
| `.singleton n` | `accelerated_orbit x k = n` | Single trajectory check: `ReachesOne n` | Per-instance — needs `n`'s trajectory certificate |
| `.bounded K` | `accelerated_orbit x k ≤ K` | Finite enumeration: `∀ y ≤ K, ReachesOne y` | Per-bound — needs all `y ≤ K` trajectory certificates |
| `.interval _ _ _` | NOT APPLICABLE | N/A | Out of Q5+ scope (handled by Q3 v4 `LeafCertificate` + `coverage_tree_soundness_cert`) |

### 3.5 Trust boundary hygiene

- **Python tests** in `tests/test_coverage_tree.py` are **UNTRUSTED RUNTIME EVIDENCE**, not formal Lean substitution (per MEMORY.md note + PR #55 v3 spec § "Restoring the direct Lean D1 regression is a separate workstream")
- **The depth-two discriminator** (scenario 5 `descendOrbit depthTwoTree 5 0 = some D1` as Lean assertion) is DEFERRED — Lean 4 toolchain can't compile-check the recursive `descendFromOrbit` (uses `acceleratedStep` → `twoAdicValuation` → `Nat.factorization`, opaque to kernel reduction). The discriminator IS covered via scenario 6 (theorem + `OrbitRoute` witness at theorem level) + Python runtime tests.
- **Q5+ Lean proofs of verifier soundness** must be kernel-checked, not Python-evidenced. The `Enforce Lean admission budget` step will catch any new admission.
- **Per the recommended architecture** (§ 3.1): Python can be buggy without entering the trusted computing base. The verifier soundness theorem is the only bridge from Python output to Lean-checked result.

### 3.6 Q5+ execution order (suggested, per the recommended architecture)

1. **Q5 PR #1 (spec)**: design the serialized certificate format + verifier interface. Document the per-shape proof obligation strategy + the concrete tree scope.
2. **Q5 PR #2 (verifier)**: implement the small Lean verifier (`checkTrajectory`) + prove the verifier soundness theorem (`checkTrajectory c = true → ReachesOne n`). Lean-only — no Python integration at this stage.
3. **Q5 PR #3 (Python generator)**: implement the Python trajectory generator that emits serialized certificates. UNTRUSTED — only the verifier soundness theorem matters.
4. **Q5 PR #4 (integration)**: prove per-leaf availability (`per_leaf_available`) for a concrete tree (e.g., `depthTwoTree`) by composing Python-generated certificates with the Lean verifier. Extend the companion theorem's `hCert` substitution for that specific tree.

---

## 4. Future work guidance

### 4.1 For future companion theorem / data layer arcs

Apply the 4-PR split (Pattern 2.7) + the patterns above:
1. **Spec first** — architectural decisions, execution order, dependencies. Include the "what's established vs deferred" wording from Pattern 2.9 in the outcome statement.
2. **Foundation lemmas + compile-checked scenarios** — the smallest building blocks with executable spec (no `by sorry` defaults, per Pattern 2.1).
3. **Data types + companion theorems** — proof-carrying data pattern (Pattern 2.2) + `: Type` sort rationale (Pattern 2.2) + explicit `hCert` hypothesis (Pattern 2.10) + no new sorry discipline (Pattern 2.1).
4. **Companion theorem + BDD scenarios** — parallel predicate design if routing relation changes (Pattern 2.3) + real API-shape regression via `def` projection (not `#check`) + applyResidueReaches/applyOrbitReaches pattern for routing-hyp differentiation (Q4 v3 lesson).
5. **Lessons-learned doc (conditional)** — if notable patterns emerged (≥3 cross-cutting insights), write a lessons-learned doc capturing them. Otherwise, defer to a future meta doc.

### 4.2 For position-sensitive Lean edits (the recurring guard)

Apply Pattern 2.4's checklist:
- Read the file from the top before committing
- Check: every consumer in the new code's body — what's its def position?
- Check: every type signature referenced — what's its def position?
- If any consumer is ABOVE the new code's insertion point → forward-reference cascade; move the new code past it
- Two docstring-anchored fixes for the SAME pattern in the SAME PR = STOP, re-read the file

### 4.3 For self-evaluation between iterations

Apply Pattern 2.5:
- Scan ALL pending Codex reviews on the PR
- Not just synthesize the latest against an earlier baseline
- If there's a pending review between your last review-read and your new commit, re-read it explicitly before declaring iteration ready

### 4.4 For wording precision in lessons-learned docs

Apply Pattern 2.9:
- Distinguish "established" (kernel-checked) from "deferred" (workstream acknowledged but not yet implemented)
- The "no global Collatz convergence" boundary applies to docs too
- Overclaim propagates into reviewer expectations

### 4.5 For hypothesis-bearing proof obligations

Apply Pattern 2.11:
- The companion theorem's proof obligations MUST be hypothesis-bearing
- The tree-soundness bridge cannot prove the per-leaf Collatz result
- It only transports a certificate hypothesis to a conclusion

---

## 5. Conclusion

This meta doc captures cross-cutting patterns that emerged from 4 arcs (02c/03c + 07c-2 + Q3 + Q4) and 9 PRs. The 12 patterns are organized for future reference:
- **Patterns 2.1, 2.10, 2.11** — companion theorem architecture (every arc)
- **Pattern 2.2** — proof-carrying data + companion theorem (Q3 + Q4)
- **Pattern 2.3** — parallel predicate design (Q4 v3 lesson)
- **Pattern 2.4** — position verification before commit (Q4 3x + 02c/03c PR #46 3x)
- **Pattern 2.5** — self-evaluation must scan ALL pending Codex reviews (PR #55 v2.1 lesson)
- **Pattern 2.6** — multi-iteration convergence is a signal
- **Pattern 2.7** — the 4-PR split works (Q4 v3 run-21858 resolution)
- **Pattern 2.8** — trim transient history from production Lean docstrings (PR #56/57/58 v3)
- **Pattern 2.9** — be precise about established vs deferred (Q4 lessons-learned P1 fix)
- **Pattern 2.12** — Lean CI is the sole validation gate

For Q5+ (external-certificate inhabitation), use Section 3's path + per-shape proof obligation table + trust boundary hygiene guidance.

For future arc work, use Section 4's guidance — apply the 4-PR split, position-verify before commit, scan all pending reviews, be precise about established vs deferred.

See `docs/lessons-learned-07c-2.md` (PR #50) for the 07c-2 arc-specific lessons; `docs/lessons-learned-q4-bounded-orbit.md` (PR #59) for the Q4 arc-specific lessons. Use this meta doc when starting a new arc or when a pattern recurs across arcs.