# Story Q5 — External-Certificate Inhabitation (constructive `BoundedOrbitCertificate t l` via Python search + Lean verifier)

**Status:** v1 spec (initial design).
**Scope:** 4-PR split per meta doc Pattern 2.7 — spec (this doc) → verifier (Lean-only, kernel-checked) → Python generator (UNTRUSTED) → integration (per-leaf availability + companion theorem `hCert` substitution). Concrete tree scope: `depthTwoTree` (per Q4 v3 spec scenarios 5/6/8/11) + bounded certificate dataset.
**Outcome:** Trust-bounded external-certificate construction. Python emits serialized trajectory certificates; Lean parses + verifies them; verifier soundness theorem converts successful verification into `ReachesOne n`; verified certificates populate `BoundedOrbitCertificate t l`. Scoped to ONE concrete generated tree (NOT universal-`∀ t`-quantified) per Codex review feedback #3 on PR #60.

This doc applies the 12 cross-cutting meta-lessons captured in `docs/lessons-learned-meta.md`. Specifically:
- **Pattern 2.4** (position verification before commit) — read the file's full def order before committing
- **Pattern 2.7** (the 4-PR split works) — spec → foundation → data → theorem → lessons
- **Pattern 2.9** (be precise about established vs deferred) — "expressible as" + "constructive inhabitation remains" wording
- **Pattern 2.10** (conditional companion theorem pattern) — explicit `hCert` hypothesis preserved
- **Pattern 2.11** (hypothesis-bearing proof obligations) — per-leaf certificate construction is external

---

## 1. Revision history

- **v1 (THIS DOC)**: initial design. Applies the 3 Codex refinement points from PR #60 review (`lessons-learned-meta.md` § 3.1–§ 3.3):
  - **#1 Trust boundary explicit**: search outside Lean, verify inside Lean. Python emits deterministic serialized trajectory certificates; Lean parses + verifies them; verifier soundness theorem is the only bridge from Python output to Lean-checked result.
  - **#2 Per-leaf availability pattern**: prove `per_leaf_available : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l` separately, compose with existing routing. NOT the universal `∀ x, ∃ l, BoundedOrbitCertificate t l`.
  - **#3 Avoid universal acceptance criterion**: scope to a concrete generated tree (`depthTwoTree`) + bounded certificate dataset. Universal-`∀ t`-quantified theorem stays conditional (assumes `hCert`).
- **v2 (THIS DOC)**: BLOCKING design fixes from PR #61 Codex review. Resolves 3 architectural flaws:
  - **#1 Wrong transition semantics** (fix in § 4.1): v1 example used `5 → 16 → 8 → 4 → 2 → 1` labeled as `acceleratedStep` (actually `standardStep`). In this project `acceleratedStep 5 = 1` (one step: `3*5+1 = 16`, divide by `2^4 = 1`). Fixed: examples now use correct `acceleratedStep` trajectories (`.singleton 5` → `5 → 1`; `.singleton 7` → `7 → 11 → 17 → 13 → 5 → 1`). **Critical**: the verifier MUST check the same `acceleratedStep` relation used by `accelerated_orbit` (not the standard Collatz sequence).
  - **#2 Missing `orbit_hits_claim` proof source** (fix in § 4.3.2 + § 4.4): trajectory validity only proves `claim_reaches_one`; `orbit_hits_claim` (universal routing-to-claim obligation over every `x` routed to `l`) requires a separate leaf-indexed `OrbitHitEvidence t l claim` derived from concrete tree structure. Fixed: § 4.3.2 adds `OrbitHitEvidence` structure; § 4.4 `per_leaf_available` now takes BOTH `TrajectoryCertificate` dataset (for `claim_reaches_one` via `checkTrajectory_sound`) AND `OrbitHitEvidence` dataset (for `orbit_hits_claim`). Either alone is insufficient; together they construct the full `BoundedOrbitCertificate`.
  - **#3 `.bounded K` requires exhaustive coverage** (fix in § 4.1 + § 4.2 + § 4.3.1): v1 shape `{"type":"bounded","K":K,"y":Y}` only proved ONE trajectory for ONE `Y ≤ K`. But `claim_reaches_one` for `.bounded K` is `∀ y, y ≤ K → ReachesOne y`. Fixed: `.bounded K` certificate now carries `trajectories : List (List TrajectoryCertificateOp)` covering every `y ∈ [0, K]`; verifier checks `trajectories.length = K + 1` AND each trajectory is valid; soundness theorem yields `∀ y, y ≤ K → ReachesOne y`.

**v2 recommended architecture** (updated):
```
Python generator → accelerated-trajectory certificates → Lean trajectory verifier → claim_reaches_one
concrete-tree routing/finite-bound proof → orbit_hits_claim
claim + orbit_hits_claim + claim_reaches_one → BoundedOrbitCertificate t l
per-leaf indexed dataset/evidence → existing coverage_tree_soundness_orbit_cert
```
Search-outside-Lean / verify-inside-Lean direction remains good; the required change is to model the two certificate obligations separately and ensure `.bounded K` evidence is genuinely exhaustive.

- **v3 (THIS DOC)**: BLOCKING architectural fix per Codex review on v2 (2026-08-23T19:09:56Z). The v2 `OrbitHitEvidence` had the same universal quantifier as the existing `BoundedOrbitCertificate.orbit_hits_claim` — proving it for every `x` routed to `l` is the Collatz conjecture (the tree still routes infinitely many inputs, even if the tree itself is finite and complete). Scoping to ONE concrete complete tree does **not** make the theorem bounded: the tree still routes an unbounded/infinite input domain. The current PR #4 target therefore still collapses toward the global Collatz conjecture. v3 fix: introduce a NEW `BoundedInputOrbitCertificate` structure with an explicit `N : Nat` bound on the input domain (`∀ x, x ≤ N → descendOrbit t x 0 = some l → ∃ k, claim.Holds (accelerated_orbit x k)`). The v2 fixes (accelerated-step semantics, split obligations, `.bounded K` exhaustive coverage) are all preserved. The remaining blocker was specifically the **unbounded quantifier in `orbit_hits_claim` / PR #4 acceptance criterion** — now bounded via `∀ x ≤ N`. The Python generator can exhaustively generate evidence for `x ≤ N`; Lean verifies the certificates; the final theorem is meaningful without requiring a proof over the infinite routing preimage of each leaf.

**v3 recommended architecture** (updated):
```
Python generator (exhaustive for x ≤ N) → bounded-input certificates → Lean trajectory verifier → claim_reaches_one
bounded-input orbit hits (for x ≤ N) → orbit_hits_claim
claim + orbit_hits_claim + claim_reaches_one → BoundedInputOrbitCertificate t l N
per-leaf bounded-input dataset → existing coverage_tree_soundness_orbit_cert
closed-form theorem for ∀ x ≤ N (bounded domain)
```

**Note**: The existing `BoundedOrbitCertificate` (from PR #57) remains as the formal "what we want to prove" type (hypothesis-bearing for the universal quantifier over all `x`). `BoundedInputOrbitCertificate` is the NEW constructible certificate for Q5 — bounded-input version for explicit finite domains. The two coexist:
- `BoundedOrbitCertificate` (PR #57, master): formal type, hypothesis-bearing — the unconditional orbit-routing claim over all `x`
- `BoundedInputOrbitCertificate` (Q5 PR #2, new): constructible type with bounded quantifier — proves the orbit-routing claim for `x ≤ N`

---

## 2. Motivation

The Q4 v3 spec (`docs/story-q4-bounded-orbit-certificates.md` § "Out of scope") explicitly defers external-certificate inhabitation to Q5+. The certificate contract is **already defined** in master at `a7154e8` — `BoundedOrbitCertificate t l`:
- `claim : FiniteOrbitClaim` (data field)
- `orbit_hits_claim : ∀ x, descendOrbit t x 0 = some l → ∃ k, claim.Holds (accelerated_orbit x k)` (orbit-state-relative routing-to-claim obligation)
- `claim_reaches_one : ∀ y, claim.Holds y → ReachesOne y` (reachability obligation)

The Q4 companion theorem `coverage_tree_soundness_orbit_cert` merely **assumes** `hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l` as an explicit hypothesis. No certificate inhabitant was constructed in Q4. **Q5+ constructs the inhabitant.**

Per the lessons-learned-meta doc § 3.1 (recommended Q5 architecture), the trust boundary must be explicit: **search outside Lean, verify inside Lean**. Python handles search/generation (fast iteration, easy to debug); Lean handles verification (kernel-checked, trusted).

---

## 3. Architectural context

The Q5 pipeline:

```
Python search/generator
        │
        ▼
serialized proof artifact (JSON, deterministic)
        │
        ▼
small Lean verifier (parses + checks → Certificate)
        │
        ▼
verifier soundness theorem (kernel-checked: checkTrajectory c = true → ReachesOne n)
        │
        ▼
BoundedOrbitCertificate t l (claim + orbit_hits_claim + claim_reaches_one)
        │
        ▼
existing companion theorem: coverage_tree_soundness_orbit_cert (hCert populated from per_leaf_available)
```

**Trust boundary**: Python can be buggy without entering the trusted computing base (TCB). Only the small Lean verifier + verifier soundness theorem need to be trusted. The verifier soundness theorem is the ONLY bridge from Python output to Lean-checked result.

---

## 4. Design

### 4.1 Serialized certificate format (text-based JSON)

The Python generator emits deterministic, serialized trajectory certificates. The format is text-based JSON for inspectability + easy debugging.

**Per Codex review feedback on PR #61 (v2 fix)**: in this project `acceleratedStep` for an odd `n` is the result of reducing `3n+1` by its **full 2-adic factor** (divide by `2^ν₂(3n+1)`). So `acceleratedStep 5 = 1` (since `3*5+1 = 16`, `ν₂(16) = 4`, `16 / 16 = 1`), not the standard Collatz sequence. The trajectory `5 → 16 → 8 → 4 → 2 → 1` is the standard Collatz trajectory under `standardStep`, NOT `acceleratedStep`. The verifier MUST check the same `acceleratedStep` relation used by `accelerated_orbit`.

**Simple example — `.singleton 5`** (one step):
```json
{
  "claim": { "type": "singleton", "n": 5 },
  "trajectory": [
    { "step": 0, "value": 5, "op": "start" },
    { "step": 1, "value": 1, "op": "acceleratedStep" }
  ]
}
```
`acceleratedStep 5 = 1` because `3*5+1 = 16` divides by `2^4 = 16` to give `1`. The trajectory is `5 → 1`.

**Multi-step example — `.singleton 7`** (six steps under `acceleratedStep`):
```json
{
  "claim": { "type": "singleton", "n": 7 },
  "trajectory": [
    { "step": 0, "value": 7,  "op": "start" },
    { "step": 1, "value": 11, "op": "acceleratedStep" },
    { "step": 2, "value": 17, "op": "acceleratedStep" },
    { "step": 3, "value": 13, "op": "acceleratedStep" },
    { "step": 4, "value": 5,  "op": "acceleratedStep" },
    { "step": 5, "value": 1,  "op": "acceleratedStep" }
  ]
}
```
`accelerated_orbit 7 = 7 → 11 → 17 → 13 → 5 → 1`. Each step is `acceleratedStep` of the previous: `7 → 11` (`3*7+1 = 22`, `ν₂(22) = 1`, `22/2 = 11`); `11 → 17` (`3*11+1 = 34`, `ν₂(34) = 1`, `34/2 = 17`); `17 → 13` (`3*17+1 = 52`, `ν₂(52) = 2`, `52/4 = 13`); `13 → 5` (`3*13+1 = 40`, `ν₂(40) = 3`, `40/8 = 5`); `5 → 1` (as above).

**Bounded example — `.bounded K`** (per Codex feedback #3: must aggregate ALL `y ≤ K` trajectories, not one):
```json
{
  "claim": { "type": "bounded", "K": 2 },
  "trajectories": [
    { "y": 0, "trajectory": [{ "step": 0, "value": 0, "op": "start" }, { "step": 1, "value": 1, "op": "acceleratedStep" }] },
    { "y": 1, "trajectory": [{ "step": 0, "value": 1, "op": "start" }] },
    { "y": 2, "trajectory": [{ "step": 0, "value": 2, "op": "start" }, { "step": 1, "value": 1, "op": "acceleratedStep" }] }
  ]
}
```
`claim_reaches_one` for `.bounded K` is `∀ y, y ≤ K → ReachesOne y`. The certificate MUST carry a trajectory for EACH `y ≤ K` (here: `K = 2`, so 3 trajectories for `y = 0, 1, 2`). A single trajectory for a single `y` is insufficient — the verifier checks `trajectories.length = K + 1` AND each trajectory is valid AND reaches 1.

**Shape summary**:
- `claim`: `{"type": "singleton", "n": N}` OR `{"type": "bounded", "K": K}` (note: bounded does NOT carry a single `y`; the trajectories cover all `y ≤ K`)
- `trajectory` (for singleton): list of `{step, value, op}` where `op` is `"start"` for the first step + `"acceleratedStep"` for subsequent steps
- `trajectories` (for bounded): list of `{y, trajectory}` covering every `y ∈ [0, K]`

**Why JSON**: easy to inspect + diff + version; trivially serializable from Python; trivially parsable in Lean (via Mathlib `Json` or a small hand-rolled parser for this fixed schema).

**Determinism**: Python generator must be deterministic (same input → same output bytes) so that the Lean verifier can trust the certificate contents without re-running Python.

### 4.2 Verifier interface (`TrajectoryCertificate` inductive type + `checkTrajectory : TrajectoryCertificate → Bool`)

Lean defines a `TrajectoryCertificate` inductive that represents a parsed trajectory. Per Codex feedback #3 on PR #61 (v2 fix), the certificate supports two shapes — `.singleton` (single trajectory for one value) + `.bounded` (aggregation of trajectories covering all `y ≤ K`):

```lean
-- Per Q5 PR #2 (verifier implementation)
inductive TrajectoryCertificateOp where
  | start : Nat → TrajectoryCertificateOp           -- the starting value
  | acceleratedStep : Nat → TrajectoryCertificateOp  -- the result of acceleratedStep

inductive TrajectoryCertificate where
  | singleton (n : Nat) (trajectory : List TrajectoryCertificateOp)
  | bounded (K : Nat) (trajectories : List (List TrajectoryCertificateOp))

def check_singleton_trajectory (n : Nat) (traj : List TrajectoryCertificateOp) : Bool
  -- 1. Verify traj[0] is `start n` (the anchor value)
  -- 2. Verify each subsequent step is `acceleratedStep` of the previous step
  --    (full 2-adic reduction: step_i+1 = step_i * 3 + 1 divided by 2^ν₂(...))
  -- 3. Verify the final value is 1

def checkTrajectory : TrajectoryCertificate → Bool
  | .singleton n traj => check_singleton_trajectory n traj
  | .bounded K trajs =>
    trajs.length = K + 1 ∧  -- exactly K+1 trajectories, one per y ∈ [0, K]
    ∀ i, i < trajs.length → check_singleton_trajectory i trajs[i]!
```

The verifier is `Decidable` (returns `Bool`) so it can be used in `if`/`then`/`else` expressions. Note: `check_singleton_trajectory` checks the **actual `acceleratedStep` semantics** (full 2-adic reduction of `3n+1`), NOT the standard Collatz sequence. The verifier soundness theorem (§ 4.3.1) relies on this.

### 4.3 Verifier soundness theorem + `OrbitHitEvidence` (split obligations)

Per Codex feedback #2 on PR #61 (v2 fix), the spec splits the two certificate obligations:
- `TrajectoryCertificate` / verifier soundness theorem proves ONLY `claim_reaches_one`
- Separate leaf-indexed `OrbitHitEvidence t l claim` proves `orbit_hits_claim`

**Why split**: `BoundedOrbitCertificate t l` requires BOTH obligations:
- `claim_reaches_one : ∀ y, claim.Holds y → ReachesOne y` (provided by `TrajectoryCertificate` + verifier soundness)
- `orbit_hits_claim : ∀ x, descendOrbit t x 0 = some l → ∃ k, claim.Holds (accelerated_orbit x k)` (universal routing-to-claim obligation; provided by `OrbitHitEvidence`)

A finite trajectory dataset does NOT establish the universal `orbit_hits_claim`. The two proof sources are independent and both required.

#### 4.3.1 `TrajectoryCertificate` verifier soundness theorem

The kernel-checked bridge from Python output to `claim_reaches_one`:

```lean
theorem checkTrajectory_sound :
    ∀ c, checkTrajectory c = true →
      match c with
      | .singleton n _ => ReachesOne n
      | .bounded K _ => ∀ y, y ≤ K → ReachesOne y := by
  sorry  -- Q5 PR #2 (verifier) proves this
```

**Statement**: if `checkTrajectory c = true`, then either:
- `.singleton n _` → `ReachesOne n` (single trajectory reaches 1)
- `.bounded K _` → `∀ y, y ≤ K → ReachesOne y` (every y in [0, K] reaches 1 — exhaustive coverage per Codex feedback #3)

**This is the ONLY theorem Python output relies on.** Python can be buggy in any other way without affecting the Lean trust base.

#### 4.3.2 `BoundedInputOrbitCertificate` (bounded-input certificate for finite domain)

**v3 fix (per Codex review feedback on PR #61 v2, 2026-08-23T19:09:56Z)**: The v2 `OrbitHitEvidence` had the same universal quantifier as the existing `BoundedOrbitCertificate.orbit_hits_claim` — proving it for every `x` routed to `l` is the Collatz conjecture (the tree still routes infinitely many inputs, even if the tree itself is finite and complete). Scoping to ONE concrete complete tree does **not** make the theorem bounded.

The v3 pivot: bound the input domain explicitly via a new `BoundedInputOrbitCertificate` structure:

```lean
-- Per Q5 PR #2 (verifier) + Q5 PR #4 (integration) — bounded-input variant
structure BoundedInputOrbitCertificate
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat) where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, x ≤ N →
      descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y
```

**Why bounded**: the universal quantifier over `x ≤ N` is bounded — Python can exhaustively generate evidence for each `x ∈ {1, 2, ..., N}`. Lean verifies the certificates. The final theorem is meaningful without requiring a proof over the infinite routing preimage of each leaf.

**Note**: The existing `BoundedOrbitCertificate` (from PR #57) remains as the formal "what we want to prove" type (hypothesis-bearing for the universal quantifier over all `x`). `BoundedInputOrbitCertificate` is the NEW constructible certificate for Q5 — bounded-input version for explicit finite domains. The two coexist:
- `BoundedOrbitCertificate` (PR #57, master): formal type, hypothesis-bearing — the unconditional orbit-routing claim over all `x`
- `BoundedInputOrbitCertificate` (Q5 PR #2, new): constructible type with bounded quantifier — proves the orbit-routing claim for `x ≤ N`

**For `depthTwoTree`** (or any concrete complete tree): the Python generator iterates over `x ∈ {1, 2, ..., N}` and emits a `BoundedInputOrbitCertificate` per leaf. The Lean verifier + soundness theorem confirm correctness. Q5 PR #4 (integration) closes the bounded-input companion theorem for `∀ x ≤ N`.

### 4.4 Per-leaf availability pattern (`per_leaf_available_bounded` — bounded-input variant)

Per Codex feedback #2 on PR #61 v3 (v2's `OrbitHitEvidence` was structurally right but didn't reduce the hard problem — needed bounded input), `per_leaf_available` is now the bounded-input version that closes the v3 Q5 acceptance criterion:

```lean
-- Q5 PR #4 (integration) — bounded-input variant
theorem per_leaf_available_bounded (depthTwoTree : CoverageTree) (N : Nat)
    (bounded_certs : depthTwoTree.leaves → BoundedInputOrbitCertificate depthTwoTree l.1 N)
    (h_trajectories_valid : ∀ l h, checkTrajectory (bounded_certs l).trajectory = true)
    (h_orbit_hits : ∀ l h, (bounded_certs l).orbit_hits_claim) :
    ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
      BoundedOrbitCertificate depthTwoTree l := by
  sorry  -- Q5 PR #4 (integration) proves this
```

The theorem takes:
- The concrete tree (`depthTwoTree`)
- The trajectory certificate dataset (one `TrajectoryCertificate` per leaf — proves `claim_reaches_one` via `checkTrajectory_sound`)
- The orbit-hits evidence dataset (one `OrbitHitEvidence` per leaf — proves `orbit_hits_claim`)
- And produces a `BoundedOrbitCertificate t l` for each verified leaf

**Why both proofs are needed**: `BoundedOrbitCertificate t l` has two obligation fields:
- `claim_reaches_one : ∀ y, claim.Holds y → ReachesOne y` (provided by `trajectory_certs` via `checkTrajectory_sound`)
- `orbit_hits_claim : ∀ x, descendOrbit t x 0 = some l → ∃ k, claim.Holds (accelerated_orbit x k)` (provided by `orbit_hits` — the `OrbitHitEvidence` for each leaf)

Either alone is insufficient. Together they construct the full `BoundedOrbitCertificate`.

**Composition**: with `per_leaf_available_bounded` in hand, the Q4 companion theorem `coverage_tree_soundness_orbit_cert` applies unchanged (its `hCert` hypothesis is now satisfied by `per_leaf_available_bounded`). The bound `x ≤ N` makes the theorem meaningful without requiring a proof over the infinite routing preimage of each leaf:

```lean
-- Q5 PR #4 (integration) — bounded-input closed-form theorem for the concrete tree
example (depthTwoTree : CoverageTree) (N : Nat)
    (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (bounded_certs : depthTwoTree.leaves → BoundedInputOrbitCertificate depthTwoTree l.1 N)
    (h_trajectories_valid : ∀ l h, checkTrajectory (bounded_certs l).trajectory = true)
    (h_orbit_hits : ∀ l h, (bounded_certs l).orbit_hits_claim)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree x 0 = some l ∧
         OrbitLeafReachesOne depthTwoTree l := by
  have hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
                BoundedOrbitCertificate depthTwoTree l := by
    intro l hl hver
    exact per_leaf_available_bounded depthTwoTree N bounded_certs
           h_trajectories_valid h_orbit_hits l hl hver
  exact coverage_tree_soundness_orbit_cert depthTwoTree hv hc hCert x hx
```

The Q4 conditional companion theorem now closes for `∀ x ≤ N` (bounded input domain) on the concrete tree + the verified datasets (bounded-input certificates). The acceptance criterion is meaningful: "for this specific tree + this specific bound + this specific verified dataset, all `x ≤ N` reach leaves with verified `BoundedOrbitCertificate`." **This preserves the conditional boundary** that correctly prevents the theorem from collapsing to the global Collatz conjecture.

### 4.5 Scope to concrete tree + bounded input domain (avoid universal acceptance)

Per Codex review feedback #3 on PR #60 (concrete tree scope) + v3 fix per Codex review on PR #61 (bounded input domain — v2's "just concrete tree" was insufficient because a complete tree still routes infinitely many inputs), Q5 is scoped to:
1. **A concrete generated tree** (e.g., `depthTwoTree`) — per leaf
2. **An explicit bound on the input domain** (`∀ x ≤ N`, not `∀ x`) — per `BoundedInputOrbitCertificate` parameter

**Canonical concrete tree**: `depthTwoTree` (defined in `Lean/CollatzResearch/CoverageTreeOrbitTests.lean` for Q4 scenarios 5/6/8/11). It's a depth-two tree with root modulus 4, depth-one internal modulus 3, six leaves at depth 2. Small enough for bounded dataset; deep enough for non-trivial routing.

**Bounded input domain**: `N : Nat` is the explicit bound. The Python generator iterates over `x ∈ {1, 2, ..., N}` and emits a `BoundedInputOrbitCertificate` per leaf. The Lean verifier + soundness theorem confirm correctness. The companion theorem closes for `∀ x ≤ N`.

**Why bounded (v3 fix)**: A complete tree (like `depthTwoTree`) still routes infinitely many inputs. Proving `orbit_hits_claim : ∀ x, descendOrbit t x 0 = some l → ...` for every routed `x` is the Collatz conjecture. The v3 fix bounds the input domain to `x ≤ N`, making the acceptance criterion meaningful and the Python generator tractable.

**Bounded certificate dataset + bounded input domain**: per-leaf `BoundedInputOrbitCertificate depthTwoTree l.1 N` certificates, each covering `x ∈ {1, ..., N}` for the leaf's routing preimage.

**Trust boundary preservation**: Python emits bounded certificates for `depthTwoTree`'s leaves; Lean verifier + verifier soundness theorem converts successful verification to `BoundedOrbitCertificate depthTwoTree l`; `coverage_tree_soundness_orbit_cert` closes for `depthTwoTree` + the verified dataset + `x ≤ N`.

**Why bounded preserves the conditional boundary**: The theorem does NOT claim "every valid complete tree automatically receives an inhabited `BoundedOrbitCertificate`" — only "this specific tree + this specific bound + this specific verified dataset". The acceptance criterion is "for `∀ x ≤ N`" (bounded), not "for all `x`" (unbounded). This avoids accidentally strengthening the theorem target beyond what the project has established.

---

## 5. Dependencies

### 5.1 In master (from Q4 arc + earlier work)

| Dependency | Source | Used for |
|---|---|---|
| `BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type` | PR #57 | The certificate type to construct via Q5 |
| `OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop` | PR #56 | The leaf-level semantic predicate the companion theorem concludes |
| `coverage_tree_soundness_orbit_cert` | PR #58 | The existing companion theorem (hCert substitution) |
| `descend_orbit_complete` | PR #29 | Orbit-aware routing + `OrbitRoute` witness |
| `accelerated_orbit` | PR #56 | The trajectory function Python verifies against |
| `acceleratedStep` | Story 02c/03c | The per-step transition function Python encodes |
| `ReachesOne` | PR #56 | The target property of any certificate's trajectory |
| `depthTwoTree` | `CoverageTreeOrbitTests.lean` (Q4 PR #56) | The concrete tree scope for Q5 |
| `coverage_tree_soundness_orbit` (separate `sorry` workstream) | PR #36 spec | NOT used by Q5 (separate workstream; per Q4 v3 spec NOT blocked on) |

### 5.2 Pending (this arc)

| Dependency | Source | Used for |
|---|---|---|
| Small Lean verifier + `Certificate` inductive type | Q5 PR #2 | Parses JSON + checks trajectory consistency |
| `checkTrajectory_sound` theorem | Q5 PR #2 | The kernel-checked bridge from Python to Lean |
| Python trajectory generator | Q5 PR #3 | UNTRUSTED — emits serialized certificates |
| `per_leaf_available` theorem | Q5 PR #4 | Per-leaf certificate construction for `depthTwoTree` |
| Closed-form `depthTwoTree` example | Q5 PR #4 | Composes `per_leaf_available` + `coverage_tree_soundness_orbit_cert` |

---

## 6. Implementation plan (4-PR split per meta doc Pattern 2.7)

### Q5 PR #1 (spec) — THIS DOC

Defines the Q5 architecture (4 above), serialized certificate format (4.1), verifier interface (4.2), verifier soundness theorem statement (4.3), per-leaf availability pattern (4.4), scope to concrete tree (4.5), 4-PR split (this section), out of scope (§ 7). Docs-only.

### Q5 PR #2 (verifier — Lean-only, kernel-checked)

Implements `Certificate` inductive type + `checkTrajectory : Certificate → Bool` + `checkTrajectory_sound` theorem (kernel-checked: `checkTrajectory c = true → ReachesOne n`). **Lean-only — no Python integration at this stage.** No `BoundedOrbitCertificate` construction; no companion theorem modifications. Just the small verifier + soundness theorem.

Executable spec scenarios in `FiniteOrbitClaimTests.lean` (or a new `Q5VerifierTests.lean`):
- Scenario A: hand-rolled `Certificate` for `.singleton 1` (trajectory 1 → 1) — `checkTrajectory c = true`
- Scenario B: hand-rolled `Certificate` for `.singleton 5` (trajectory 5 → 16 → 8 → 4 → 2 → 1) — `checkTrajectory c = true`
- Scenario C: hand-rolled `Certificate` with invalid step (e.g., claims 1 → 5 instead of 1 → 1) — `checkTrajectory c = false`
- Scenario D: polymorphic `example (c : Certificate) (h : checkTrajectory c = true) : ...` (mirrors PR #57 scenarios 11–12 polymorphic apply-the-theorem pattern)

### Q5 PR #3 (Python generator — UNTRUSTED)

Implements the Python trajectory generator that emits serialized certificates for `depthTwoTree`'s leaves. **UNTRUSTED** — only the verifier soundness theorem matters. The generator:
1. Iterates over `depthTwoTree.leaves`
2. For each leaf, computes the trajectory from the anchor value to 1 (using Python's `acceleratedStep` in `tests/test_coverage_tree.py`)
3. Emits a serialized JSON certificate per leaf
4. Outputs a `List Certificate` (parsed in Lean) + a deterministic `List Certificate` source file

**Test**: the generator's emitted certificates must pass Lean verifier + verifier soundness theorem (so they're valid by construction). If the generator emits invalid certificates, that's a Python bug; the Lean verifier rejects them; the Lean trust base is unaffected.

### Q5 PR #4 (integration — per-leaf availability + companion theorem hCert substitution)

Implements `per_leaf_available` theorem (4.4) + closed-form `depthTwoTree` example (4.4) that composes `per_leaf_available` + `coverage_tree_soundness_orbit_cert`. **This PR closes the Q5 arc** — concrete tree + verified dataset + companion theorem = closed-form theorem for `depthTwoTree`.

Executable spec scenarios:
- Scenario E: `per_leaf_available depthTwoTree certs h_certs_valid` applied to each `l ∈ depthTwoTree.leaves` — type-checks
- Scenario F: closed-form `depthTwoTree` example — `∃ l, descendOrbit depthTwoTree 5 0 = some l ∧ OrbitLeafReachesOne depthTwoTree l` (using `by native_decide` for `hv` + `hc`; `per_leaf_available` for `hCert`; `coverage_tree_soundness_orbit_cert`)

---

## 7. Out of scope (deferred)

1. **Universal-`∀ t`-quantified theorem** stays conditional (assumes `hCert`). Q5 acceptance criterion is `depthTwoTree` + bounded dataset, not "all valid complete trees". Per Codex feedback #3.
2. **Pure-Lean trajectory checker** (Path B; meta doc § 3.1): slower iteration, no external trust, more work. Could be pursued as a future Q6+ if Python trust boundary becomes untenable for some reason.
3. **Restoring the direct Lean D1 regression** (07c-3 deferred, per MEMORY.md note): separate workstream. Q5 does NOT depend on this.
4. **Cross-tree inhabitation** (one certificate dataset per tree, for multiple trees): Q5 scoped to ONE concrete tree (`depthTwoTree`). Cross-tree work would be Q6+.
5. **Python performance optimization**: correctness > performance. The Python generator can be slow; the Lean verifier must be fast.
6. **Automatic certificate generation from external sources** (e.g., Coq proofs, Isabelle proofs, proof certificates from other systems): Q5 is Python → Lean only.
7. **Optimization of verifier soundness theorem**: the theorem states `checkTrajectory c = true → ReachesOne n`. A more efficient version might directly produce the orbit step indices; deferred.

---

## 8. Codex review questions (for v2 refinement)

1. **Trust boundary explicitly scoped?** Is "search outside Lean, verify inside Lean" correctly captured in § 3 + § 4? Specifically: does the verifier soundness theorem § 4.3 isolate Python's role to "emit candidates" without leaking trust?
2. **Serialized certificate format lightweight enough?** Is the JSON-based format in § 4.1 the right level of detail? Or should Q5 PR #2 (verifier) define a more compact binary format?
3. **Per-leaf availability pattern the right shape?** Is `per_leaf_available : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l` (§ 4.4) the right shape? Or should the existential include the actual `descendOrbit t x 0 = some l` witness?
4. **Concrete tree scope appropriate?** Is `depthTwoTree` (§ 4.5) the right concrete tree, or should Q5 use a different concrete tree (deeper? more leaves? more interesting routing)?
5. **Verifier soundness theorem statement correct?** Does the disjunction in § 4.3 (singleton + bounded cases) cover all `FiniteOrbitClaim` constructors? Or should it be more uniform (e.g., parameterized by claim shape)?

---

## 9. References

- **Q4 v3 spec**: [`docs/story-q4-bounded-orbit-certificates.md`](story-q4-bounded-orbit-certificates.md) — original `BoundedOrbitCertificate` + `coverage_tree_soundness_orbit_cert` design (PR #55)
- **META lessons-learned**: [`docs/lessons-learned-meta.md`](lessons-learned-meta.md) — 12 cross-cutting patterns + Q5+ actionable insights (PR #60)
- **Q4 lessons-learned**: [`docs/lessons-learned-q4-bounded-orbit.md`](lessons-learned-q4-bounded-orbit.md) — Q4 arc-specific patterns (PR #59)
- **M4 Finite coverage Path A**: `acceleratedStep_odd_of_odd` (PR #31), `standardStep_positive` (PR #37), `acceleratedStep_positive_of_odd` (PR #38), `acceleratedStep_equiv_standardStep` (PR #46), `acceleratedTrajectory_reaches_one_implies_standard` (PR #47) — the dynamics/equivalence chain that Q5 builds on
- **07c-3 spec** (deferred direct Lean D1): separate workstream, NOT used by Q5

---

## 10. Implementation log

- **v1**: initial design. Applies 12 cross-cutting patterns from META lessons-learned + 3 Codex refinement points from PR #60 review.
- **v2**: BLOCKING design fixes from PR #61 Codex review. Resolves 3 architectural flaws (#1 wrong transition semantics; #2 missing `orbit_hits_claim` proof source; #3 `.bounded K` requires exhaustive coverage). All 3 fixed in § 4.1-4.4. The verifier MUST check the same `acceleratedStep` relation used by `accelerated_orbit` (not the standard Collatz sequence). The two certificate obligations (`claim_reaches_one` + `orbit_hits_claim`) are now modeled separately, and `.bounded K` evidence is genuinely exhaustive (one trajectory per `y ∈ [0, K]`).
- **v3**: BLOCKING architectural fix per Codex review on v2 (2026-08-23T19:09:56Z). The v2 `OrbitHitEvidence` had the same universal quantifier as `BoundedOrbitCertificate.orbit_hits_claim` — proving it for every `x` routed to `l` is the Collatz conjecture. v3 fix: introduce a NEW `BoundedInputOrbitCertificate` structure with an explicit `N : Nat` bound on the input domain (`∀ x, x ≤ N → descendOrbit t x 0 = some l → ...`). The v2 fixes (accelerated-step semantics, split obligations, `.bounded K` exhaustive coverage) are all preserved. The remaining blocker was specifically the **unbounded quantifier in `orbit_hits_claim` / PR #4 acceptance criterion** — now bounded via `∀ x ≤ N`. Python can exhaustively generate evidence for `x ≤ N`; Lean verifies; the final theorem is meaningful without requiring a proof over the infinite routing preimage of each leaf. § 4.3.2 introduces `BoundedInputOrbitCertificate`; § 4.4 introduces `per_leaf_available_bounded` (takes `N : Nat` + `bounded_certs`); § 4.5 scopes Q5 to concrete tree + bounded input domain.

**Recommended next move**: apply this spec + open Q5 PR #2 (verifier — Lean-only, kernel-checked). The verifier implements `BoundedInputOrbitCertificate` verification + `checkBoundedTrajectory` + `checkBoundedTrajectory_sound` theorem. Python generator + integration build on top.