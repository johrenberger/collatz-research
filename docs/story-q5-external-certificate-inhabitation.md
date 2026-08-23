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

The Python generator emits deterministic, serialized trajectory certificates. The format is text-based JSON for inspectability + easy debugging:

```json
{
  "claim": { "type": "singleton", "n": 5 },
  "trajectory": [
    { "step": 0, "value": 5, "op": "start" },
    { "step": 1, "value": 16, "op": "acceleratedStep" },
    { "step": 2, "value": 8,  "op": "acceleratedStep" },
    { "step": 3, "value": 4,  "op": "acceleratedStep" },
    { "step": 4, "value": 2,  "op": "acceleratedStep" },
    { "step": 5, "value": 1,  "op": "acceleratedStep" }
  ]
}
```

**Shape**:
- `claim`: `{"type": "singleton", "n": N}` (per-instance trajectory reaching `N`) or `{"type": "bounded", "K": K, "y": Y}` (per-bound trajectory within `Y ≤ K`)
- `trajectory`: list of `{step, value, op}` where `op` is `"start"` for the first step + `"acceleratedStep"` for subsequent steps

**Why JSON**: easy to inspect + diff + version; trivially serializable from Python; trivially parsable in Lean (via Mathlib `Json` or a small hand-rolled parser for this fixed schema).

**Determinism**: Python generator must be deterministic (same input → same output bytes) so that the Lean verifier can trust the certificate contents without re-running Python.

### 4.2 Verifier interface (`Certificate` inductive type + `checkTrajectory : Certificate → Bool`)

Lean defines a `Certificate` structure (or inductive) that represents a parsed trajectory:

```lean
-- Per Q5 PR #2 (verifier implementation)
inductive CertificateOp where
  | start : Nat → CertificateOp           -- the starting value
  | acceleratedStep : Nat → CertificateOp  -- the result of acceleratedStep

structure Certificate where
  claim : FiniteOrbitClaim
  trajectory : List CertificateOp

def checkTrajectory : Certificate → Bool
  -- 1. Verify trajectory[0] is `start` (the claim's anchor value)
  -- 2. Verify each subsequent step is `acceleratedStep` of the previous step
  -- 3. Verify the final value satisfies the claim
```

The verifier is `Decidable` (returns `Bool`) so it can be used in `if`/`then`/`else` expressions.

### 4.3 Verifier soundness theorem (`checkTrajectory_sound`)

The kernel-checked bridge from Python output to Lean-checked result:

```lean
theorem checkTrajectory_sound (c : Certificate) (h : checkTrajectory c = true) :
    (∃ n, c.claim = FiniteOrbitClaim.singleton n ∧
         c.trajectory matches n's orbit reaching 1) ∨
    (∃ K Y, c.claim = FiniteOrbitClaim.bounded K ∧ Y ≤ K ∧
         c.trajectory matches Y's orbit reaching 1) := by
  sorry  -- Q5 PR #2 (verifier) proves this
```

**Statement**: if `checkTrajectory c = true`, then the trajectory encoded in `c` correctly reaches 1 for the claimed finite value. **This is the ONLY theorem Python output relies on.** Python can be buggy in any other way without affecting the Lean trust base.

### 4.4 Per-leaf availability pattern (`per_leaf_available`)

Per Codex review feedback #2 on PR #60, avoid the universal shape `∀ x, ∃ l, BoundedOrbitCertificate t l` (one reusable certified leaf could satisfy it for every `x`). Instead, prove per-leaf availability separately:

```lean
-- Q5 PR #4 (integration)
theorem per_leaf_available (t : CoverageTree) [ValidTree t] [IsComplete t]
    (depthTwoTree : CoverageTree)  -- concrete tree
    (depthTwoTree_is_target : depthTwoTree = t)  -- or use defeq directly
    (certs : List Certificate)  -- bounded dataset from Python generator
    (h_certs_valid : ∀ c ∈ certs, checkTrajectory c = true) :
    ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
      BoundedOrbitCertificate depthTwoTree l := by
  sorry  -- Q5 PR #4 (integration) proves this
```

The theorem takes the concrete tree + the bounded certificate dataset + a verification proof that all certificates are valid, and produces a `BoundedOrbitCertificate t l` for each verified leaf.

**Composition**: with `per_leaf_available` in hand, the Q4 companion theorem `coverage_tree_soundness_orbit_cert` applies unchanged (its `hCert` hypothesis is now satisfied by `per_leaf_available`):

```lean
-- Q5 PR #4 (integration) — closed-form theorem for the concrete tree
example (depthTwoTree : CoverageTree)
    (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (certs : List Certificate)
    (h_certs_valid : ∀ c ∈ certs, checkTrajectory c = true)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree x 0 = some l ∧
         OrbitLeafReachesOne depthTwoTree l := by
  have hCert := per_leaf_available depthTwoTree certs h_certs_valid
  exact coverage_tree_soundness_orbit_cert depthTwoTree hv hc hCert x hx
```

The Q4 conditional companion theorem now closes for the concrete tree + the verified certificate dataset.

### 4.5 Scope to concrete tree / bounded certificate dataset (avoid universal acceptance)

Per Codex review feedback #3 on PR #60, scope Q5 to a concrete generated tree + bounded certificate dataset. The universal-`∀ t`-quantified theorem stays conditional (assumes `hCert`); Q5 acceptance criterion is "the verified certificate dataset for THIS specific tree", not "all valid complete trees".

**Canonical concrete tree**: `depthTwoTree` (defined in `Lean/CollatzResearch/CoverageTreeOrbitTests.lean` for Q4 scenarios 5/6/8/11). It's a depth-two tree with root modulus 4, depth-one internal modulus 3, six leaves at depth 2. Small enough for bounded dataset; deep enough for non-trivial routing.

**Bounded certificate dataset**: per-leaf certificates for each verified leaf in `depthTwoTree`. For each leaf, a `.singleton n` or `.bounded K` certificate encoding the trajectory to 1.

**Trust boundary preservation**: Python emits certificates for `depthTwoTree`'s leaves; Lean verifier + verifier soundness theorem converts successful verification to `BoundedOrbitCertificate depthTwoTree l`; `coverage_tree_soundness_orbit_cert` closes for `depthTwoTree` + the verified dataset.

**Why bounded**: the conditional boundary (the `hCert` hypothesis) is preserved. The theorem does NOT claim "every valid complete tree automatically receives an inhabited `BoundedOrbitCertificate`" — only "this specific tree with this verified dataset". This avoids accidentally strengthening the theorem target beyond what the project has established.

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

- **THIS DOC (v1)**: initial design. Applies 12 cross-cutting patterns from META lessons-learned + 3 Codex refinement points from PR #60 review.

**Recommended next move**: apply this spec + open Q5 PR #2 (verifier — Lean-only, kernel-checked). The verifier is the foundation; the Python generator + integration build on top of it.