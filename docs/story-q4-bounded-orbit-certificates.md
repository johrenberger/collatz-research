# Story Q4 — Bounded-orbit certificates for finite `LeafClaim` shapes

Status: **v3 spec (revised per Codex re-review on PR #55, runs 21848 + 21858, 2026-08-22T15:09:09Z + 2026-08-22T15:42:40Z).** Introduces `OrbitLeafReachesOne` predicate (parallel to `LeafReachesOne`, defined over `descendOrbit` instead of `descend`); removes the merge-blocking routing-predicate mismatch from the v2 theorem body; drops the tautological `wellFormed` field and `IsFinite` predicate per run-21858 P2. Re-scopes companion theorem prose as a **parallel orbit-routing theorem**, not a refinement of `coverage_tree_soundness_full` / `coverage_tree_soundness_cert`.

## Revision history

- **v1 (PR #55, commit `eaae6e8`)**: initial draft. **Rejected by Codex** at run 21843 (P1×2 + P2): `routed_implies_claim` constrained original `x` directly (same uninhabitable boundary Q3 v3 explicitly avoided); missing `ReachesOne (accelerated_orbit x k) → ReachesOne x` composition lemma; inline constructor-match disjunction.
- **v2 (commit `a24e914`)**: redesigned around `orbit_hits_claim` shape + new `FiniteOrbitClaim` type + `accelerated_orbit_compose`/`orbit_predecessor_reaches_one` foundation lemmas. Structure improved but introduced **routing-relation mismatch** at theorem conclusion: theorem concluded `LeafReachesOne t l` (defined over `descend`) while the proof actually constructs an `OrbitLeafReachesOne` (defined over `descendOrbit`). Codex run-21848 P1 flagged this.
- **v2.1 (commit `62932fc`)**: proactively aligned `wellFormed : claim.IsFinite` with Codex's sketch and dropped YAGNI `FiniteOrbitClaim.toLeafClaim` lifting. **Self-evaluation failure**: run-21848's P1 routing-relation mismatch was not addressed. Codex run-21858 re-rejected (P1 still unresolved + new P2 on tautological `IsFinite` predicate).
- **v3 (THIS DOC)**: introduces `OrbitLeafReachesOne` predicate so the theorem conclusion matches the routing evidence (`descendOrbit`-based). Drops the tautological `wellFormed` field and `IsFinite` predicate. Re-scopes companion theorem prose as a **parallel orbit-routing theorem** (not a refinement of `coverage_tree_soundness_full` / `coverage_tree_soundness_cert`, which certify a different routing relation). Adds API-shape regression to prevent conflating the two routing predicates.

## Motivation

The Q3 v3 spec ([`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md)) deferred finite `LeafClaim` constructors (`.empty`, `.singleton n`, `.bounded K`) to a separate **bounded-orbit workstream** with this rationale:

> Under current `descend` semantics (residue-only routing, no Collatz
> reduction), finite claims cannot be constructively inhabited for
> nonempty leaves. The preimage of a nonempty leaf under residue-routed
> `descend` is periodic (every residue class mod `2^k` contains
> infinitely many positive integers). It cannot be contained in
> `{x | x = n}` or `{x | x ≤ K}`.

Q3 v3 also explicitly flagged that **even under orbit-aware routing**,
the finite claim must NOT be asserted about the original input `x`
directly — the claim must be about an **orbit state**, with a
composition lemma to lift orbit-state reachability back to original-input
reachability. Q4 v1 missed the first half of this distinction. Q4 v2
fixed the certificate shape but still concluded the wrong semantic
predicate (the v2 thesis was right; the v2 conclusion was wrong). Q4
v3 corrects both — the certificate asserts the orbit-state-relative
claim, and the companion theorem concludes an **orbit-state-relative**
leaf-level semantic predicate `OrbitLeafReachesOne` (NEW), defined
parallel to `LeafReachesOne` but over `descendOrbit` instead of
`descend`.

## Architectural context

```
                                  LEAF-LEVEL SEMANTIC PREDICATES (parallel)
                                  ──────────────────────────────────────────
LeafClaim.interval claim    ─→   LeafReachesOne t l         (defined over descend)
LeafClaim.{empty,singleton,       OrbitLeafReachesOne t l    (defined over descendOrbit)
   bounded} finite claim    ─→   (NEW Q4 v3)

                                  CERTIFICATES + COMPANION THEOREMS (parallel)
                                  ──────────────────────────────────────────
LeafClaim.interval   ─→   LeafCertificate t l                ─→   coverage_tree_soundness_cert
                              : Type                           (concludes LeafReachesOne t l)
                              (Q3 v4, residue-only)             (residue-only routing)

FiniteOrbitClaim      ─→   BoundedOrbitCertificate t l       ─→   coverage_tree_soundness_orbit_cert
(NEW Q4 v3; .empty /        : Type                           (concludes OrbitLeafReachesOne t l)
 .singleton / .bounded      (Q4 v3, no wellFormed field;        (orbit-aware routing)
 only; .interval            two obligation fields:
 excluded by                orbit_hits_claim,
 construction)              claim_reaches_one)
```

**No mutual exclusion** between the two certificate types — a leaf
can carry both `LeafCertificate t l` (Q3 v4) and `BoundedOrbitCertificate
t l` (Q4 v3) as **independent views** of its semantic content:

- `LeafCertificate t l` certifies interval claims under **residue-only**
  routing (`descend`); concludes `LeafReachesOne t l`.
- `BoundedOrbitCertificate t l` certifies finite claims under
  **orbit-aware** routing (`descendOrbit`); concludes `OrbitLeafReachesOne t l`
  (NEW).

The two companion theorems certify **different routing relations** and
are **parallel, not refinements** of each other. Each API restricts its
accepted claim shapes internally.

## Design

### `OrbitLeafReachesOne` — NEW orbit-routing leaf-level semantic predicate

```lean
/-- Orbit-routing leaf-level semantic predicate, parallel to
    `LeafReachesOne` (which is defined over the residue-only router
    `descend`). `OrbitLeafReachesOne t l` asserts: every input `x`
    that the orbit-aware router `descendOrbit` selects for leaf `l`
    reaches 1 via the accelerated orbit.

    This is the predicate concluded by `coverage_tree_soundness_orbit_cert`.
    It is **not** interchangeable with `LeafReachesOne t l` — the two
    certify different routing relations (orbit-aware vs residue-only).

    Per the run-21848 Codex review on PR #55 v2: introducing
    `OrbitLeafReachesOne` is required to resolve the routing-relation
    mismatch in the v2 theorem body (which concluded `LeafReachesOne
    t l` while constructing a proof over `descendOrbit`). The kernel
    rejected the v2 proof because `descend t x = some l` and
    `descendOrbit t x 0 = some l` are different routing relations.
    This NEW predicate makes the conclusion type-safe. -/
def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descendOrbit t x 0 = some l → ReachesOne x
```

### `FiniteOrbitClaim` — restricted claim type

```lean
/-- A claim about which **orbit states** reach a leaf, restricted to
    finite shapes. The `.interval` constructor (from `LeafClaim`) is
    intentionally omitted — interval claims are residue-only routing
    territory (Q3 v4 `LeafCertificate`), not orbit-aware routing
    territory (Q4 v3 `BoundedOrbitCertificate`).

    `Holds` here is a predicate on `Nat` interpreted as an **orbit
    state** (a value `accelerated_orbit x k` for some `k : Nat`),
    NOT on the original routing input `x` directly. This is the
    critical Q4 v2 fix from the v1 spec.

    Equality-comparable, serializable. `DecidableEq` provided by
    `deriving`. -/
inductive FiniteOrbitClaim where
  | empty                       -- no orbit states
  | singleton (n : Nat)         -- exactly one orbit state: n
  | bounded (K : Nat)           -- orbit state ≤ K (finite enumeration)
  deriving Repr, DecidableEq

namespace FiniteOrbitClaim

/-- The set of orbit states claimed by a `FiniteOrbitClaim`. Pure predicate.
    `Holds y` is interpreted as "y is an orbit state reachable from some
    input routed to this leaf, AND y is claimed to reach 1". -/
def Holds (c : FiniteOrbitClaim) (y : Nat) : Prop :=
  match c with
  | .empty => False
  | .singleton n => y = n
  | .bounded K => y ≤ K

/-- Decidability instance for `FiniteOrbitClaim.Holds`. Cases:
    - `.empty` → `Decidable False`
    - `.singleton n` → `Decidable (y = n)` via `Nat.decEq`
    - `.bounded K` → `Decidable (y ≤ K)` via `Nat.decLe` -/
instance Holds.decidable (c : FiniteOrbitClaim) (y : Nat) :
    Decidable (c.Holds y) := by
  cases c <;> first
  | exact (inferInstance : Decidable False)
  | exact (inferInstance : Decidable (y = _))
  | exact (inferInstance : Decidable (y ≤ _))

/-- `IsFiniteClaim : LeafClaim → Prop` predicate, used by external code
    that needs to distinguish finite vs interval `LeafClaim` values
    (e.g., parsers, deserializers). Returns `True` for the three
    finite constructors (`.empty`, `.singleton n`, `.bounded K`) and
    `False` for `.interval`.

    Reusable across Q3/Q4 boundaries: any code that needs to check
    "is this `LeafClaim` finite-shaped?" can call this predicate. -/
def IsFiniteClaim : LeafClaim → Prop
  | .empty => True
  | .singleton _ => True
  | .bounded _ => True
  | .interval _ _ _ => False

instance IsFiniteClaim.decidable : (c : LeafClaim) → Decidable (IsFiniteClaim c)
  | .empty => inferInstance
  | .singleton _ => inferInstance
  | .bounded _ => inferInstance
  | .interval _ _ _ => inferInstance

end FiniteOrbitClaim
```

**Note (Q4 v3):** the v2.1 `FiniteOrbitClaim.IsFinite : FiniteOrbitClaim →
Prop` predicate (always `True`) has been **dropped** per Codex run-21858
P2 ("tautological obligation for symmetry"). The `BoundedOrbitCertificate`
structure no longer carries a `wellFormed` field; the finite-shape
restriction is enforced at the type level by `FiniteOrbitClaim`'s
constructor set.

### `BoundedOrbitCertificate` — proof-carrying data bundle

Type-valued (NOT `: Prop`) per Q3 v4 lesson. The structure carries a
single data field (`claim`) plus two `Prop`-valued obligation proofs
(`orbit_hits_claim`, `claim_reaches_one`). The kernel verifies that the
proof fields are consistent with the data field.

```lean
/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `OrbitLeafReachesOne t l` (the orbit-routing leaf-level
    semantic predicate) for a **finite** `FiniteOrbitClaim` shape
    (`.empty`, `.singleton n`, `.bounded K`).

    Declared as `: Type` (NOT `: Prop`) per Q3 v4 lesson: the
    `claim : FiniteOrbitClaim` data field requires the structure to
    live in `Type` (Lean 4 elaboration rejects `Type`-valued fields in
    `Prop`-valued structures). The obligation fields are still `Prop`s,
    so the kernel still verifies them — only the structure's outer sort
    is `Type`. This makes `BoundedOrbitCertificate t l` a
    **proof-carrying data bundle**: inspectable data plus kernel-checked
    proof fields. It is NOT proof-irrelevant evidence and is intended to
    be constructed, pattern-matched on, and projected through.

    **Orbit-state-relative claim shape (Q4 v2 — the v1→v2 fix).** The
    `orbit_hits_claim` field is the Q4 mechanism: it asserts that the
    routed input's orbit reaches a state satisfying the claim, NOT that
    the original input satisfies the claim. This is structurally
    different from Q3 v4's `LeafCertificate`, where `routed_implies_claim`
    is about the original input. The orbit-state-relative shape is what
    makes finite claims constructively inhabitable under `descendOrbit`.

    **Two obligation fields** (Q4 v3 — `wellFormed` removed per Codex
    run-21858 P2):
    1. `orbit_hits_claim`: every input routed (orbit-aware) to `l`
       reaches an orbit state satisfying the claim. (Routing-to-orbit-state
       obligation.) This is the field where the Q4 mechanism lives.
    2. `claim_reaches_one`: every orbit state satisfying the claim
       reaches 1. (Reachability obligation — per-input enumeration
       for `.bounded K`, single trajectory check for `.singleton n`,
       vacuous for `.empty`.)

    The companion theorem `coverage_tree_soundness_orbit_cert` takes
    `(hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)`
    as an **explicit** hypothesis (no default, no `by sorry`) per the
    project "no new sorry" discipline (PR #51 P1). -/
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y
```

**Sort rationale (`: Type`, not `: Prop`).** Same as Q3 v4: the `claim`
data field forces `: Type`. The two obligation fields are `Prop`-valued
and kernel-checked; only the outer sort is `Type`. No structural guards
(`wellFormed`) — the finite-shape restriction is enforced at the type
level by `FiniteOrbitClaim`'s constructor set. (Q4 v3 removed the
tautological `wellFormed : claim.IsFinite` field that v2.1 had kept
"for symmetry" with Q3 v4 `LeafCertificate.WellFormed`; Codex run-21858
P2 explicitly rejected symmetry-by-placeholder as a design precedent.)

**Why no `K : Nat` data field?** Q4 v1 had `K : Nat` as a separate
data field with `orbit_image_bound : claim matches .bounded K' → K' = K`
as a static consistency check. Codex flagged this as dead weight
(run-21843 P1) — the `K` is implicit in the
`claim : FiniteOrbitClaim.bounded K` constructor. The v2 certificate
drops the redundant `K` field and the `orbit_image_bound` static
check; `orbit_hits_claim` does the real work by asserting
`claim.Holds (accelerated_orbit x k)` for some `k` — when
`claim = .bounded K`, this asserts `accelerated_orbit x k ≤ K`.

### Foundation lemmas — the actual Q4 mechanism

The companion theorem's correctness depends on the foundational
lemmas that the certificate's `orbit_hits_claim` + `claim_reaches_one`
fields compose, plus a new parallel orbit-routing leaf-level semantic
predicate. **Without the foundation, the certificate is just typed
packaging** — these are what make Q4 substantively different from Q3.

```lean
/-- Orbit-additive composition: `accelerated_orbit x (k + k') =
    accelerated_orbit (accelerated_orbit x k) k'`.

    This is the elementary orbit-composition lemma: stepping forward
    by `k + k'` is the same as stepping forward by `k` then by `k'`
    more. Proof by induction on `k`. -/
theorem accelerated_orbit_compose (x : Nat) (k k' : Nat) :
    accelerated_orbit x (k + k') = accelerated_orbit (accelerated_orbit x k) k' := by
  induction k generalizing x k' with
  | zero =>
      simp [accelerated_orbit, Nat.add_zero]
  | succ k ih =>
      sorry  -- TODO PR #56 (orbit foundation)

/-- Orbit-predecessor closure: if some future state of `x`'s orbit reaches 1,
    then `x` reaches 1. Built on `accelerated_orbit_compose`.

    Proof sketch: given `accelerated_orbit x k = y` and `ReachesOne y` (i.e.,
    `∃ k', accelerated_orbit y k' = 1`), compose via `accelerated_orbit_compose`
    to get `accelerated_orbit x (k + k') = 1`, so `ReachesOne x`. -/
theorem orbit_predecessor_reaches_one (x : Nat) (k : Nat) (y : Nat)
    (h_eq : accelerated_orbit x k = y) (h_reaches : ReachesOne y) :
    ReachesOne x := by
  obtain ⟨k', hk'⟩ := h_reaches
  exact ⟨k + k', by rw [accelerated_orbit_compose, h_eq, hk']⟩
```

**Proof status: preparatory.** `accelerated_orbit_compose` induction
step is marked `sorry` as a placeholder — PR #56 (orbit foundation)
will close it via straightforward induction on `k`. `OrbitLeafReachesOne`
and `orbit_predecessor_reaches_one` will be defined and proved in the
same PR #56, along with executable compile-checked scenarios. Per
Codex run-21858 resolution ("the right execution order is: orbit
foundation + compile-checked iterate-composition and predecessor
scenarios → data type/certificate → orbit-semantic companion theorem
with BDD scenarios"), the foundation PR precedes the data-layer PR.

### Companion theorem: `coverage_tree_soundness_orbit_cert` — parallel orbit-routing theorem

```lean
/-- Bounded-orbit companion theorem for `FiniteOrbitClaim` shapes
    (`.empty`, `.singleton n`, `.bounded K`) — **parallel** to (NOT a
    refinement of) `coverage_tree_soundness_full` / `coverage_tree_soundness_cert`.

    Certifies the **orbit-aware routing relation** (`descendOrbit t x 0`)
    rather than the residue-only routing relation (`descend t x`).
    Concludes `OrbitLeafReachesOne t l` (NEW Q4 v3 predicate defined
    above), defined over `descendOrbit`, NOT `LeafReachesOne t l`
    (defined over `descend`).

    Per Codex run-21848 P1: the previous v2 spec concluded `LeafReachesOne
    t l` while constructing a proof over `descendOrbit`; the kernel
    rejected this because `descend t x = some l` and
    `descendOrbit t x 0 = some l` are different routing relations.
    v3 introduces `OrbitLeafReachesOne` so the conclusion type matches
    the routing evidence used in the proof.

    Proof sketch:
      1. `descend_orbit_complete` provides orbit-aware routing with
         `OrbitRoute` witness.
      2. `cert.orbit_hits_claim` lifts the routing to an orbit-state
         claim (`∃ k, claim.Holds (accelerated_orbit x' k)`).
      3. `cert.claim_reaches_one` derives `ReachesOne (accelerated_orbit
         x' k)` (orbit state reaches 1).
      4. `orbit_predecessor_reaches_one` closes: original `x'` reaches
         1 via the orbit-predecessor closure lemma.

    **Q4 v3 scope:** the theorem is universally quantified over
    `FiniteOrbitClaim` shapes (`.empty` / `.singleton n` / `.bounded K`).
    For `.interval` claims, use `coverage_tree_soundness_cert` (Q3 v4)
    instead. The two theorems certify DIFFERENT routing relations and
    are PARALLEL, not refinements of each other.

    **Hypothesis-bearing.** The theorem does NOT prove any new global
    or per-leaf Collatz reachability result beyond what
    `BoundedOrbitCertificate t l` packages. The actual Collatz
    evidence comes from external sources (per-input finite trajectory
    checks, Python runtime oracles, etc.) supplied by the caller at
    certificate construction time.

    PR #58 does NOT establish any new global or per-leaf Collatz
    reachability result. -/
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
  -- hdesc' : descendOrbit t x' 0 = some l  ✓ matches cert.orbit_hits_claim's expected input
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x' hdesc'
  -- cert.claim_reaches_one (accelerated_orbit x' k) hk : ReachesOne (accelerated_orbit x' k)
  exact orbit_predecessor_reaches_one x' k (accelerated_orbit x' k) rfl
         (cert.claim_reaches_one _ hk)
```

The proof is a four-step composition: `descend_orbit_complete` provides
the orbit-aware routing + `OrbitRoute` witness; `cert.orbit_hits_claim`
lifts routing to an orbit-state claim (`∃ k, claim.Holds
(accelerated_orbit x' k)`); `cert.claim_reaches_one` derives
`ReachesOne (accelerated_orbit x' k)`; `orbit_predecessor_reaches_one`
closes via orbit-predecessor closure. The conclusion
`OrbitLeafReachesOne t l` matches the routing evidence — the v2
mismatch (concluding `LeafReachesOne t l` over `descendOrbit` routing) is
resolved.

### Per-shape proof obligations (Q4 v3)

| Claim | `claim.Holds (accelerated_orbit x k)` | `claim_reaches_one` provable? | Q4 v3 status |
|---|---|---|---|
| `.empty` | `False` | Vacuously (from `False` premise) | **Q4 v3 scope** — `orbit_hits_claim` is a genuine unreachable-leaf proof under `descendOrbit` (orbit-aware routing never selects this leaf); `claim_reaches_one` vacuous |
| `.singleton n` | `accelerated_orbit x k = n` | Hypothesis-bearing — needs `ReachesOne n` (single trajectory check, finite witness `k' : Nat`) | **Q4 v3 scope** — `orbit_hits_claim` identifies the orbit step `k` at which the input hits `n`; `claim_reaches_one` proves `ReachesOne n` (typically constructive via small trajectory) |
| `.bounded K` | `accelerated_orbit x k ≤ K` | Hypothesis-bearing — needs `∀ y ≤ K, ReachesOne y` (finite enumeration of `0..K`) | **Q4 v3 scope** — `orbit_hits_claim` identifies the orbit step `k` at which the input drops below `K` (orbit-image bound); `claim_reaches_one` proves `ReachesOne y` for each `y ≤ K` (finite enumeration) |
| `.interval period lo hi` | (NOT applicable — `.interval` is structurally routed, not orbit-routed) | N/A | **OUT OF Q4 v3 scope** — handled by Q3 v4 `LeafCertificate` + `coverage_tree_soundness_cert` (residue-only routing). `FiniteOrbitClaim` does not include `.interval` by construction. |

**Key Q4 v3 design choice**: every obligation field is hypothesis-bearing.
The bounded-orbit workstream provides **typed packaging** for finite
claims, not **constructive proof** that any finite claim is inhabited.
This is consistent with the Q3 v3 spec's hypothesis-bearing approach
and with the project's "no new `sorry`" discipline (PR #51 P1): the
kernel verifies consistency, not convergence.

### Companion executable spec + API-shape regression

Following the Q3 v3 pattern (PR #51 P1: explicit-parameter regression
example, no `by sorry` default), Q4 v3 adds:

```lean
/-- Scenario N (Q4 PR #58): compile-checked regression example for
    `coverage_tree_soundness_orbit_cert` with a concrete `depthTwoTree`
    + indexed `BoundedOrbitCertificate depthTwoTree l` certificates.
    The `hCert` parameter is **explicit** (no default) — preserves
    the project's "no new sorry" discipline. The per-leaf certificate
    construction (i.e., the actual proofs of `orbit_hits_claim` and
    `claim_reaches_one`) is supplied externally by the test author
    (hypothesis-bearing; finite trajectory witnesses).

    Note (Q4 v3): the conclusion uses `OrbitLeafReachesOne depthTwoTree l`,
    NOT `LeafReachesOne depthTwoTree l` — the v2 spec incorrectly used
    `LeafReachesOne` here, which would not elaborate. See the API-shape
    regression below. -/
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             BoundedOrbitCertificate depthTwoTree l) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree 5 0 = some l ∧
         OrbitLeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_orbit_cert depthTwoTree hv hc hCert 5 (by norm_num)

/-- API-shape regression (Q4 v3 — addresses Codex run-21858 P2):
    prevent conflating the two distinct leaf-level semantic predicates.

    `applyResidueReaches` accepts `LeafReachesOne` (defined over the
    residue-only router `descend`); its routing-hyp parameter has type
    `descend t x = some l`.

    `applyOrbitReaches` accepts `OrbitLeafReachesOne` (defined over
    the orbit-aware router `descendOrbit`); its routing-hyp parameter
    has type `descendOrbit t x 0 = some l`.

    The two functions require **strictly different routing-hypothesis
    types**. Passing the wrong hypothesis at a call site will surface a
    Lean type error. This is the executable-spec-layer guard against
    the v2 routing-relation mismatch. -/
def applyResidueReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : LeafReachesOne t l) (x : Nat) (hdesc : descend t x = some l) :
    ReachesOne x :=
  h x hdesc

def applyOrbitReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : OrbitLeafReachesOne t l) (x : Nat) (hdesc : descendOrbit t x 0 = some l) :
    ReachesOne x :=
  h x hdesc
```

## Dependencies (in master vs pending)

| Dependency | Status | Used for |
|---|---|---|
| `descend_orbit_complete` (PR #29 at `4a67591`) | ✅ In master | Orbit-aware routing (`descendOrbit t x 0 = some l`); used in `coverage_tree_soundness_orbit_cert` proof |
| `OrbitRoute` witness (PR #29) | ✅ In master | Threaded through `descend_orbit_complete` proof (not directly used in Q4 v3 theorem body) |
| `acceleratedStep_odd_of_odd` (PR #31) | ✅ In master | Orbit bridge — oddness preservation; available for downstream certificate construction |
| `standardStep_positive` (PR #37) | ✅ In master | Orbit bridge — positivity preservation |
| `acceleratedStep_positive_of_odd` (PR #38) | ✅ In master | Orbit bridge — positivity preservation (accelerated) |
| `acceleratedStep_equiv_standardStep` (PR #46) | ✅ In master | Orbit bridge — accelerated ≡ standard step composition |
| `acceleratedTrajectory_reaches_one_implies_standard` (PR #47) | ✅ In master | Orbit bridge — reachability bridge |
| `coverage_tree_soundness_orbit` (PR #36 spec) | ❌ Pending (`sorry` in master) | **NOT NEEDED for Q4 v3** — analyzed below |
| `LeafClaim` data type (PR #53) | ✅ In master | Source for `IsFiniteClaim : LeafClaim → Prop` predicate; `FiniteOrbitClaim`'s three constructors mirror `LeafClaim`'s finite constructors |
| `LeafCertificate t l` Type-valued structure (PR #54) | ✅ In master | Parallel sibling certificate; Q4 v3 is the orbit-aware counterpart — no mutual exclusion |
| `coverage_tree_soundness_cert` companion theorem (PR #54) | ✅ In master | Parallel sibling theorem; Q4 v3 is the orbit-aware counterpart — different routing relation, different conclusion |
| **`OrbitLeafReachesOne t l` predicate** (Q4 v3 NEW, PR #56 deliverable) | ❌ To add | Orbit-routing leaf-level semantic predicate (parallel to `LeafReachesOne`); concluded by the new companion theorem |
| **`accelerated_orbit_compose`** (Q4 v3 NEW, PR #56 deliverable) | ❌ To prove | Orbit-additive composition lemma; foundation for `orbit_predecessor_reaches_one` |
| **`orbit_predecessor_reaches_one`** (Q4 v3 NEW, PR #56 deliverable) | ❌ To prove | Orbit-predecessor closure lemma; the actual Q4 mechanism |

**Analysis: does Q4 v3 need `coverage_tree_soundness_orbit` (PR #36 spec,
`sorry` pending)?**

Q4 v3 does NOT depend on `coverage_tree_soundness_orbit` (confirmed by
Codex review on PR #55 at run 21843 — "Resolved design questions":
"Q4 does not depend on coverage_tree_soundness_orbit; SatOrbit and the
required orbit-hit relation are distinct"). The two workstreams are
independent — `SatOrbit` (from `coverage_tree_soundness_orbit`) and the
Q4 v3 `OrbitLeafReachesOne` predicate address different routing
relations. The Q3 v3 spec listing of `coverage_tree_soundness_orbit`
as a dependency was corrected in Q4 v1; v3 retains this correction.

**Implication**: the bounded-orbit workstream can proceed in parallel
with the `coverage_tree_soundness_orbit` sorry closure. Neither blocks
the other.

## Implementation plan (Q4 v3 — foundation split)

Per Codex run-21858 resolution: "the right execution order is: orbit
foundation + compile-checked iterate-composition and predecessor
scenarios → data type/certificate → orbit-semantic companion theorem
with BDD scenarios." The orbit foundation PR precedes the data-layer
PR (different risk profiles, independent test requirements).

| PR | Scope | Lean CI | Depends on |
|---|---|---|---|
| **#55** (THIS DOC) | Q4 v3 spec — `OrbitLeafReachesOne` predicate + drop `wellFormed`/`IsFinite` + re-scope as parallel orbit-routing theorem + API-shape regression | No | — |
| **#56** | Q4 orbit foundation — `OrbitLeafReachesOne` predicate + `accelerated_orbit_compose` (close the placeholder `sorry`) + `orbit_predecessor_reaches_one` + compile-checked iterate-composition and predecessor scenarios | Yes | PR #55 (spec) |
| **#57** | Q4 data layer — `FiniteOrbitClaim` type + `IsFiniteClaim : LeafClaim → Prop` predicate (decidability) + `BoundedOrbitCertificate t l` structure (no `wellFormed` field) | Yes | PR #56 (orbit foundation) |
| **#58** | Q4 companion theorem + BDD — `coverage_tree_soundness_orbit_cert` theorem + executable spec scenario (uses `OrbitLeafReachesOne`) + API-shape regression `applyResidueReaches` + `applyOrbitReaches` | Yes | PR #57 (data layer) |
| **#59** | Q4 lessons-learned doc (if notable patterns emerge from PRs #55–58) | No | PR #58 |

**Future workstream (separate, NOT in Q4 v3):** constructive
construction of `BoundedOrbitCertificate t l` from external sources
(Python runtime oracles, finite trajectory checks). Would require a
Python↔Lean translation layer; deferred to Q5 or later.

## Out of scope (Q4 v3)

1. **Actual Collatz convergence.** Q4 v3 makes the dependency explicit
   but does not prove the Collatz theorem for any non-trivial interval.
2. **`coverage_tree_soundness_orbit`** (the `sorry` from PR #36).
   Separate orbit-aware soundness workstream; Q4 v3 is independent of
   it (analyzed above).
3. **Certificate.lean parser sorries** (lines 198, 199, 202).
   Pre-existing over-budget condition, separate audit pass.
4. **Affine.lean sorries.** Story 04b workstream.
5. **Python oracle bridge.** Promoting
   `tests/test_coverage_tree.py` trajectory checks to formal Lean
   certificates is a separate Q5+ workstream.
6. **Composite certificates** (`union`, `inter`,
   `tree_of_certificates`). Deferred to Q4 follow-ups if needed.
7. **Replacing `leafProperty : String`.** Deferred to a future
   version after the certificate type stabilises.

## Codex review questions (v3)

1. **`OrbitLeafReachesOne` as a sibling to `LeafReachesOne`.** v3
   introduces `OrbitLeafReachesOne t l := ∀ x, descendOrbit t x 0 = some l →
   ReachesOne x` as a parallel predicate (rather than overloading
   `LeafReachesOne` or introducing a generalized `LeafReaches` indexed by
   a routing relation). Is the parallel-predicate approach the right
   call, or would a generalized `LeafReaches` (parameterized over a
   `Nat → Option CoverageLeaf` routing function) be cleaner?
2. **`OrbitLeafReachesOne` placement in PR #56 (orbit foundation).**
   v3 places `OrbitLeafReachesOne` in the foundation PR along with
   `accelerated_orbit_compose` and `orbit_predecessor_reaches_one`,
   keeping all orbit-routing primitives together. Is the foundation
   PR scope right, or should `OrbitLeafReachesOne` (being the
   conclusion shape of the companion theorem) move to PR #58
   (companion theorem)?
3. **PR sequencing: 4 implementation PRs (#56-#59) instead of 2.** v3
   splits foundation from data and data from theorem per Codex
   run-21858 "right execution order". Is this sequencing right, or
   should some PRs be combined (e.g., #56 foundation + #57 data into
   a single data-and-foundation PR)?
4. **`accelerated_orbit_compose` proof shape.** The v3 spec still
   marks the `succ` induction step as `sorry` (placeholder) for the
   foundation PR (#56). Is the sketch sufficient, or should the spec
   carry a more complete proof sketch (with explicit `rw [accelerated_orbit]`
   / `simp` calls)?
5. **API-shape regression coverage.** The v3 spec adds
   `applyResidueReaches` + `applyOrbitReaches` as parallel `def`s
   with strictly different routing-hyp types. Is this regression
   strong enough, or does it need additional coverage (e.g., a
   negative-type example that fails to compile)?
6. **`IsFiniteClaim : LeafClaim → Prop` kept alongside `FiniteOrbitClaim`.**
   v3 keeps `IsFiniteClaim` (predicate on `LeafClaim`) for external
   code discrimination, while using `FiniteOrbitClaim` (new type) as
   the certificate's claim field. Is this dual-mechanism justified,
   or should one be dropped in favor of the other?

## References

- **Q3 v3 spec** (PR #52): [`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md) — design source; the "Future workstream: bounded-orbit certificates" subsection (lines 359–388) is the v1 sketch that v3 formalizes
- **Q3 v4 implementation** (PR #54, merge commit `c2f3d5b`): `LeafCertificate t l` Type-valued proof-carrying data bundle + `coverage_tree_soundness_cert` companion theorem. The Q4 v3 sibling — `BoundedOrbitCertificate` for finite claims under orbit-aware routing + `coverage_tree_soundness_orbit_cert` companion theorem
- **Codex reviews on PR #55**: run 21843 (2026-08-22T14:59:50Z, v1 → v2 fix), run 21848 (2026-08-22T15:09:09Z, v2 → v3 routing mismatch flag), run 21858 (2026-08-22T15:42:40Z, v2.1 → v3 final fix)
- **07c-2 promotion** (PR #49, merge commit `29c41e0`): [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) — original `LeafReachesOne` predicate + `coverage_tree_soundness_full` companion theorem; Q4 v3 introduces `OrbitLeafReachesOne` + `coverage_tree_soundness_orbit_cert` as a **parallel** orbit-routing pair (not a refinement)
- **07c-4 structural induction** (PR #29, merge commit `4a67591`): [`docs/story-07c-4-structural-induction.md`](story-07c-4-structural-induction.md) — `descend_orbit_complete` + `OrbitRoute` witness; Q4 v3 depends on this for orbit-aware routing
- **02c/03c closed lemmas** (PRs #31, #37, #38, #46, #47): orbit bridges available for downstream Q4 v3 certificate construction
- **Spec parent**: [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) Q3 (lines 75–104)
- **Theorem status**: [`docs/theorem-status.md`](theorem-status.md) — rows for `LeafCertificate`, `coverage_tree_soundness_cert`, `descend_orbit_complete` are upstream prerequisites for Q4 v3
- **Closed prerequisites** (orbit bridges): PRs #31, #37, #38, #46, #47 (02c/03c)
- **Lean validation gate**: GitHub Lean CI on each PR (per project discipline; no local `lake` commands)

## Implementation log

- `eaae6e8` — Q4 v1 spec (initial draft, PR #55) — REJECTED by Codex P1×2 + P1 + P2 at run 21843
- `a24e914` — Q4 v2 spec (revision per Codex run-21843): redesign around `orbit_hits_claim`, drop `K`/`orbit_image_bound`, add `accelerated_orbit_compose` + `orbit_predecessor_reaches_one` foundation lemmas to plan, remove Q3/Q4 mutual exclusion. Codex run-21848 flagged the routing-relation mismatch at the theorem conclusion (unresolved at this head)
- `62932fc` — Q4 v2.1 spec (proactive amendment): align `wellFormed : claim.IsFinite` with Codex sketch; drop YAGNI `toLeafClaim` lifting. **Self-evaluation failure**: run-21848 P1 routing mismatch NOT addressed; tautological `IsFinite` introduced. Codex run-21858 re-rejected
- (this commit) — Q4 v3 spec (final revision per Codex runs 21848 + 21858): introduce `OrbitLeafReachesOne` predicate (parallel to `LeafReachesOne`, defined over `descendOrbit`), fix routing-relation mismatch in the theorem conclusion; drop `wellFormed` field + `IsFinite` predicate per run-21858 P2; re-scope companion theorem prose as a **parallel orbit-routing theorem** (not a refinement of `coverage_tree_soundness_full` / `coverage_tree_soundness_cert`); add API-shape regression `applyResidueReaches` + `applyOrbitReaches` with strictly different routing-hyp types; split implementation into 4 PRs (#56 foundation, #57 data, #58 theorem, #59 lessons) per run-21858 "right execution order"
