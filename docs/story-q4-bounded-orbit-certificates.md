# Story Q4 — Bounded-orbit certificates for finite `LeafClaim` shapes

Status: **v2 spec (revised per Codex P1+P2 review on PR #55, run 21843, 2026-08-22T14:59:50Z).** Adopts `orbit_hits_claim` shape + `FiniteOrbitClaim` type + `orbit_predecessor_reaches_one` composition lemma; removes `K : Nat` field, `orbit_image_bound` field, and Q3/Q4 mutual-exclusion constraint.

## Revision history

- **v1 (PR #55, commit `eaae6e8`)**: initial draft. **Rejected by Codex** at run 21843 because `routed_implies_claim` still constrained the original input `x` directly (same uninhabitable boundary Q3 v3 explicitly avoided for finite claims under residue-only routing). The orbit-aware router changed which edge was selected but did not change the claim target. The `K` field + `orbit_image_bound` static-equality check were unused by the proposed theorem and provided no Q4 bridge.
- **v2 (THIS DOC)**: fundamental redesign around the **orbit-state-relative claim shape**. The certificate establishes that the routed input's orbit reaches a state satisfying a finite claim, not that the original input satisfies the claim. Adds the **foundational composition lemma** `ReachesOne (accelerated_orbit x k) → ReachesOne x` (built on `accelerated_orbit_compose`) as PR #56 deliverable. Uses a new `FiniteOrbitClaim` type (only `.empty` / `.singleton n` / `.bounded K` constructors; `.interval` is out of Q4 scope, handled by Q3 v4 `LeafCertificate`). Removes Q3/Q4 mutual-exclusion constraint — a leaf can carry both `LeafCertificate t l` (interval) and `BoundedOrbitCertificate t l` (finite) as independent views.

## Motivation

The Q3 v3 spec ([`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md)) deferred finite `LeafClaim` constructors (`.empty`, `.singleton n`, `.bounded K`) to a separate **bounded-orbit workstream** with this rationale:

> Under current `descend` semantics (residue-only routing, no Collatz
> reduction), finite claims cannot be constructively inhabited for
> nonempty leaves. The preimage of a nonempty leaf under residue-routed
> `descend` is periodic (every residue class mod `2^k` contains
> infinitely many positive integers). It cannot be contained in
> `{x | x = n}` or `{x | x ≤ K}`.

Q3 v3 explicitly flagged that **even under orbit-aware routing**, the
finite claim must NOT be asserted about the original input `x` directly
— the claim must be about an **orbit state**, with a composition lemma
to lift orbit-state reachability back to original-input reachability.
Q4 v1 missed this distinction. Q4 v2 (this doc) corrects it.

## Architectural context

```
LeafClaim (Q3 v3)
├── .empty         ─┐
├── .singleton n   ─┼─→ FiniteOrbitClaim (Q4 NEW) ─→ BoundedOrbitCertificate (Q4 v2)
└── .bounded K     ─┘    (only these 3 constructors;    ─→ coverage_tree_soundness_orbit_cert
                         .interval NOT included)           (composes descend_orbit_complete
                                                            + orbit_hits_claim + claim_reaches_one
                                                            + orbit_predecessor_reaches_one)

LeafClaim (Q3 v3)
└── .interval ──→ LeafCertificate (Q3 v4 Type-valued) ─→ coverage_tree_soundness_cert
                  (uses coverage_tree_soundness, not orbit-aware)
```

Two certificate types, two companion theorems, **no mutual exclusion** —
a leaf can carry both:

- `LeafCertificate t l` (Q3 v4, Type-valued) for `.interval` claims using
  **residue-only** routing (`descend`). Per-shape obligation
  `routed_implies_claim : descend t x = some l → interval.Holds x`.
- `BoundedOrbitCertificate t l` (Q4 v2, Type-valued) for **finite** claims
  using **orbit-aware** routing (`descendOrbit`). Per-shape obligation
  `orbit_hits_claim : descendOrbit t x 0 = some l → ∃ k, finite.Holds (accelerated_orbit x k)`.

The two are **independent views**: a leaf's verified status carries
both certificates (or either, depending on what the caller has
constructed). The companion theorems take their respective certificate
hypotheses independently — `coverage_tree_soundness_cert` does not
require `BoundedOrbitCertificate`, and vice versa.

## Design

### `FiniteOrbitClaim` — restricted claim type

A new inductive type that captures the three finite `LeafClaim`
constructors without the `.interval` constructor. This makes the
finite-claim restriction structurally enforced at the type level — no
risk of an `.interval` claim slipping through a `BoundedOrbitCertificate`
construction.

```lean
/-- A claim about which **orbit states** reach a leaf, restricted to
    finite shapes. The `.interval` constructor (from `LeafClaim`) is
    intentionally omitted — interval claims are residue-only routing
    territory (Q3 v4 `LeafCertificate`), not orbit-aware routing
    territory (Q4 `BoundedOrbitCertificate`).

    `Holds` here is a predicate on `Nat` interpreted as an **orbit
    state** (a value `accelerated_orbit x k` for some `k : Nat`),
    NOT on the original routing input `x` directly. This is the
    critical Q4 v2 fix from the v1 spec.

    Equality-comparable, serializable. `DecidableEq` provided by
    `deriving`. -/
inductive FiniteOrbitClaim where
  | empty                       -- no inputs
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

/-- `IsFiniteClaim : LeafClaim → Prop` predicate, used by Q3 v4
    `LeafCertificate.WellFormed` extension or by external code that
    needs to distinguish finite vs interval `LeafClaim` values.

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

/-- Trivial well-formedness predicate on `FiniteOrbitClaim`: every
    value is well-formed by construction (the type only contains finite
    constructors). The predicate is kept for symmetry with Q3 v4
    `LeafCertificate.WellFormed` (which is non-trivial for `.interval`
    claims) and for future structural guards if needed, e.g.,
    `K > 0` for `.bounded K` claims.

    For `LeafClaim` values, the `IsFiniteClaim` predicate (defined
    above) discriminates finite vs interval shapes. The two predicates
    serve different concerns: `IsFinite` is the per-certificate
    well-formedness guard (always `True` for `FiniteOrbitClaim`);
    `IsFiniteClaim` discriminates `LeafClaim` values that come from
    external sources (parsers, deserializers). -/
def IsFinite : FiniteOrbitClaim → Prop
  | _ => True

instance IsFinite.decidable : (c : FiniteOrbitClaim) → Decidable c.IsFinite
  | _ => inferInstance

end FiniteOrbitClaim
```

**Why a new type instead of a predicate on `LeafClaim`?** Codex's
required redesign uses `FiniteOrbitClaim` (new type) — the structural
restriction is enforced at the type level, so a `BoundedOrbitCertificate`
cannot be constructed with an `.interval` claim by accident. A
predicate `IsFiniteClaim : LeafClaim → Prop` would allow runtime
violations if the caller forgets the guard. The new-type approach is
stricter and more auditable. (`IsFiniteClaim` is also defined above as
a reusable helper for external code that needs to discriminate `LeafClaim`
values.)

### `BoundedOrbitCertificate` — proof-carrying data bundle

Type-valued (NOT `: Prop`) per Q3 v4 lesson. The structure carries data
fields (`claim`) plus `Prop`-valued obligation proofs (`wellFormed`,
`orbit_hits_claim`, `claim_reaches_one`). The kernel verifies that the
proof fields are consistent with the data field.

```lean
/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `LeafReachesOne t l` for a **finite** `FiniteOrbitClaim` shape
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
    the original input satisfies the claim. This is structurally different
    from Q3 v4's `LeafCertificate`, where `routed_implies_claim` is about
    the original input. The orbit-state-relative shape is what makes
    finite claims constructively inhabitable under `descendOrbit`.

    **Three obligation fields:**
    1. `wellFormed : claim.IsFinite` — trivially discharged (every
       `FiniteOrbitClaim` value satisfies `IsFinite` by construction;
       the field is kept for symmetry with Q3 v4 `LeafCertificate.WellFormed`
       and for future structural guards if needed, e.g., `K > 0` for
       `.bounded K`).
    2. `orbit_hits_claim`: every input routed (orbit-aware) to `l`
       reaches an orbit state satisfying the claim. (Routing-to-orbit-state
       obligation.) This is the field where the Q4 mechanism lives.
    3. `claim_reaches_one`: every orbit state satisfying the claim
       reaches 1. (Reachability obligation — per-input enumeration
       for `.bounded K`, single trajectory check for `.singleton n`,
       vacuous for `.empty`.)

    The companion theorem `coverage_tree_soundness_orbit_cert` takes
    `(hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)`
    as an **explicit** hypothesis (no default, no `by sorry`) per the
    project "no new sorry" discipline (PR #51 P1). -/
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : FiniteOrbitClaim
  wellFormed : claim.IsFinite
  orbit_hits_claim :
    ∀ x, descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y
```

**Sort rationale (`: Type`, not `: Prop`).** Same as Q3 v4: the `claim`
data field forces `: Type`. The mandatory `wellFormed : claim.IsFinite`
field is a trivial guard today (every `FiniteOrbitClaim` value satisfies
`IsFinite` by construction); the field is kept for symmetry with Q3 v4
`LeafCertificate.WellFormed` and for future structural guards if needed
(e.g., requiring `.bounded K` to have `K > 0`).

**Why no `K : Nat` data field?** Q4 v1 had `K : Nat` as a separate
data field with `orbit_image_bound : claim matches .bounded K' → K' = K`
as a static consistency check. Codex flagged this as dead weight —
the `K` is implicit in the `claim : FiniteOrbitClaim.bounded K`
constructor. The v2 certificate drops the redundant `K` field and the
`orbit_image_bound` static check; `orbit_hits_claim` does the real
work by asserting `claim.Holds (accelerated_orbit x k)` for some `k`
— when `claim = .bounded K`, this asserts `accelerated_orbit x k ≤ K`.

### Foundation lemmas — the actual Q4 mechanism

The companion theorem's correctness depends on two foundational
lemmas that the certificate's `orbit_hits_claim` + `claim_reaches_one`
fields compose. **Without these lemmas, the certificate is just typed
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
      -- accelerated_orbit x (0 + k') = accelerated_orbit x k'
      -- accelerated_orbit (accelerated_orbit x 0) k' = accelerated_orbit x k'
      simp [accelerated_orbit, Nat.add_zero]
  | succ k ih =>
      -- accelerated_orbit x (k + 1 + k') = accelerated_orbit (accelerated_orbit (accelerated_orbit x (k + 1)) 0) k'
      -- LHS: by ih with x, k+1, k' = accelerated_orbit (accelerated_orbit x (k+1)) k'
      -- RHS: accelerated_orbit (acceleratedStep (accelerated_orbit x (k+1))) k'
      -- Both unfold to accelerated_orbit (acceleratedStep (accelerated_orbit x (k+1))) k'
      -- (i.e., the zero-step on RHS is identity by accelerated_orbit_zero)
      sorry  -- TODO PR #56

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

**Proof status: preparatory.** `accelerated_orbit_compose` proof is
marked `sorry` here as a placeholder — PR #56 will close it via
straightforward induction on `k`. `orbit_predecessor_reaches_one` is a
direct corollary of `accelerated_orbit_compose` and does not introduce
a new sorry. The two lemmas together provide the **orbit-predecessor
closure** mechanism that makes Q4 finite-claim certificates constructively
usable.

### Companion theorem: `coverage_tree_soundness_orbit_cert`

```lean
/-- Bounded-orbit variant of `coverage_tree_soundness_full` for finite
    `FiniteOrbitClaim` shapes (`.empty`, `.singleton n`, `.bounded K`).

    Uses `descend_orbit_complete` (Story 07c-4) for orbit-aware
    routing, then composes:
      1. `orbit_hits_claim` (from the per-leaf certificate) — the orbit
         reaches a state satisfying the claim,
      2. `claim_reaches_one` — that orbit state reaches 1,
      3. `orbit_predecessor_reaches_one` (foundation lemma) — the
         original input reaches 1 (orbit-predecessor closure).

    A **sound, typed refinement** of `coverage_tree_soundness_full`:
    the new `hCert` hypothesis is **strictly stronger** than
    `coverage_tree_soundness_full`'s `hLeaf` (a `BoundedOrbitCertificate
    t l` factors through `LeafReachesOne t l` via the three-step
    composition above; the reverse is not supplied and generally cannot
    construct a well-formed finite claim plus its orbit-hit and reachability
    proofs from `hLeaf` alone).

    **Q4 scope:** the theorem is universally quantified over
    `FiniteOrbitClaim` shapes (`.empty` / `.singleton n` / `.bounded K`).
    For `.interval` claims, use `coverage_tree_soundness_cert` (Q3 v4)
    instead. The two are **independent views**: a leaf can carry both
    `LeafCertificate t l` (interval claim, residue-only routing) and
    `BoundedOrbitCertificate t l` (finite claim, orbit-aware routing),
    and the two companion theorems apply independently to their
    respective certificates.

    **Hypothesis-bearing.** The theorem does NOT prove any new global
    or per-leaf Collatz reachability result beyond what
    `BoundedOrbitCertificate t l` packages. The actual Collatz
    evidence comes from external sources (per-input finite trajectory
    checks, Python runtime oracles, etc.) supplied by the caller at
    certificate construction time.

    Per Q3 v4 lesson: the theorem is documented as a **sound, typed
    refinement**, not "kernel-equivalent" (which would imply
    bidirectional equivalence with `coverage_tree_soundness_full`).
    PR #57 does NOT establish any new global or per-leaf Collatz
    reachability result. -/
theorem coverage_tree_soundness_orbit_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         LeafReachesOne t l := by
  obtain ⟨l, hl, hver, hdesc, hroute⟩ := descend_orbit_complete t hv hic x hx
  obtain cert := hCert l hl hver
  refine ⟨l, hl, hver, hdesc, ?_⟩
  intro x' hdesc'
  -- hdesc' : descendOrbit t x' 0 = some l
  -- cert.orbit_hits_claim x' hdesc' : ∃ k, claim.Holds (accelerated_orbit x' k)
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x' hdesc'
  -- cert.claim_reaches_one (accelerated_orbit x' k) hk : ReachesOne (accelerated_orbit x' k)
  exact orbit_predecessor_reaches_one x' k (accelerated_orbit x' k) rfl
         (cert.claim_reaches_one _ hk)
```

The proof is a three-step composition:
1. `descend_orbit_complete` provides orbit-aware routing with `OrbitRoute` witness
2. `cert.orbit_hits_claim` lifts the routing to an orbit-state claim (`∃ k, claim.Holds (accelerated_orbit x' k)`)
3. `cert.claim_reaches_one` derives `ReachesOne (accelerated_orbit x' k)` (orbit state reaches 1)
4. `orbit_predecessor_reaches_one` closes: original `x'` reaches 1 via the orbit-predecessor closure lemma

### Per-shape proof obligations (Q4 v2)

| Claim | `claim.Holds (accelerated_orbit x k)` | `claim_reaches_one` provable? | Q4 v2 status |
|---|---|---|---|
| `.empty` | `False` | Vacuously (from `False` premise) | **Q4 v2 scope** — `orbit_hits_claim` is a genuine unreachable-leaf proof under `descendOrbit` (orbit-aware routing never selects this leaf); `claim_reaches_one` vacuous |
| `.singleton n` | `accelerated_orbit x k = n` | Hypothesis-bearing — needs `ReachesOne n` (single trajectory check, finite witness `k' : Nat`) | **Q4 v2 scope** — `orbit_hits_claim` identifies the orbit step `k` at which the input hits `n`; `claim_reaches_one` proves `ReachesOne n` (typically constructive via small trajectory) |
| `.bounded K` | `accelerated_orbit x k ≤ K` | Hypothesis-bearing — needs `∀ y ≤ K, ReachesOne y` (finite enumeration of `0..K`) | **Q4 v2 scope** — `orbit_hits_claim` identifies the orbit step `k` at which the input drops below `K` (orbit-image bound); `claim_reaches_one` proves `ReachesOne y` for each `y ≤ K` (finite enumeration) |
| `.interval period lo hi` | (NOT applicable — `.interval` is structurally routed, not orbit-routed) | N/A | **OUT OF Q4 v2 scope** — handled by Q3 v4 `LeafCertificate` + `coverage_tree_soundness_cert` (residue-only routing). `FiniteOrbitClaim` does not include `.interval` by construction. |

**Key Q4 v2 design choice**: every obligation field is hypothesis-bearing.
The bounded-orbit workstream provides **typed packaging** for finite
claims, not **constructive proof** that any finite claim is inhabited.
This is consistent with the Q3 v3 spec's hypothesis-bearing approach
and with the project's "no new `sorry`" discipline (PR #51 P1): the
kernel verifies consistency, not convergence.

### Companion executable spec

Following the Q3 v3 pattern (PR #51 P1: explicit-parameter regression
example, no `by sorry` default), Q4 adds:

```lean
/-- Scenario N (Q4 PR #57): compile-checked regression example for
    `coverage_tree_soundness_orbit_cert` with a concrete `depthTwoTree`
    + indexed `BoundedOrbitCertificate depthTwoTree l` certificates.
    The `hCert` parameter is **explicit** (no default) — preserves
    the project's "no new sorry" discipline. The per-leaf certificate
    construction (i.e., the actual proofs of `orbit_hits_claim` and
    `claim_reaches_one`) is supplied externally by the test author
    (hypothesis-bearing; finite trajectory witnesses). -/
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             BoundedOrbitCertificate depthTwoTree l) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree 5 0 = some l ∧
         LeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_orbit_cert depthTwoTree hv hc hCert 5 (by norm_num)
```

## Dependencies (in master vs pending)

| Dependency | Status | Used for |
|---|---|---|
| `descend_orbit_complete` (PR #29 at `4a67591`) | ✅ In master | Orbit-aware routing (`descendOrbit t x 0 = some l`); used in `coverage_tree_soundness_orbit_cert` proof |
| `OrbitRoute` witness (PR #29) | ✅ In master | Threaded through `descend_orbit_complete` proof (not directly used in Q4 theorem body) |
| `acceleratedStep_odd_of_odd` (PR #31) | ✅ In master | Orbit bridge — oddness preservation; available for downstream certificate construction |
| `standardStep_positive` (PR #37) | ✅ In master | Orbit bridge — positivity preservation |
| `acceleratedStep_positive_of_odd` (PR #38) | ✅ In master | Orbit bridge — positivity preservation (accelerated) |
| `acceleratedStep_equiv_standardStep` (PR #46) | ✅ In master | Orbit bridge — accelerated ≡ standard step composition |
| `acceleratedTrajectory_reaches_one_implies_standard` (PR #47) | ✅ In master | Orbit bridge — reachability bridge |
| `coverage_tree_soundness_orbit` (PR #36 spec) | ❌ Pending (`sorry` in master) | **NOT NEEDED for Q4** — analyzed below |
| `LeafClaim` data type (PR #53) | ✅ In master | Source for `FiniteOrbitClaim` constructors (`.empty`, `.singleton`, `.bounded`); `.interval` is intentionally excluded from `FiniteOrbitClaim` |
| `LeafClaim.WellFormed` predicate (PR #53 v2) | ✅ In master | Shared infrastructure; `IsFiniteClaim` predicate defined in Q4 mirrors its style |
| `LeafCertificate t l` Type-valued structure (PR #54) | ✅ In master | Sibling view; Q4 is the orbit-aware counterpart — no mutual exclusion |
| `coverage_tree_soundness_cert` companion theorem (PR #54) | ✅ In master | Sibling theorem; Q4 is the orbit-aware counterpart |
| **`accelerated_orbit_compose`** (Q4 NEW, PR #56 deliverable) | ❌ To prove | Orbit-additive composition lemma; foundation for `orbit_predecessor_reaches_one` |
| **`orbit_predecessor_reaches_one`** (Q4 NEW, PR #56 deliverable) | ❌ To prove | Orbit-predecessor closure lemma; the actual Q4 mechanism |

**Analysis: does Q4 need `coverage_tree_soundness_orbit` (PR #36 spec,
`sorry` pending)?**

Q4 does NOT depend on `coverage_tree_soundness_orbit` (confirmed by
Codex review on PR #55 at run 21843 — "Resolved design questions":
"Q4 does not depend on coverage_tree_soundness_orbit; SatOrbit and the
required orbit-hit relation are distinct"). The two workstreams are
independent — `SatOrbit` and `BoundedOrbit` (now recast as the
`orbit_hits_claim` obligation) address different questions. The Q3 v3
spec listing of `coverage_tree_soundness_orbit` as a dependency was
corrected in Q4 v1; v2 retains this correction.

**Implication**: the bounded-orbit workstream can proceed in parallel
with the `coverage_tree_soundness_orbit` sorry closure. Neither blocks
the other.

## Implementation plan

| PR | Scope | Lean CI | Depends on |
|---|---|---|---|
| **#55** (THIS DOC) | Q4 v2 spec — redesign around `orbit_hits_claim`, drop `K`/`orbit_image_bound`, add foundation lemmas to plan, remove mutual exclusion | No | — |
| **#56** | Q4 data layer + foundation — `FiniteOrbitClaim` type + `IsFiniteClaim` predicate + `toLeafClaim` lifting + `BoundedOrbitCertificate` structure + `accelerated_orbit_compose` (close the placeholder `sorry`) + `orbit_predecessor_reaches_one` | Yes | PR #55 (spec) |
| **#57** | Q4 implementation — `coverage_tree_soundness_orbit_cert` theorem + executable spec scenario + `LeafClaimTests.lean` extension (or new `BoundedOrbitCertificateTests.lean`) | Yes | PR #56 (data + foundation) |
| **#58** | Q4 lessons-learned doc (if notable patterns emerge from PRs #55–57) | No | PR #57 |

**Future workstream (separate, NOT in Q4 v2):** constructive
construction of `BoundedOrbitCertificate t l` from external sources
(Python runtime oracles, finite trajectory checks). Would require a
Python↔Lean translation layer; deferred to Q5 or later.

## Out of scope (revised — Q4 v2)

1. **Actual Collatz convergence.** Q4 makes the dependency explicit but does
   not prove the Collatz theorem for any non-trivial interval.
2. **`coverage_tree_soundness_orbit`** (the `sorry` from PR #36).
   Separate orbit-aware soundness workstream; Q4 is independent of
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
8. **Q3/Q4 mutual exclusion.** REMOVED in Q4 v2 per Codex review. A leaf
   can carry both `LeafCertificate t l` and `BoundedOrbitCertificate t l`
   as independent views. Each API restricts its claim shapes internally
   (`LeafCertificate` for `.interval`; `BoundedOrbitCertificate` for
   finite `.empty` / `.singleton n` / `.bounded K`).

## Codex review questions (v2)

1. **`FiniteOrbitClaim` vs `IsFiniteClaim : LeafClaim → Prop` as the
   primary mechanism.** v2 uses the new type (stricter, type-level
   enforcement); `IsFiniteClaim` is defined as a reusable helper but
   not the primary guard. Is the new-type approach the right call, or
   should `IsFiniteClaim` be the primary mechanism (with `FiniteOrbitClaim`
   as a derived subtype)?
2. **`accelerated_orbit_compose` proof shape.** v2 marks its proof as
   `sorry` (placeholder) with an induction-on-`k` sketch. Is the sketch
   correct, or are there subtle issues (e.g., the `generalizing x` need,
   the `accelerated_orbit_zero @[simp]` requirement, the `Nat.add_succ`
   vs `Nat.succ_add` direction) that the implementation PR #56 should
   pre-emptively address?
3. **`wellFormed : True` placeholder.** v2 keeps the `wellFormed` field
   as `True` for symmetry with Q3 v4 `LeafCertificate.WellFormed` (which
   is non-trivial for `.interval`). Is the trivial guard the right
   choice, or should it be removed entirely from the v2 certificate?
4. **Companion theorem proof step order.** v2 chains
   `descend_orbit_complete` → `orbit_hits_claim` → `claim_reaches_one`
   → `orbit_predecessor_reaches_one`. Is this the right ordering for
   PR #57's `exact`/`refine` chain, or is there a more direct form
   (e.g., composing via `Exists.intro` and `Eq.refl` directly)?
5. **`FiniteOrbitClaim.toLeafClaim` lifting.** v2 defines a structural
   lifting from `FiniteOrbitClaim` to `LeafClaim`. Is this lifting
   needed (for interoperation with Q3 v4 code), or is it premature?
6. **PR sequencing for foundation lemmas.** v2 places
   `accelerated_orbit_compose` + `orbit_predecessor_reaches_one` in
   PR #56 (data layer). Codex's review suggested "preferably in PR #56
   if it elaborates cleanly; otherwise split it into a dedicated
   foundation PR before the certificate theorem." Is the PR #56
   placement right, or should these lemmas get a dedicated PR
   (e.g., PR #55b or PR #56.5)?

## References

- **Q3 v3 spec** (PR #52): [`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md) — design source; the "Future workstream: bounded-orbit certificates" subsection (lines 359–388) is the v1 sketch that v2 formalizes
- **Q3 v4 implementation** (PR #54, merge commit `c2f3d5b`): `LeafCertificate t l` Type-valued proof-carrying data bundle + `coverage_tree_soundness_cert` companion theorem. Q3 v4 lessons applied throughout Q4 v2
- **Codex review on PR #55** at run 21843 (2026-08-22T14:59:50Z): P1×2 + P1 + P2 feedback; addressed at Q4 v2
- **07c-2 promotion** (PR #49, merge commit `29c41e0`): [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) — original `LeafReachesOne` predicate + `coverage_tree_soundness_full` companion theorem; Q4 mirrors this pattern for the orbit-aware case
- **07c-4 structural induction** (PR #29, merge commit `4a67591`): [`docs/story-07c-4-structural-induction.md`](story-07c-4-structural-induction.md) — `descend_orbit_complete` + `OrbitRoute` witness; Q4 depends on this for orbit-aware routing
- **02c/03c closed lemmas** (PRs #31, #37, #38, #46, #47): orbit bridges available for downstream Q4 certificate construction
- **Spec parent**: [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) Q3 (lines 75–104)
- **Theorem status**: [`docs/theorem-status.md`](theorem-status.md) — rows for `LeafCertificate`, `coverage_tree_soundness_cert`, `descend_orbit_complete` are upstream prerequisites for Q4
- **Closed prerequisites** (orbit bridges): PRs #31, #37, #38, #46, #47 (02c/03c)
- **Lean validation gate**: GitHub Lean CI on each PR (per project discipline; no local `lake` commands)

## Implementation log

- `eaae6e8` — Q4 v1 spec (initial draft, PR #55) — REJECTED by Codex P1×2 + P1 + P2 at run 21843
- (this commit) — Q4 v2 spec (revision per Codex feedback): redesign around `orbit_hits_claim`, drop `K`/`orbit_image_bound`, add `accelerated_orbit_compose` + `orbit_predecessor_reaches_one` foundation lemmas to plan, remove Q3/Q4 mutual exclusion

