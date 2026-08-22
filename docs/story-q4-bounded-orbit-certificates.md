# Story Q4 — Bounded-orbit certificates for finite `LeafClaim` shapes

Status: **v1 spec (initial draft, PR #55).**

## Motivation

The Q3 v3 spec ([`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md)) deferred finite `LeafClaim` constructors (`.empty`, `.singleton n`, `.bounded K`) to a separate **bounded-orbit workstream** with this rationale:

> Under current `descend` semantics (residue-only routing, no Collatz
> reduction), finite claims cannot be constructively inhabited for
> nonempty leaves. The preimage of a nonempty leaf under residue-routed
> `descend` is periodic (every residue class mod `2^k` contains
> infinitely many positive integers). It cannot be contained in
> `{x | x = n}` or `{x | x ≤ K}`.

The Q3 v3 spec identified orbit-aware routing (`descendOrbit`) as the
natural substrate for finite claims — `descendOrbit` walks the tree
using orbit-aware residues (`accelerated_orbit x k % m`), which
exposes the Collatz-dynamics structure that residue-only `descend`
hides.

Q4 delivers the **bounded-orbit certificate infrastructure** for finite
`LeafClaim` shapes. The infrastructure is **infrastructure + typed
packaging** — the actual Collatz convergence evidence comes from
external sources (per-input finite trajectory checks, Python runtime
oracles, or future formal-derivation workstreams). The certificates
are **hypothesis-bearing**: each obligation field is a `Prop`-valued
proof that the caller supplies. The kernel still verifies that the
fields are consistent; it does not prove convergence.

## Scope

**In scope:**
- `BoundedOrbit x K : Prop` — orbit-image bound predicate
- `BoundedOrbitCertificate t l : Type` — proof-carrying data bundle
  indexed by tree AND leaf, with claim-shape-specific obligation fields
- Companion theorem `coverage_tree_soundness_orbit_cert` — composes
  `descend_orbit_complete` + per-leaf `BoundedOrbitCertificate t l` to
  derive `LeafReachesOne t l` (conditional, hypothesis-bearing)
- Per-shape proof obligation tables (`.empty`, `.singleton n`,
  `.bounded K`)
- Spec-level architectural review via Codex

**Out of scope (explicit):**
- **Actual Collatz convergence.** Q4 makes the dependency explicit but
  does NOT prove `ReachesOne x` for any non-trivial `x` not already
  known from external sources.
- **`coverage_tree_soundness_orbit` sorry** (PR #36 spec). The bounded-orbit
  workstream does NOT depend on it (see § "Dependencies" below); Q4
  produces a NEW companion theorem `coverage_tree_soundness_orbit_cert`
  that uses `descend_orbit_complete` directly, not via
  `coverage_tree_soundness_orbit`.
- **Certificate.lean parser sorries** (lines 198, 199, 202). Pre-existing,
  separate audit pass.
- **Affine.lean sorries.** Story 04b workstream, separate.
- **Python oracle integration.** Promoting `tests/test_coverage_tree.py`
  trajectory checks to formal Lean certificates is a separate workstream.
- **Composite certificates** (`union`, `inter`, `tree_of_certificates`).
  Deferred to Q4 follow-ups if needed.

## Architectural context

```
LeafClaim (Q3 v3)
├── .empty         ─┐
├── .singleton n   ─┼─→ BoundedOrbitCertificate (Q4 NEW) ─→ coverage_tree_soundness_orbit_cert
└── .bounded K     ─┘                                            (composes descend_orbit_complete)
    .interval (Q3 v3) ──→ LeafCertificate (Q3 v4 Type-valued)
                            ──→ coverage_tree_soundness_cert
                            (uses coverage_tree_soundness, not orbit-aware)
```

Two certificate types, two companion theorems:
- `LeafCertificate t l` (Q3 v4, Type-valued) for `.interval` claims
  using **residue-only** routing (`descend`). Per-shape obligation
  `routed_implies_claim : descend t x = some l → interval.Holds x`.
- `BoundedOrbitCertificate t l` (Q4, Type-valued) for **finite** claims
  using **orbit-aware** routing (`descendOrbit`). Per-shape obligation
  `routed_implies_claim : descendOrbit t x 0 = some l → finite.Holds x`.

The two are mutually exclusive at the call site: a leaf carries either
a `LeafCertificate t l` (interval claim) or a `BoundedOrbitCertificate
t l` (finite claim), not both. (Composite certificates are deferred.)

## Design

### `BoundedOrbit x K` — orbit-image bound

```lean
/-- Orbit-image bound: `x` reaches a value ≤ K within its accelerated
    orbit. This is the typed-quantitative bridge between
    `descendOrbit` routing (which exposes the orbit) and finite
    `LeafClaim` shapes (which bound the input domain).

    Provability note: `BoundedOrbit x K` is NOT decidable in general —
    for large `x` and small `K`, proving `∃ k, accelerated_orbit x k ≤ K`
    would amount to a Collatz convergence claim. The predicate is
    intended as **hypothesis-bearing evidence**, supplied by the caller
    from external sources (per-input finite trajectory checks, Python
    runtime oracles, etc.). The kernel verifies consistency but does
    not derive the bound from first principles. -/
def BoundedOrbit (x : Nat) (K : Nat) : Prop :=
  ∃ k, accelerated_orbit x k ≤ K
```

### `BoundedOrbitCertificate t l` — proof-carrying data bundle

Type-valued (NOT `: Prop`) per Q3 v4 lesson. The structure carries data
fields (`claim`, `K`) plus `Prop`-valued obligation proofs
(`routed_implies_claim`, `orbit_image_bound`, `claim_reaches_one`).
The kernel verifies that the proof fields are consistent with the
data fields.

```lean
/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `LeafReachesOne t l` for a **finite** `LeafClaim` shape
    (`.empty`, `.singleton n`, `.bounded K`).

    Declared as `: Type` (NOT `: Prop`) per Q3 v4 lesson: the
    `claim : LeafClaim` and `K : Nat` data fields require the
    structure to live in `Type` (Lean 4 elaboration rejects
    `Type`-valued fields in `Prop`-valued structures). The obligation
    fields are still `Prop`s, so the kernel still verifies them —
    only the structure's outer sort is `Type`. This makes
    `BoundedOrbitCertificate t l` a **proof-carrying data bundle**:
    inspectable data plus kernel-checked proof fields. It is NOT
    proof-irrelevant evidence and is intended to be constructed,
    pattern-matched on, and projected through.

    **Hypothesis-bearing nature.** Unlike `LeafCertificate` (Q3 v4),
    which uses residue-only routing, `BoundedOrbitCertificate` uses
    orbit-aware routing (`descendOrbit`). The obligation fields are
    *necessarily* hypothesis-bearing because their proof obligations
    would amount to Collatz convergence claims (see `BoundedOrbit`
    provability note above):

    1. `routed_implies_claim`: every input routed (orbit-aware) to
       `l` satisfies the claim. (Routing-to-claim obligation.)
    2. `orbit_image_bound`: every input routed to `l` has its orbit
       bounded by `K`. (Orbit-bridge obligation — needed for
       `.bounded K` claims; vacuous for `.empty` / `.singleton n`.)
    3. `claim_reaches_one`: every input satisfying the claim reaches
       1. (Reachability obligation — per-input enumeration.)

    `well_formed` enforces `LeafClaim.WellFormed` so that direct
    construction of malformed `.interval` claims (which are out of
    scope here) or `.bounded` claims with negative `K` (not
    representable in Nat) cannot slip through as purported certificates.

    The companion theorem `coverage_tree_soundness_orbit_cert` takes
    `(hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)`
    as an explicit hypothesis (no default, no `by sorry`) per the
    project "no new sorry" discipline (PR #51 P1). -/
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : LeafClaim
  K : Nat
  well_formed : claim.WellFormed ∧ (claim matches .bounded _ ∨ claim matches .singleton _ ∨ claim matches .empty)
  routed_implies_claim :
    ∀ x, descendOrbit t x 0 = some l → claim.Holds x
  orbit_image_bound :
    claim matches .bounded K' → K' = K  -- K matches the bound in .bounded K
  claim_reaches_one :
    ∀ x, claim.Holds x → ReachesOne x
```

**Sort rationale (`: Type`, not `: Prop`).** Same as Q3 v4: the `claim`
data field forces `: Type`. The `well_formed` conjunction is a
`Prop`-valued field that the kernel verifies. The mandatory `well_formed`
field prevents direct construction of `.interval` claims (which are out
of scope here) or `.bounded` claims with mismatched `K`.

**Per-shape obligation split.** The `well_formed` conjunction restricts
the certificate to finite claim shapes. The `orbit_image_bound` field
is only meaningful for `.bounded K` claims; for `.empty` /
`.singleton n`, the `K : Nat` field is unused (and the
`orbit_image_bound` proof is vacuously discharged by the `claim matches
.bounded K' → False` form, which is a TODO item in the v1 sketch —
see § "Per-shape proof obligations" below).

### Companion theorem: `coverage_tree_soundness_orbit_cert`

```lean
/-- Bounded-orbit variant of `coverage_tree_soundness_full` for finite
    `LeafClaim` shapes (`.empty`, `.singleton n`, `.bounded K`).

    Uses `descend_orbit_complete` (Story 07c-4) for orbit-aware
    routing, then composes the per-leaf `BoundedOrbitCertificate t l`
    obligations to derive `LeafReachesOne t l`.

    A **sound, typed refinement** of `coverage_tree_soundness_full`:
    the new `hCert` hypothesis is **strictly stronger** than
    `coverage_tree_soundness_full`'s `hLeaf` (a
    `BoundedOrbitCertificate t l` factors through `LeafReachesOne t l`
    via `claim_reaches_one ∘ routed_implies_claim`; the reverse is not
    supplied and generally cannot construct a well-formed claim plus
    its per-input orbit-image bound and reachability proof from
    `hLeaf` alone).

    **Q4 scope:** the theorem is universally quantified over finite
    `LeafClaim` shapes. For `.interval` claims, use
    `coverage_tree_soundness_cert` (Q3 v4) instead. The two are
    mutually exclusive at the call site: a leaf carries either a
    `LeafCertificate t l` (interval claim, residue-only routing) or a
    `BoundedOrbitCertificate t l` (finite claim, orbit-aware routing),
    not both.

    **Hypothesis-bearing.** The theorem does NOT prove any new global
    or per-leaf Collatz reachability result beyond what
    `BoundedOrbitCertificate t l` packages. The actual Collatz
    evidence comes from external sources (per-input finite trajectory
    checks, Python runtime oracles, etc.) supplied by the caller at
    certificate construction time.

    Per Q3 v4 lesson: the theorem is documented as a **sound, typed
    refinement**, not "kernel-equivalent" (which would imply
    bidirectional equivalence with `coverage_tree_soundness_full`).
    PR #55 does NOT establish any new global or per-leaf Collatz
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
  exact cert.claim_reaches_one x'
         (cert.routed_implies_claim x' hdesc')
```

The proof is a straightforward composition: `descend_orbit_complete`
provides the routing witness, then `routed_implies_claim` derives
`claim.Holds x'` from the routing, then `claim_reaches_one` derives
`ReachesOne x'`.

Note: `orbit_image_bound` is NOT used in the proof — it's a structural
constraint that prevents `.bounded K'` mismatches in the certificate
construction. Its presence in the structure ensures that
`.bounded K`-typed certificates carry a consistent `K` field that
external verifiers can audit.

### Per-shape proof obligations

| Claim | `claim.Holds` | `routed_implies_claim` provable? | `orbit_image_bound` meaningful? | `claim_reaches_one` provable? | Q4 status |
|---|---|---|---|---|---|
| `.empty` | `False` | Hypothesis-bearing — needs proof that no `x` is orbit-routed to `l` (genuine unreachable-leaf proof, even under `descendOrbit`) | No (`.empty` doesn't carry `K`) | Vacuously (from `False` premise) | **Q4 scope** — infrastructure provided; construction hypothesis-bearing |
| `.singleton n` | `x = n` | Hypothesis-bearing — needs proof that the only orbit-routed `x` is `n` | No (`.singleton` doesn't carry `K`) | Hypothesis-bearing — needs `ReachesOne n` (finite trajectory check) | **Q4 scope** — infrastructure provided; construction hypothesis-bearing |
| `.bounded K` | `x ≤ K` | Hypothesis-bearing — needs proof that every orbit-routed `x` is ≤ `K` (i.e., the leaf's residue interval is bounded by `K` under orbit-aware routing) | **Yes** — `orbit_image_bound` enforces `K` consistency | Hypothesis-bearing — needs `∀ x ≤ K, ReachesOne x` (finite enumeration of `0..K`) | **Q4 scope** — infrastructure provided; construction hypothesis-bearing |
| `.interval period lo hi` | `lo ≤ x % period ∧ x % period ≤ hi` | **NOT applicable** — `.interval` is structurally routed (residue-only), not orbit-routed. Use `LeafCertificate` (Q3 v4) instead. | No | N/A | **OUT OF Q4 scope** — handled by Q3 v4 / `LeafCertificate` |

**Key Q4 design choice**: every obligation field is hypothesis-bearing.
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
    construction (i.e., the actual proofs of `routed_implies_claim`,
    `orbit_image_bound`, `claim_reaches_one`) is supplied externally
    by the test author (hypothesis-bearing; finite trajectory
    witnesses). -/
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
| `LeafClaim` data type (PR #53) | ✅ In master | Shared infrastructure — Q4 reuses `.empty` / `.singleton` / `.bounded` constructors |
| `LeafClaim.WellFormed` predicate (PR #53 v2) | ✅ In master | `well_formed` field enforcement |
| `LeafCertificate t l` Type-valued structure (PR #54) | ✅ In master | Mutual-exclusion sibling; Q4 is the orbit-aware counterpart |

**Analysis: does Q4 need `coverage_tree_soundness_orbit` (PR #36 spec,
`sorry` pending)?**

`coverage_tree_soundness_orbit` proves
`descendOrbit t x 0 = some l → SatOrbit t x l` (orbit-aware routing
implies orbit-aware semantic content — the orbit reaches the leaf's
declared interval at some step `k`).

Q4 needs to prove `routed_implies_claim` for finite claims:
`descendOrbit t x 0 = some l → claim.Holds x` for `.empty` /
`.singleton n` / `.bounded K`. The relevant `Holds` predicate is
NOT `SatOrbit` — it's `x = n`, `False`, or `x ≤ K`. These bounds are
NOT derivable from `SatOrbit` (which only guarantees the orbit
reaches the leaf's interval at some step `k`, not that the input `x`
itself is bounded by `K`).

Therefore Q4 does NOT depend on `coverage_tree_soundness_orbit`. The
Q3 v3 spec listed it as a dependency, but on closer analysis, the two
workstreams are independent — `SatOrbit` and `BoundedOrbit` are
different predicates addressing different questions. The Q3 v3 spec
wording is corrected here in Q4 v1.

**Implication**: the bounded-orbit workstream can proceed in parallel
with the `coverage_tree_soundness_orbit` sorry closure. Neither blocks
the other.

## Implementation plan

| PR | Scope | Lean CI | Depends on |
|---|---|---|---|
| **#55** (THIS DOC) | Q4 v1 spec — design, dependencies, per-shape obligations, companion theorem | No | — |
| **#56** | Q4 data layer — `BoundedOrbit` predicate + `BoundedOrbitCertificate` structure + `DecidableEq` + `well_formed` machinery + `BoundedOrbitCertificate.decidable` for the structural fields | Yes | PR #55 (spec) |
| **#57** | Q4 implementation — `coverage_tree_soundness_orbit_cert` theorem + executable spec scenario + `LeafClaimTests.lean` extension | Yes | PR #56 (data layer) |
| **#58** | Q4 lessons-learned doc (if notable patterns emerge from PRs #55–57) | No | PR #57 |

**Future workstream (separate, NOT in Q4 v1):** constructive
construction of `BoundedOrbitCertificate t l` from external sources
(Python runtime oracles, finite trajectory checks). Would require a
Python↔Lean translation layer; deferred to Q5 or later.

## Per-shape proof obligation tables (revised — Q4 v1)

The Q3 v3 spec table at lines 290–296 listed "Future: bounded-orbit
workstream" for `.empty` / `.singleton n` / `.bounded K`. Q4 v1
sharpens these entries:

| Claim | Q3 v3 status | Q4 v1 status |
|---|---|---|
| `.empty` | Future: bounded-orbit workstream | **Q4 v1 scope** — infrastructure provided; `routed_implies_claim` is hypothesis-bearing (genuine unreachable-leaf proof under `descendOrbit`); `claim_reaches_one` vacuous |
| `.singleton n` | Future: bounded-orbit workstream | **Q4 v1 scope** — infrastructure provided; `routed_implies_claim` is hypothesis-bearing (single-input orbit routing proof); `claim_reaches_one` is hypothesis-bearing (`ReachesOne n` from external finite trajectory check) |
| `.bounded K` | Future: bounded-orbit workstream | **Q4 v1 scope** — infrastructure provided; `routed_implies_claim` is hypothesis-bearing (orbit-routed inputs ≤ `K`); `orbit_image_bound` enforces `K` consistency; `claim_reaches_one` is hypothesis-bearing (`∀ x ≤ K, ReachesOne x` from external finite enumeration) |
| `.interval period lo hi` | Q3 v3 scope | **Q3 v4 scope** (unchanged) — handled by `LeafCertificate` + `coverage_tree_soundness_cert` (residue-only routing) |

## Out of scope (unchanged from Q3 v3)

1. **Actual Collatz proof.** Q4 makes the dependency explicit but does
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

## Codex review questions (v1)

1. **Sort rationale: `: Type` for `BoundedOrbitCertificate`.** Does
   Q3 v4's lesson (Lean 4 elaboration rejects `Type`-valued fields in
   `: Prop` structures) apply symmetrically here, requiring the
   structure to be `: Type`-valued from the start? Or is there a
   reason to prefer `: Prop` for `BoundedOrbitCertificate` (e.g.,
   the `well_formed` conjunction is small enough to fit in a `Prop`)?
2. **`orbit_image_bound` field semantics.** Is the
   `claim matches .bounded K' → K' = K` form the right structural
   constraint, or should `orbit_image_bound` be a full
   `∀ x, descendOrbit t x 0 = some l → BoundedOrbit x K` obligation
   (matching the Q3 v4 per-claim-field pattern more strictly)? The
   former is a static structural check; the latter is a dynamic
   routing+orbit obligation.
3. **Companion theorem naming.** `coverage_tree_soundness_orbit_cert`
   (orbit-aware, finite claims) is a sibling to
   `coverage_tree_soundness_cert` (residue-only, interval claims).
   Does the naming convention hold, or is there a clearer
   alternative (e.g., `coverage_tree_soundness_finite`)?
4. **Dependency claim: `coverage_tree_soundness_orbit` NOT needed.**
   The analysis in § "Dependencies" argues that Q4 is independent of
   `coverage_tree_soundness_orbit` (different predicates: `BoundedOrbit`
   vs `SatOrbit`). Is this analysis correct, or is there a hidden
   dependency I missed?
5. **Per-shape obligation split.** The three finite claim shapes
   (`.empty` / `.singleton n` / `.bounded K`) have different
   obligation structures. Is the `well_formed` conjunction
   `(claim matches .bounded _ ∨ ...)` form the right way to encode
   the "finite claim only" constraint, or should it be a separate
   `IsFiniteClaim : LeafClaim → Prop` predicate?
6. **PR sequencing.** Spec (PR #55) → data layer (PR #56) →
   implementation (PR #57) → lessons-learned (PR #58). Is this
   sequencing right, or should the data layer + implementation be
   combined into a single PR (as PR #54 was for Q3)?

## References

- **Q3 v3 spec** (PR #52): [`docs/story-q3-leaf-certificate.md`](story-q3-leaf-certificate.md) — design source; the "Future workstream: bounded-orbit certificates" subsection (lines 359–388) is the v1 sketch that this spec formalizes
- **Q3 v4 implementation** (PR #54, merge commit `c2f3d5b`): `LeafCertificate t l` Type-valued proof-carrying data bundle + `coverage_tree_soundness_cert` companion theorem. Q3 v4 lessons applied throughout Q4 v1
- **07c-2 promotion** (PR #49, merge commit `29c41e0`): [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) — original `LeafReachesOne` predicate + `coverage_tree_soundness_full` companion theorem; Q4 mirrors this pattern for the orbit-aware case
- **07c-4 structural induction** (PR #29, merge commit `4a67591`): [`docs/story-07c-4-structural-induction.md`](story-07c-4-structural-induction.md) — `descend_orbit_complete` + `OrbitRoute` witness; Q4 depends on this for orbit-aware routing
- **02c/03c closed lemmas** (PRs #31, #37, #38, #46, #47): orbit bridges available for downstream Q4 certificate construction
- **Spec parent**: [`docs/story-07c-2-promotion.md`](story-07c-2-promotion.md) Q3 (lines 75–104)
- **Theorem status**: [`docs/theorem-status.md`](theorem-status.md) — rows for `LeafCertificate`, `coverage_tree_soundness_cert`, `descend_orbit_complete` are upstream prerequisites for Q4
- **Closed prerequisites** (orbit bridges): PRs #31, #37, #38, #46, #47 (02c/03c)
- **Lean validation gate**: GitHub Lean CI on each PR (per project discipline; no local `lake` commands)

## Implementation log

- (this commit) — Q4 v1 spec (initial draft, PR #55)

