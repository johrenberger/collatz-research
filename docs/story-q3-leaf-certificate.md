# Story Q3 — Structured `LeafCertificate` type for `coverage_tree_soundness_full`

Status: **v3 spec, scope-corrected per Codex re-review on PR #52 (run 228, 2026-08-21T19:51:46Z).**

## Revision history

- **v1 (PR #52, commit `7eac993`)**: initial sketch with a 4-constructor `LeafCertificate` data type. **Rejected by Codex** at run 222 because the certificate was not linked to its leaf or to the routed inputs.
- **v2 (PR #52, commit `3ac45c2`)**: split into `LeafClaim` (data) + `LeafCertificate t l` (Prop indexed by tree AND leaf, with two obligations). v2 was structurally correct but **still claimed** that `.empty`, `.singleton`, `.bounded` could have `routed_implies_claim` proved "structurally" — this is wrong because `descend` is residue-only routing (no Collatz reduction), so finite claims are not inhabitable under current routing semantics. **Re-review request changes** at run 228.
- **v3 (THIS DOC)**: **scope-narrow** Q3 v3 to the indexed certificate infrastructure only. `.interval` claims stay in scope (structurable via `Sat`); `.empty`, `.singleton`, `.bounded` are kept in the type for forward compatibility but marked as **future orbit/reduction certificates**. Constructive finite-certificate work is moved to a separate **bounded-orbit workstream** that depends on the orbit-aware routing in master (PR #29 at `4a67591`: `descend_orbit_complete`). Also fixes three P2 nits: `ReachesOne` is an unbounded existential (not decidable); `deriving Repr, Decidable` on `LeafClaim` → `deriving Repr, DecidableEq`; closed prerequisites re-stated as downstream orbit bridges.

## Motivation

After the 07c-2 promotion (PR #49, merged 2026-08-21 at `29c41e0`), the
Collatz Research project has a formally established
`coverage_tree_soundness_full` theorem that takes an **explicit**
`hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l` hypothesis
(PR #51 added scenario 8 to `CoverageTreeOrbitTests.lean` as a
compile-checked regression on the explicit-parameter API, merged
2026-08-21 at `388b4a7`).

Q3 replaces the opaque `LeafReachesOne` claim with a typed
**indexed** `LeafCertificate t l` (Type-valued proof-carrying data
bundle) whose two obligation fields make the proof structure
explicit. v3 narrows Q3 to delivering only the **infrastructure** —
the data type, the indexed structure, and the companion theorem —
plus the `.interval` claim shape, whose `routed_implies_claim` is
provable from current `Sat` semantics.

The finite claims (`.empty`, `.singleton`, `.bounded`) are
**deliberately deferred** to a separate orbit-aware workstream,
because under current `descend` semantics (residue-only routing,
no Collatz reduction), finite claims cannot be constructively
inhabited for nonempty leaves. See § "Why finite claims are out
of Q3 scope" below.

## Current state (recap)

| Component | Status | Reference |
|---|---|---|
| `CoverageTree` / `CoverageLeaf` | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 50–71 |
| `leafProperty : String` | Defined | line 58 — opaque token |
| `leanInterval` parser | Defined | lines 173–185 — `"<period>:<lo>-<hi>"` → `Option (Nat × Nat × Nat)` |
| `Sat` / `WellFormed` / `SatOrbit` | Defined | lines 188–245 |
| `coverage_tree_soundness` | Formally established | lines 285–336 |
| `coverage_tree_soundness_full` | Formally established | lines 338–358 (PR #49 at `29c41e0`) |
| `coverage_tree_soundness_orbit` | Preparatory (`sorry`) | lines 361–385 — separate workstream |
| `descend_orbit_complete` | Formally established | PR #29 at `4a67591` — orbit-aware routing |
| Scenario 8 (PR #51) | Compile-checked | `CoverageTreeOrbitTests.lean` — invokes `coverage_tree_soundness_full` with explicit `hLeaf` (no `by sorry` default) |

**`descend` semantics** (critical for Q3 scope): `descend t x` selects
child edges by residue lookup on the **unchanged input** `x`. It never
performs a Collatz step. The residue-routed preimage of a nonempty
leaf is therefore **periodic** (every residue class mod `2^k` contains
infinitely many positive integers). This is the model boundary that
forces the v3 scope correction.

## Design — `LeafClaim` (data) + `LeafCertificate t l` (Type, proof-carrying data bundle)

Q3 splits the certificate into two parts:

- **`LeafClaim`**: pure data — the structural description of which
  inputs are claimed to reach the leaf. Equality-comparable,
  serializable, containable in `leafProperty : String`.
- **`LeafCertificate t l`**: a `Type`-valued **proof-carrying data
  bundle** indexed by tree `t` AND leaf `l`. The `claim : LeafClaim`
  data field forces the structure to live in `Type` (Lean 4
  elaboration rejects `Type`-valued fields in `: Prop`-valued
  structures; a record declared `: Prop` carrying a `Type`-valued
  field will not compile). The structure carries **two distinct
  obligation proofs** as `Prop`-valued fields; the kernel still
  verifies both. The bundle is inspectable data plus kernel-checked
  proof fields — it is NOT proof-irrelevant evidence and is intended
  to be constructed, pattern-matched on, and projected through.

### `LeafClaim` (data, equality-comparable)

```lean
/-- A claim about which inputs reach a leaf. Pure data — equality-
    comparable, serializable, no proof content. The Lean proof that
    the claim holds for the routed inputs (and that every claimed
    input reaches 1) is in `LeafCertificate`.

    **Q3 v3 scope:** only the `.interval` constructor is
    constructively inhabited under current `descend` semantics.
    The other constructors (`.empty`, `.singleton`, `.bounded`)
    are kept in the type for forward compatibility with the
    bounded-orbit workstream (which depends on orbit-aware routing
    from PR #29). See § "Why finite claims are out of Q3 scope". -/
inductive LeafClaim
  | empty                       -- no inputs
  | singleton (n : Nat)         -- exactly one input: n
  | bounded (K : Nat)           -- inputs ≤ K (finite enumeration)
  | interval (period lo hi : Nat)  -- residue interval [lo, hi] mod period
  deriving Repr, DecidableEq

/-- The set of inputs claimed by a `LeafClaim`. Pure predicate. -/
def LeafClaim.Holds : LeafClaim → Nat → Prop
  | .empty       => fun _ => False
  | .singleton n => fun x => x = n
  | .bounded K   => fun x => x ≤ K
  | .interval period lo hi =>
    fun x => lo ≤ x % period ∧ x % period ≤ hi

instance LeafClaim.Holds.decidable (c : LeafClaim) (x : Nat) :
    Decidable (c.Holds x) := by
  cases c <;> first
  | exact (by exact Nat.decLe _ _ ∧ Nat.decLe _ _)
  | exact (by exact Nat.decLe _ _)
```

**Derivation note (P2 fix from re-review)**: `deriving Repr, DecidableEq`
(not `Decidable` — `Decidable` is for `Prop`, not for data types).
`DecidableEq` provides decidable equality on `LeafClaim`. The
`LeafClaim.Holds` decidability instance is derived separately (as
shown above) via case analysis.

### `LeafCertificate t l` (Prop, indexed, two obligations)

```lean
/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `LeafReachesOne t l`. Three components:

    1. `claim : LeafClaim` — data describing which inputs are claimed.
    2. `well_formed : claim.WellFormed` — proof that the claim is
       structurally valid (mandatory field; prevents `.interval 0 0 0`,
       `.interval 2 2 1`, etc. from slipping through).
    3. `routed_implies_claim` — routing-to-claim obligation: every
       input routed to `l` satisfies the claim.
    4. `claim_reaches_one` — reachability obligation: every input
       satisfying the claim reaches 1.

    Composing the two obligation proofs gives `LeafReachesOne t l`.

    Declared as `: Type` (not `: Prop`) because `claim : LeafClaim`
    is a data field; Lean 4 rejects `Type`-valued fields in
    `: Prop`-valued structures. The two obligation fields are still
    `Prop`s, so the kernel still verifies them — only the structure's
    outer sort is `Type`. This makes `LeafCertificate t l` a
    proof-carrying data bundle. -/
structure LeafCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : LeafClaim
  well_formed : claim.WellFormed
  routed_implies_claim :
    ∀ x, descend t x = some l → claim.Holds x
  claim_reaches_one :
    ∀ x, claim.Holds x → ReachesOne x
```

**Sort rationale (`: Type`, not `: Prop`).** The v3 spec originally
declared `LeafCertificate t l : Prop`. PR #54 implementation
discovered that Lean 4 elaboration rejects `Type`-valued fields in
`: Prop`-valued structures — a `Prop`-valued record carrying
`claim : LeafClaim` (a `Type`) will not compile. The structure was
flipped to `: Type` so the data field is legal. Codex review at
PR #54 run 21786 (2026-08-22T12:45:01Z) confirmed this is a real
Lean 4 elaboration limitation, not a bug — the two obligation
fields are still `Prop`s, and the kernel still verifies them. The
sort change is reflected throughout the spec at PR #54 v3.

**No `Decidable LeafCertificate`**: `LeafCertificate t l` is
`: Type`-valued; the structure is constructible on demand (the
caller supplies all fields explicitly). Its `Prop`-valued obligation
fields are kernel-checked at the call site. A separate checker
(Python or Lean tool) can verify finite witnesses for bounded claims
via `BoundedOrbitCertificate` in the future orbit workstream.

## Why finite claims are out of Q3 scope (the v3 scope correction)

The v2 spec claimed `.singleton n` and `.bounded K` could have
`routed_implies_claim` proved "structurally" from `ValidTree t ∧
IsComplete t`. The Codex re-review at run 228 flagged this as wrong:

> `descend t x` only selects child edges using residues of the
> **unchanged input** `x`; it never performs a Collatz step or
> otherwise reduces `x`. For a finite-depth, residue-routed tree, a
> nonempty leaf's preimage is periodic and therefore generally
> infinite. It cannot be contained in `{x | x = n}` or
> `{x | x ≤ K}`. In particular, no structural proof of
> `∀ x, descend t x = some l → x ≤ K` exists for a nonempty routed
> leaf merely from `ValidTree` and `IsComplete`.

The same applies to `.empty`: `False.elim` discharges the
*reachability* field, but it does not establish
`routed_implies_claim : descend t x = some l → False`. That requires
a genuine unreachable-leaf proof.

**Consequence**: under current `descend`, only `.interval` claims
have a structurable `routed_implies_claim` (via `Sat t x l`). The
other three constructors (`.empty`, `.singleton`, `.bounded`) are
kept in the type for forward compatibility but cannot be inhabited
without orbit reduction.

**Future workstream**: the bounded-orbit workstream will add an
orbit-aware `descendOrbit` with orbit-image bounds (e.g.,
`∃ k, accelerated_orbit x k ≤ K`), enabling constructive
`routed_implies_claim` for `.empty`, `.singleton`, and `.bounded`
claims. This workstream depends on:
- `descend_orbit_complete` (PR #29 at `4a67591`, in master) for the
  orbit-aware routing skeleton
- `coverage_tree_soundness_orbit` (PR #36 spec, `sorry` pending) for
  the orbit-aware soundness closure
- The 02c/03c closed lemmas (PRs #31, #37, #38, #46, #47) as
  **downstream orbit bridges** (see § "Closed prerequisites")

## API integration

### `parse_leaf_claim` (untrusted structural decoder)

```lean
/-- Untrusted structural decoder: parses a `CoverageLeaf`'s
    `leafProperty` into a `LeafClaim` (data only). Does NOT
    construct the Lean proof. The proof is supplied by the caller.

    **Q3 v3 scope:** the decoder recognises only the existing
    `"<period>:<lo>-<hi>"` format and produces the `.interval`
    claim. Other claim shapes (`.singleton`, `.bounded`) require
    new `leafProperty` formats and are deferred. -/
def parse_leaf_claim (l : CoverageLeaf) : Option LeafClaim :=
  match leanInterval l with
  | some (period, lo, hi) =>
    if hWF : period > 0 ∧ lo ≤ hi ∧ hi < period then
      some (LeafClaim.interval period lo hi)
    else none
  | none => none
```

The decoder is **structural only** (per re-review decision #3); it
must never manufacture semantic evidence.

### `coverage_tree_soundness_cert` (revised theorem)

```lean
/-- Variant of `coverage_tree_soundness_full` where the per-leaf
    certificate is the typed `LeafCertificate t l` Prop (indexed by
    tree AND leaf) rather than an opaque `LeafReachesOne` claim.

    A **sound, typed refinement** of `coverage_tree_soundness_full`:
    the proof composes `routed_implies_claim` and `claim_reaches_one`
    to derive `LeafReachesOne t l`. The new `hCert` hypothesis is
    **strictly stronger** than `coverage_tree_soundness_full`'s
    `hLeaf` (a `LeafCertificate t l` factors through
    `LeafReachesOne t l` via `claim_reaches_one ∘ routed_implies_claim`;
    the reverse is not supplied and generally cannot construct a
    well-formed claim plus its all-claim reachability proof from
    `hLeaf` alone). PR #54 does **NOT** establish any new global or
    per-leaf Collatz reachability result.

    **Q3 v3 scope:** the theorem is universally quantified over
    `LeafClaim` shapes. For `.interval` claims,
    `routed_implies_claim` is structural (via `Sat`); for the other
    constructors, it must come from the bounded-orbit workstream
    (see § "Why finite claims are out of Q3 scope"). -/
theorem coverage_tree_soundness_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → LeafCertificate t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l := by
  obtain ⟨l, hl, hver, hdesc⟩ := coverage_tree_soundness t hv hic x hx
  refine ⟨l, hl, hver, hdesc, ?_⟩
  intro x' hdesc'
  exact (hCert l hl hver).claim_reaches_one x'
         ((hCert l hl hver).routed_implies_claim x' hdesc')
```

### Scenario 8 update (Q3 v3)

`CoverageTreeOrbitTests.lean` scenario 8 is updated to use the new
`coverage_tree_soundness_cert` API with the **indexed**
`LeafCertificate depthTwoTree l` parameter:

```lean
-- Scenario 8 (Q3): compile-checked regression example for
-- `coverage_tree_soundness_cert` with a concrete `depthTwoTree` +
-- indexed `LeafCertificate depthTwoTree l` certificates. The
-- `hCert` parameter is **explicit** (no default) — preserves the
-- no-new-`sorry` discipline from PR #51 P1.
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             LeafCertificate depthTwoTree l) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descend depthTwoTree 5 = some l ∧ LeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_cert depthTwoTree hv hc hCert 5 (by norm_num)
```

## Per-shape proof obligations (revised — Q3 v3 scope)

| Claim | `claim.Holds` | `routed_implies_claim` provable under current `descend`? | `claim_reaches_one` provable? | Q3 v3 status |
|---|---|---|---|---|
| `.empty` | `False` | **No** — requires genuine unreachable-leaf proof (orbit-aware) | Vacuously | Future: bounded-orbit workstream |
| `.singleton n` | `x = n` | **No** — preimage is periodic and infinite | Constructive (small `n`: trajectory) | Future: bounded-orbit workstream |
| `.bounded K` | `x ≤ K` | **No** — preimage is periodic and infinite | Constructive (finite enumeration of `x ≤ K`) | Future: bounded-orbit workstream |
| `.interval period lo hi` | residue `[lo, hi]` mod `period` | **Yes** — structural via `Sat t x l` | **Hypothesis-bearing** — global Collatz for class | **Q3 v3 scope** |

**Per the re-review at run 228**: "If finite certificates remain in
the data type, state that their `routed_implies_claim` fields are not
expected to be inhabitable under present `descend` except for
separately proved degenerate leaves." This is what the table above
encodes.

## ReachesOne decidability clarification (P2 fix)

`ReachesOne x := ∃ k, accelerated_orbit x k = 1` is an **unbounded
existential** (over `k : Nat`). It is **not decidable** in general.

For finite claims (deferred to the bounded-orbit workstream), a
finite checker must supply **explicit bounded witnesses**: for each
input `x` in the claim's domain, provide a `k : Nat` and a checked
equality `accelerated_orbit x k = 1`. Lean can then reduce/check each
concrete witness via `decide`. The orbit-aware workstream will
introduce a `BoundedOrbitCertificate` (or similar) bundling these
witnesses.

For `.interval` claims (Q3 v3 scope), `claim_reaches_one` is
hypothesis-bearing — the caller supplies the unbounded
`ReachesOne x` proof directly (typically via an external source or
axiom).

## Closed prerequisites (02c/03c) — re-stated as downstream orbit bridges

The following 5 lemmas, closed in PRs #31 + #37 + #38 + #46 + #47,
are **downstream orbit bridges** for the future bounded-orbit
workstream. They do **not** establish `routed_implies_claim` under
current `descend` semantics (per the re-review P2):

| Lemma | PR | Role in future bounded-orbit workstream |
|---|---|---|
| `acceleratedStep_odd_of_odd` | #31 | Bridge: odd-input orbit step produces odd output |
| `standardStep_positive` | #37 | Bridge: standard step preserves positivity |
| `acceleratedStep_positive_of_odd` | #38 | Bridge: accelerated step preserves positivity for odd input |
| `acceleratedStep_equiv_standardStep` | #46 | Bridge: accelerated ≡ standard step composition |
| `acceleratedTrajectory_reaches_one_implies_standard` | #47 | Bridge: accelerated trajectory reaching 1 → standard trajectory |

The re-review is explicit: "The 02c/03c lemmas concern dynamics and
equivalence. They do not establish the current tree's
`descend t x = some l → claim.Holds x` structural relation; that
relation must come from the tree layout/labels and a dedicated
alignment invariant."

Q3 v3 does not use these lemmas directly. They will be relevant when
the bounded-orbit workstream adds orbit-image bounds.

## Implementation plan (revised — Q3 v3)

| PR | Scope | Lean CI |
|---|---|---|
| **#53** | `LeafClaim` data type + `LeafClaim.Holds` + `parse_leaf_claim` + `DecidableEq` + `LeafClaim.Holds.decidable` instance | Yes |
| **#54** | `LeafCertificate t l` Prop + `coverage_tree_soundness_cert` + scenario 8 update (indexed cert) | Yes |
| ~~**#55**~~ | ~~Constructive proofs for `.bounded K`~~ — **REMOVED** from Q3 v3; moved to bounded-orbit workstream | — |
| **#56** | Lessons-learned doc (if notable patterns emerge from PRs #53–54) | No |

**Future workstream (separate, NOT in Q3 v3)**: bounded-orbit
certificates — depends on `descend_orbit_complete` (PR #29) and
`coverage_tree_soundness_orbit` (PR #36 spec). Will introduce
`BoundedOrbitCertificate` for finite claims via orbit-image bounds.

## Future workstream: bounded-orbit certificates

**Goal**: provide constructive `routed_implies_claim` for
`.empty`, `.singleton`, and `.bounded` claims via orbit-aware
routing (`descendOrbit`) and orbit-image bounds.

**Prerequisites** (already in master or pending):
- `descend_orbit_complete` (PR #29 at `4a67591`, formally established)
- `coverage_tree_soundness_orbit` (PR #36 spec, `sorry` pending —
  separate workstream)
- The 02c/03c closed lemmas (PRs #31, #37, #38, #46, #47) as
  orbit bridges

**Design sketch** (out of scope for Q3 v3):

```lean
/-- Orbit-image bound: x reaches a value ≤ K within its
    accelerated orbit. Finite enumeration then proves ReachesOne
    for each value ≤ K. -/
def BoundedOrbit (x : Nat) (K : Nat) : Prop :=
  ∃ k, accelerated_orbit x k ≤ K

/-- A bounded-orbit certificate bundles orbit witnesses for the
    finite domain. The future workstream will construct this from
    `parse_leaf_claim` + per-input trajectory checks. -/
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Prop where
  -- ... (future design)
```

The Q3 v3 implementation does not deliver this. It is sketched here
so the data type (`LeafClaim`) and Prop (`LeafCertificate t l`) can
accommodate it without breaking changes.

## Codex decisions acknowledged

Per the re-review at run 228 (2026-08-21T19:51:46Z):

1. **Remove finite claims from Q3 v3 implementation, OR mark them
   explicitly as future orbit/reduction certificates.** v3 marks them
   as future (kept in the type for forward compatibility, but not
   constructively inhabited under current `descend`).
2. **PRs #53–#54 establish only the generic indexed certificate
   interface + conditional companion theorem.** No claim that Q3
   constructively supplies certificates for present nonempty leaves.
3. **Finite certificates stay in the data type** (for forward
   compatibility) with explicit note that `routed_implies_claim` is
   not expected to be inhabitable under present `descend` except for
   separately proved degenerate leaves.
4. **Constructive finite-certificate work moves to a separate
   bounded-orbit workstream** that depends on `descend_orbit_complete`
   (PR #29) + `coverage_tree_soundness_orbit` (PR #36 spec).
5. **ReachesOne is an unbounded existential**, not decidable.
   Finite checkers must supply explicit bounded witnesses.
6. **`deriving Repr, Decidable` → `deriving Repr, DecidableEq`** on
   `LeafClaim` (`Decidable` is for `Prop`, not data types).
7. **02c/03c lemmas are downstream orbit bridges**, not direct inputs
   to `routed_implies_claim`.

After these scope corrections, Codex supports merging the spec.

## Out of scope (unchanged from v2)

1. **Actual Collatz proof.** Q3 makes the dependency explicit but does
   not prove the Collatz theorem for any non-trivial interval.
2. **`coverage_tree_soundness_orbit`** (the `sorry` from PR #36).
   Separate orbit-aware routing workstream.
3. **Bounded-orbit certificates.** Q3 v3 defers `.empty`,
   `.singleton`, `.bounded` constructive certificates to a separate
   future workstream (see § "Future workstream: bounded-orbit
   certificates").
4. **Python oracle bridge.** Promoting `tests/test_coverage_tree.py`
   to formal proofs requires a Python↔Lean translation layer.
5. **Composite certificates** (`union`, `inter`,
   `tree_of_certificates`). Deferred to Q3 follow-ups if needed.
6. **Replacing `leafProperty : String`.** Deferred to a future Q3
   version after the type stabilises.

## References

- **PR #49** (07c-2 promotion): `29c41e0`
- **PR #50** (lessons-learned doc): `7d42bfb`
- **PR #51** (P2 follow-ups + scenario 8): `388b4a7`
- **PR #52 v1** (this branch, commit `7eac993`): rejected at run 222
- **PR #52 v2** (this branch, commit `3ac45c2`): request-changes re-review at run 228
- **PR #52 v3** (THIS DOC): scope-corrected per re-review
- **PR #29** (07c-4 `descend_orbit_complete`): `4a67591` — orbit-aware routing in master
- **PR #36** (07c-2 v2 spec + `coverage_tree_soundness_orbit`): `57b6d37` — orbit-aware soundness (sorry pending)
- **Spec parent**: `docs/story-07c-2-promotion.md` Q3 (lines 75–104)
- **Theorem status**: `docs/theorem-status.md` row for `LeafReachesOne`
- **Closed prerequisites** (re-stated as downstream orbit bridges):
  PRs #31, #37, #38, #46, #47 (02c/03c)