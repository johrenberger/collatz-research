# Story Q3 — Structured `LeafCertificate` type for `coverage_tree_soundness_full`

Status: **v2 spec, redesigned per Codex P1 + P2 feedback on PR #52 (run 222, 2026-08-21T19:36:30Z).**

## Revision history

- **v1 (PR #52, commit `7eac993`)**: initial sketch with a 4-constructor `LeafCertificate` data type. **Rejected by Codex** at run 222 because the certificate was **not linked to its leaf or to the routed inputs** — `coverage_tree_soundness_cert` was not kernel-equivalent to `coverage_tree_soundness_full`. Two P1s + one P2.
- **v2 (THIS DOC, PR #52 follow-up commit)**: split into `LeafClaim` (pure data, decidable, serializable) + `LeafCertificate t l` (Prop indexed by tree AND leaf, with **two distinct obligations**: `routed_implies_claim` and `claim_reaches_one`). `bounded K` replaces the v1 `known_small` for finite cases. The parser is renamed `parse_leaf_claim` and explicitly flagged as an **untrusted structural decoder** — it must never manufacture semantic evidence. PR #51 narrative corrected (no `by sorry` was in the merged version).

## Motivation

After the 07c-2 promotion (PR #49, merged 2026-08-21 at `29c41e0`), the
Collatz Research project has a formally established
`coverage_tree_soundness_full` theorem that takes an **explicit**
`hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l` hypothesis
and routes any positive `x` to a leaf with the `LeafReachesOne`
certificate in the conclusion (PR #51 added scenario 8 to
`CoverageTreeOrbitTests.lean` as a compile-checked regression on the
explicit-parameter API, merged 2026-08-21 at `388b4a7`).

But `LeafReachesOne t l := ∀ x, descend t x = some l → ReachesOne x` is
**trustable only via the `hLeaf` hypothesis**. The conditional form
was the right thing for PR #49 — it stops short of claiming the global
Collatz theorem from tree soundness alone. But it also leaves a real
gap: **what should `hLeaf` look like as actual data, not as a
hypothesis to be supplied by callers?**

v1's first attempt at answering that question failed. The proposed
4-constructor `LeafCertificate` data type carried the proof inside
each constructor (`hReach`, `h`, etc.) but had **no link** between the
certificate and:
1. The leaf it is attached to.
2. The inputs that the tree routes to that leaf.

Consequently, each proof branch in v1 was unjustified:
- `empty` contained no proof that no input descends to the leaf.
- `single n hReach` proved only `ReachesOne n`, not `ReachesOne x`
  for an arbitrary `x` routed to that leaf.
- `interval ... h ...` required `Sat t x l` (residue membership),
  which `coverage_tree_soundness` does not derive.

v2 fixes this by making the certificate a **Prop indexed by
`(t, l)`** and separating the two distinct obligations
explicitly. The kernel can then verify both.

## Current state (recap, with PR #51 narrative correction)

| Component | Status | Reference |
|---|---|---|
| `CoverageTree` / `CoverageLeaf` | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 50–71 |
| `leafProperty : String` | Defined | `Lean/CollatzResearch/CoverageTree.lean` line 58 — opaque token |
| `leanInterval` parser | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 173–185 — `"<period>:<lo>-<hi>"` → `Option (Nat × Nat × Nat)` |
| `Sat` / `WellFormed` / `SatOrbit` | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 188–245 |
| `coverage_tree_soundness` | Formally established | `Lean/CollatzResearch/CoverageTree.lean` lines 285–336 |
| `coverage_tree_soundness_full` | Formally established | `Lean/CollatzResearch/CoverageTree.lean` lines 338–358 (PR #49, `29c41e0`) |
| `coverage_tree_soundness_orbit` | Preparatory (`sorry`) | `Lean/CollatzResearch/CoverageTree.lean` lines 361–385 — separate workstream, **out of scope** |
| `descend_orbit_complete` | Formally established | PR #29 at `4a67591` — separate workstream, **out of scope** |
| Scenario 8 (PR #51) | Compile-checked | `Lean/CollatzResearch/CoverageTreeOrbitTests.lean` — invokes `coverage_tree_soundness_full` with **explicit** `hLeaf` parameter (no `:= by sorry` default, per Codex P1 at PR #51 run 196) |

**Note (corrected from v1)**: PR #51 was merged with the **explicit**
`hLeaf` parameter precisely to remove the `:= by sorry` default. The
`by sorry` placeholder was the P1 fix at commit `23aef20`. Q3 does
**not** remove a `sorry`; Q3 **replaces** the `LeafReachesOne` claim
with the new indexed `LeafCertificate t l` (Prop with two obligations),
keeping the explicit-parameter discipline. v1's framing — "PR #51
scenario 8 used `by sorry` and will be removed by Q3" — was wrong on
both counts and is corrected here.

## Design — `LeafClaim` (data) + `LeafCertificate t l` (Prop)

The design follows the three-option analysis from
`docs/story-07c-2-promotion.md` § "Why this matters" (lines 88–101):

1. **Structured certificates** ← preferred; the shape of Q3.
2. **Proof-carrying strings** ← rejected; brittle.
3. **External oracle** ← rejected; requires formal integration.

Q3 splits the certificate into two parts:

- **`LeafClaim`**: pure data — the structural description of which
  inputs are claimed to reach the leaf. Decidable, serializable,
  containable in `leafProperty : String`.
- **`LeafCertificate t l`**: a `Prop` indexed by tree `t` AND leaf `l`,
  carrying **two distinct obligations** as fields.

The split makes the claim auditable as data while keeping the proof
obligations kernel-checked.

### `LeafClaim` (data, decidable)

```lean
/-- A claim about which inputs reach a leaf. Pure data — decidable,
    serializable, no proof content. The Lean proof that the claim
    holds for the routed inputs (and that every claimed input reaches
    1) is in `LeafCertificate`. -/
inductive LeafClaim
  | empty                       -- no inputs
  | singleton (n : Nat)         -- exactly one input: n
  | bounded (K : Nat)           -- inputs ≤ K (finite enumeration)
  | interval (period lo hi : Nat)  -- residue interval [lo, hi] mod period
  deriving Repr, Decidable

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
  | exact (by infer_instance)
  | exact (by exact Nat.decLe _ _)
  | exact (by exact Nat.decLe _ _ ∧ Nat.decLe _ _)
```

The four constructors:

- **`.empty`**: the leaf claims no inputs reach it. The `Holds`
  predicate is `False`, so the certificate's `routed_implies_claim`
  must show that no input descends here.
- **`.singleton n`**: the leaf claims exactly one input `n`. The
  certificate must show that all routed inputs equal `n`.
- **`.bounded K`**: the leaf claims inputs `x ≤ K`. **Finite
  enumeration** — for small `K`, the certificate's
  `claim_reaches_one` is provable by `decide` on the finite trajectory
  table. The bound `K` is a **parameter of the claim**, not a hard-
  coded constant.
- **`.interval period lo hi`**: the leaf claims a residue interval
  modulo `period`. **Not finite** — this is the unproven Collatz-for-
  this-class obligation. The certificate's `claim_reaches_one` is the
  caller's responsibility.

### `LeafCertificate t l` (Prop, indexed, two obligations)

```lean
/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `LeafReachesOne t l`. The certificate has two distinct
    obligations:

    1. `routed_implies_claim`: every input routed to `l` satisfies the
       claim. (Routing-to-claim obligation.)
    2. `claim_reaches_one`: every input satisfying the claim reaches
       1. (Reachability obligation.)

    Composing these gives `LeafReachesOne t l`. -/
structure LeafCertificate (t : CoverageTree) (l : CoverageLeaf) : Prop where
  claim : LeafClaim
  routed_implies_claim :
    ∀ x, descend t x = some l → claim.Holds x
  claim_reaches_one :
    ∀ x, claim.Holds x → ReachesOne x
```

**Important — no `Decidable LeafCertificate`**: the certificate is a
`Prop` with universal-function fields (`routed_implies_claim`,
`claim_reaches_one`). Per Codex's P1 decision, we do **not** promise
a `Decidable` instance. The claim side (`LeafClaim`) is decidable;
the proof side is kernel-checked. A separate checker can verify
finite witnesses for `.bounded K` claims (e.g., a Python harness
that runs `decide` on each `x ≤ K` and confirms `ReachesOne x`).

### Why this design (vs v1's rejected version)

| v1 flaw | v2 fix |
|---|---|
| `single n hReach` carried only `ReachesOne n` | `LeafCertificate t l` carries `routed_implies_claim : ∀ x, descend t x = some l → claim.Holds x` — the claim is leaf-specific |
| `interval ... h ...` mixed routing + reachability in one `h` | Split: `routed_implies_claim` (structural) + `claim_reaches_one` (the global-Collatz obligation) |
| `empty` had no obligation | `.empty`'s `claim.Holds x = False` forces `routed_implies_claim` to prove no input descends |
| No link between certificate and leaf | `LeafCertificate` is indexed by `(t, l)` — the routing-to-claim obligation is leaf-specific |
| The parser produced semantic evidence | `parse_leaf_claim` is flagged as a **structural decoder only**; the proof is the caller's job |

## API integration

### `parse_leaf_claim` (untrusted structural decoder)

```lean
/-- Untrusted structural decoder: parses a `CoverageLeaf`'s
    `leafProperty` into a `LeafClaim` (data only). Does NOT
    construct the Lean proof. The proof is supplied by the caller.

    This is a STRUCTURAL DECODER, not a SEMANTIC DECODER. It must
    never be used to manufacture semantic evidence. The
    `leafProperty` string is an untrusted input — the caller is
    responsible for verifying the resulting claim's semantic
    obligations. -/
def parse_leaf_claim (l : CoverageLeaf) : Option LeafClaim :=
  match leanInterval l with
  | some (period, lo, hi) =>
    if hWF : period > 0 ∧ lo ≤ hi ∧ hi < period then
      some (LeafClaim.interval period lo hi)
    else none
  | none => none
```

The decoder recognises only the existing `"<period>:<lo>-<hi>"`
format and produces the `interval` claim. Other claim shapes
(`.singleton`, `.bounded`) would require new `leafProperty` formats
and are out of scope for v2.

**Critical**: `parse_leaf_claim` is not `certificate_of_leaf`. The
proof is not constructed here. This is the P2 fix from Codex — the
legacy parser is preserved as an untrusted decoder.

### `coverage_tree_soundness_cert` (revised theorem)

```lean
/-- Variant of `coverage_tree_soundness_full` where the per-leaf
    certificate is the typed `LeafCertificate t l` Prop (indexed by
    tree AND leaf) rather than an opaque `LeafReachesOne` claim.

    **Kernel-equivalent** to `coverage_tree_soundness_full`: the
    proof composes `routed_implies_claim` and `claim_reaches_one`
    to derive `LeafReachesOne t l`.

    **Easier to audit** — the two obligations are explicit at the
    call site, and the kernel verifies them. The certificate is
    leaf-specific (indexed by `l`), so the routing-to-claim
    obligation is provable from the local tree structure. -/
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

The proof is the **composition** of the two obligations:

1. `coverage_tree_soundness` gives `l ∈ t.leaves`, `verified t l`,
   and `descend t x = some l`.
2. `hCert l hl hver : LeafCertificate t l` gives the two obligations
   for this specific leaf.
3. `(hCert l hl hver).routed_implies_claim x' hdesc'` proves
   `claim.Holds x'`.
4. `(hCert l hl hver).claim_reaches_one x'` proves `ReachesOne x'`.

This is the kernel-equivalent composition — no axioms, no `sorry`.

### Scenario 8 update (Q3 revision)

`CoverageTreeOrbitTests.lean` scenario 8 is updated to use the new
`coverage_tree_soundness_cert` API instead of `coverage_tree_soundness_full`,
with the parameter changed to the **indexed** `LeafCertificate depthTwoTree l`
(per Codex P1 decision #5):

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

## Per-shape proof obligations (revised — finite vs infinite split)

| Claim | `claim.Holds` | `routed_implies_claim` provable? | `claim_reaches_one` provable? | Strategy |
|---|---|---|---|---|
| `.empty` | `False` | **Yes** — `False.elim` (any routed input → False) | **Vacuously** — `False → ReachesOne x` | Trivial |
| `.singleton n` | `x = n` | **Yes** — structural: only `n` descends | **Constructive** (small `n`) — trajectory computation | `ReachesOne n` via `decide` |
| `.bounded K` | `x ≤ K` | **Yes** — structural: bounded set | **Constructive** — finite enumeration of `x ≤ K` | Enumerate `ReachesOne x` for each `x ≤ K` |
| `.interval period lo hi` | `lo ≤ x % period ∧ x % period ≤ hi` | **Yes** — structural: residue matches | **Hypothesis-bearing** — global Collatz for class | Caller supplies `ReachesOne` proof |

**Critical correction from v1**: v1 claimed `period = 2, lo = 0, hi = 1`
was a "small finite-enumeration case". This is **wrong** — that
interval covers **all** natural numbers (since `x % 2 ∈ {0, 1}`), so
it is exactly the global Collatz obligation, not a finite case.

Finite enumeration requires an explicit bound like `x ≤ K` (via
`.bounded K`), **not** a residue class. The 02c/03c closed lemmas
are bridges — they do not discharge `∀ x, ReachesOne x` on any
infinite residue class.

## Closed prerequisites (02c/03c)

The following 5 lemmas, closed in PRs #31 + #37 + #38 + #46 + #47,
are **direct inputs** to the `routed_implies_claim` side and
structural arguments:

| Lemma | PR | Usage in Q3 |
|---|---|---|
| `acceleratedStep_odd_of_odd` | #31 | Structural: odd-input orbit step produces odd output |
| `standardStep_positive` | #37 | Structural: standard step preserves positivity |
| `acceleratedStep_positive_of_odd` | #38 | Structural: accelerated step preserves positivity for odd input |
| `acceleratedStep_equiv_standardStep` | #46 | Structural: accelerated ≡ standard step composition |
| `acceleratedTrajectory_reaches_one_implies_standard` | #47 | Structural: accelerated trajectory reaching 1 → standard trajectory |

These are **bridges** — they prove the structural relationships
needed for `routed_implies_claim`. They do **not** discharge
`claim_reaches_one` for any infinite residue class (per Codex P1.2).
For finite `.bounded K` claims, the `claim_reaches_one` proof is by
finite enumeration (using `decide` on each `x ≤ K`'s trajectory).

## Implementation plan (revised)

The split into multiple PRs is deliberate: each PR has a single
**verifiable** claim (data type, theorem + scenario, constructive
proofs, docs).

- **PR #53** (docs + Lean): add `LeafClaim` inductive type +
  `LeafClaim.Holds` predicate + `parse_leaf_claim` + `Decidable`
  instances. Lean CI gate.
- **PR #54** (Lean + docs): add `LeafCertificate t l` Prop +
  `coverage_tree_soundness_cert` theorem + scenario 8 update
  (indexed cert parameter). Lean CI gate.
- **PR #55** (Lean + docs): constructive proofs for `.bounded K`
  (small K via `decide` on finite trajectory). **K is a
  parameter**; the default value is chosen **after** the
  checker/witness representation has measured CI cost (per Codex
  decision #2). Lean CI gate.
- **PR #56** (docs-only): lessons-learned doc (if notable patterns
  emerge from PRs #53–55).

## Codex decisions acknowledged

Per the Codex review at run 222 (2026-08-21T19:36:30Z):

1. **Keep `interval` hypothesis-bearing.** Neither `noncomputable` nor
   `classical` marks an axiom or solves the proof obligation. The
   `claim_reaches_one` obligation for `interval` claims is the caller's
   responsibility.
2. **Do not select `K = 64` yet.** The bound `K` is a certificate
   parameter; the default value is chosen after the
   checker/witness representation has measured CI cost. PR #55 will
   introduce the bound; the default value will be set there.
3. **Preserve the legacy parser only as an untrusted structural
   decoder.** `parse_leaf_claim` decodes the structural data only;
   the proof is the caller's job. It must not manufacture semantic
   evidence.
4. **`coverage_tree_soundness_cert` is a good name** — kept as the
   companion theorem name.
5. **Keep Scenario 8, but make its parameter `LeafCertificate depthTwoTree l`** (indexed by tree AND leaf), not an unindexed certificate.

## Out of scope (unchanged from v1)

1. **Actual Collatz proof.** Q3 makes the dependency explicit but does
   not prove the Collatz theorem for any non-trivial interval. The
   project does not have this proof; PR #49 deliberately scopes
   around it.
2. **`coverage_tree_soundness_orbit`** (the `sorry` from PR #36).
   Separate orbit-aware routing workstream. Not touched by Q3.
3. **Python oracle bridge.** Promoting
   `tests/test_coverage_tree.py` to formal proofs requires a
   Python↔Lean translation layer. Not in Q3 v2.
4. **Composite certificates** (`union`, `inter`,
   `tree_of_certificates`). Deferred to Q3 follow-ups if needed.
5. **Replacing `leafProperty : String`.** Q3 v2 adds `LeafCertificate`
   alongside the existing field; replacing the field is a breaking
   change that affects the Python side and tests. Deferred to Q3 v3
   after the type stabilises.

## References

- **PR #49** (07c-2 promotion): `29c41e0`
- **PR #50** (lessons-learned doc): `7d42bfb`
- **PR #51** (P2 follow-ups + scenario 8): `388b4a7`
- **PR #52 v1** (this branch, commit `7eac993`): rejected by Codex at run 222
- **PR #52 v2** (THIS DOC): redesigned per Codex feedback
- **Spec parent**: `docs/story-07c-2-promotion.md` Q3 (lines 75–104)
- **Theorem status**: `docs/theorem-status.md` row for `LeafReachesOne`
- **Closed prerequisites**: PRs #31, #37, #38, #46, #47 (02c/03c)
- **Out-of-scope siblings**: `coverage_tree_soundness_orbit` (PR #36
  spec, `sorry` workstream), `descend_orbit_complete` (PR #29,
  formally established, separate workstream)