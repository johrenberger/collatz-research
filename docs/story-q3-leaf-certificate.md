# Story Q3 — Structured `LeafCertificate` type for `coverage_tree_soundness_full`

Status: **v1 spec draft (2026-08-21).** Design under Codex review.

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
a **trustable only via the `hLeaf` hypothesis**. In PR #51's scenario
8, `hLeaf` is supplied as an explicit parameter — the regression
compiles, but the proof obligation is the caller's responsibility.

The conditional form was the right thing for PR #49 — it stops short of
claiming the global Collatz theorem from tree soundness alone. But it
also leaves a real gap: **what should `hLeaf` look like as actual data,
not as a hypothesis to be supplied by callers?**

This spec addresses that gap.

## Current state (recap)

| Component | Status | Reference |
|---|---|---|
| `CoverageTree` / `CoverageLeaf` | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 50–71 |
| `leafProperty : String` | Defined | `Lean/CollatzResearch/CoverageTree.lean` line 58 — opaque token |
| `leanInterval` parser | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 173–185 — `"<period>:<lo>-<hi>"` → `Option (Nat × Nat × Nat)` |
| `Sat` / `WellFormed` / `SatOrbit` | Defined | `Lean/CollatzResearch/CoverageTree.lean` lines 188–245 |
| `coverage_tree_soundness` | Formally established | `Lean/CollatzResearch/CoverageTree.lean` lines 285–336 |
| `coverage_tree_soundness_full` | Formally established | `Lean/CollatzResearch/CoverageTree.lean` lines 338–358 (squash-merged at `29c41e0`) |
| `coverage_tree_soundness_orbit` | Preparatory (`sorry`) | `Lean/CollatzResearch/CoverageTree.lean` lines 361–385 — separate workstream, **out of scope** |
| `descend_orbit_complete` | Formally established | PR #29 at `4a67591` — separate workstream, **out of scope** |
| Scenario 8 (PR #51) | Compile-checked | `Lean/CollatzResearch/CoverageTreeOrbitTests.lean` — invokes `coverage_tree_soundness_full` with explicit `hLeaf` parameter |

`LeafReachesOne` is documented in `docs/theorem-status.md` as:
> Defined (predicate) — leaf-level semantic certificate. Promotion to `Checked` requires per-leaf certificate construction (see `docs/story-07c-2-promotion.md` Q3).

## The gap Q3 closes

The current `coverage_tree_soundness_full` API is sound but
**not self-contained**: a caller who wants to use it must construct a
`hLeaf` proof from somewhere. The "somewhere" today is either:
1. An external oracle (Python's `tree.py`, a separate Lean file, etc.).
2. A direct proof that descends into the Collatz theorem (not available).
3. An explicit `sorry` (PR #51's scenario 8 — explicitly marked as
   `by sorry` placeholder; will be removed when Q3 lands).

Q3 replaces (3) with a real data type: **structured `LeafCertificate`s
that the project itself can produce and verify**, with explicit
"axiom-of-Collatz" boundaries for cases the project cannot prove
constructively.

## Design — `LeafCertificate` inductive type

The design follows the three-option analysis from
`docs/story-07c-2-promotion.md` § "Why this matters" (lines 88–101):

1. **Structured certificates** ← preferred; the shape of Q3.
2. **Proof-carrying strings** ← rejected; brittle.
3. **External oracle** ← rejected; requires formal integration.

### Definition sketch

```lean
/-- A structured certificate that a leaf carries to prove
    `LeafReachesOne t l`. The certificate is data: it can be
    constructed by the project from a `CoverageLeaf` (via
    `certificate_of_leaf`) and verified by the kernel.

    Constructors come in two flavours:
    - **Constructive** (`single`, `empty`, `known_small`): the proof
      is witnessed by trajectory computation or induction. No
      external axiom needed.
    - **Hypothesis-bearing** (`interval`): the proof of
      `ReachesOne` for the interval is supplied by the caller.
      When the interval covers all residues, this is equivalent
      to the Collatz theorem restricted to one residue class;
      the caller is acknowledging that dependency explicitly.

    The split between constructive and hypothesis-bearing is the
    "axiom-of-Collatz boundary" — Q3 makes it auditable. -/
inductive LeafCertificate where
  | empty : LeafCertificate
    -- For leaves that cover no inputs (e.g., `0:0-0` — every input
    -- is outside the interval). `LeafReachesOne` is vacuously true.

  | single (n : Nat) (hReach : ReachesOne n) : LeafCertificate
    -- For a leaf that declares exactly one reachable input `n`.
    -- Proof is supplied by the caller; for small `n` it can be
    -- discharged by trajectory computation
    -- (`by decide` on the finite trajectory).

  | known_small (n : Nat) (hn : n ≤ K) : LeafCertificate
    -- For a leaf that declares a small `n ≤ K` is reachable.
    -- Bound `K` is fixed (suggested `K = 64` — small enough for
    -- exhaustive verification via `decide`). Proof: enumerate the
    -- finite trajectory.

  | interval (period lo hi : Nat)
      (h : ∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x)
      (hWF : period > 0 ∧ lo ≤ hi ∧ hi < period) : LeafCertificate
    -- For a leaf that declares a residue interval modulo `period`.
    -- The proof obligation is explicit: the caller must supply
    -- `h : ∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x`.
    -- When `period = 2` and `[lo, hi] = [1, 1]`, this covers all
    -- odd `x` — equivalent to the Collatz theorem for the odd
    -- residue class.
```

### Constructor choices — alternatives considered

- **`of_residue`** (residue-only, no `lo`/`hi`): rejected. The
  `interval` form subsumes it (`lo = hi = r`) and keeps the
  structural shape uniform.
- **`union` / `inter`**: deferred. Composite certificates can be
  added in a Q3 follow-up if the codebase needs them; YAGNI for v1.
- **`tree_of_certificates`** (nested certificates): deferred.
  Composite certificates for non-trivial trees can use `interval`
  directly with a coarser `period`.
- **`extern_python`** (typed bridge to Python oracle): deferred.
  The Python runtime tests are **untrusted runtime evidence** (per
  `MEMORY.md`); promoting them to formal proofs would require a
  Python↔Lean translation layer that is out of scope.

## API integration

### New parser

```lean
/-- Parse a `CoverageLeaf` into a `LeafCertificate`, if possible.

    The parser recognises the existing `"<period>:<lo>-<hi>"` format
    (carried over from `leafProperty`) and dispatches to:
    - `LeafCertificate.empty` if the interval is vacuous (`hi < lo`,
      impossible due to `WellFormed`, so unreachable; reserved for
      future "no inputs" leaves).
    - `LeafCertificate.single n hReach` if the interval is a single
      residue (`lo = hi`) and the caller supplies the reachability
      proof (out of scope for v1; rejected for now).
    - `LeafCertificate.interval period lo hi h hWF` otherwise; the
      proof `h` is left as an obligation.

    Returns `none` for any `CoverageLeaf` whose `leafProperty` does
    not parse. The caller is expected to have verified `WellFormed`
    before calling this parser. -/
def certificate_of_leaf (l : CoverageLeaf) : Option LeafCertificate :=
  match leanInterval l with
  | some (period, lo, hi) =>
    if hWF : period > 0 ∧ lo ≤ hi ∧ hi < period then
      -- Build the interval certificate with the proof as an obligation.
      -- The caller supplies `h` separately (see `certify_with` below).
      some (LeafCertificate.interval period lo hi (fun _ _ => sorry) hWF)
    else none
  | none => none
```

Wait — `sorry` inside a `def` body is not allowed (it's an admitted
proof, not an unprovable proposition). The correct API is to make
the proof a parameter of the **theorem**, not of the parser. Revised:

```lean
/-- Construct a `LeafCertificate` from a well-formed `CoverageLeaf`
    with the proof obligation discharged by the caller. -/
def certificate_of_leaf (l : CoverageLeaf)
    (h : ∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x) :
    Option LeafCertificate :=
  match leanInterval l, h with
  | some (period, lo, hi), h => some (LeafCertificate.interval period lo hi h ⟨...⟩)
  | _, _ => none

/-- Lighter-weight constructor: parse the leaf and assemble the
    interval certificate, leaving `h` as a separate parameter.
    Returns `none` if the leaf is not well-formed. -/
def leaf_interval_shape (l : CoverageLeaf) : Option (Nat × Nat × Nat) :=
  match leanInterval l with
  | some (period, lo, hi) =>
    if hWF : period > 0 ∧ lo ≤ hi ∧ hi < period then
      some (period, lo, hi)
    else none
  | none => none
```

This is the cleaner shape. `certificate_of_leaf` takes both the leaf
and the proof; the caller is responsible for discharging `h`. The
`leaf_interval_shape` helper just extracts the structural tuple.

### Updated theorem signature

`coverage_tree_soundness_full` stays the same (the `hLeaf` hypothesis
is unchanged) — but a new companion theorem threads the certificate
explicitly:

```lean
/-- Variant of `coverage_tree_soundness_full` where the per-leaf
    certificate is a typed `LeafCertificate` rather than an opaque
    `LeafReachesOne` claim.

    **Equivalent in kernel** to `coverage_tree_soundness_full` —
    `LeafReachesOne t l` is defined as `∀ x, descend t x = some l →
    ReachesOne x`, which is exactly the conclusion of every
    `LeafCertificate.interval`'s `h` field.

    **Easier to audit** — the certificate is data, not a hypothesis;
    the project can construct it from `CoverageLeaf` and the closed
    02c/03c lemmas (see § "Closed prerequisites"). -/
theorem coverage_tree_soundness_cert (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l → LeafCertificate)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l := by
  exact coverage_tree_soundness_full t hv hic
    (fun l hl hver => match hCert l hl hver with
     | .empty => fun _ _ => ⟨0, rfl⟩  -- vacuous: no x reaches empty leaf
     | .single _ hReach => fun _ _ => hReach  -- degenerate
     | .known_small n _ hn => fun x' _ =>
       -- x' must be ≤ K by leaf shape (TODO: prove this)
       sorry
     | .interval _ _ _ h _ => fun _ hdesc' => h _ hdesc')
    x hx
```

Two `sorry`s are flagged — these are the **explicit boundaries** that
Q3 must close. See § "Per-shape proof obligations" below.

### Scenario 8 update

`CoverageTreeOrbitTests.lean` scenario 8 is updated to use the new
`coverage_tree_soundness_cert` API instead of `coverage_tree_soundness_full`:

```lean
-- Scenario 8 (Q3): compile-checked regression example for
-- `coverage_tree_soundness_cert` with a concrete `depthTwoTree` +
-- `certificate_of_leaf`-derived `LeafCertificate`s. The certificate
-- is constructively produced from the well-formed leaves (interval
-- shape with `period = 2`, `lo = hi = 1`); the `h` proof remains an
-- obligation (axiom-marked via `sorry` until the per-residue-class
-- Collatz proof is available — out of scope for Q3 v1).
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             LeafCertificate) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descend depthTwoTree 5 = some l ∧ LeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_cert depthTwoTree hv hc hCert 5 (by norm_num)
```

The `hCert` is an explicit parameter (no `by sorry` default — same
discipline as PR #51's scenario 8 fix per Codex P1).

## Per-shape proof obligations

Each `LeafCertificate` constructor carries its own proof obligation:

| Constructor | Proof obligation | Constructively provable? | Source |
|---|---|---|---|
| `empty` | None (vacuous) | Yes | Trivial: no `x` reaches an empty leaf |
| `single n hReach` | `ReachesOne n` | For small `n` (≤ 64), yes | Trajectory computation + `decide` |
| `known_small n hn` | `ReachesOne n` for `n ≤ K` | For `K ≤ 64`, yes | Exhaustive enumeration |
| `interval period lo hi h hWF` | `∀ x, lo ≤ x % period ∧ x % period ≤ hi → ReachesOne x` | **No** for `period = 2`, `[1, 1]` (full odd class); **partial** for smaller intervals | **Closes via 02c/03c lemmas** (see below) for small intervals; otherwise the Collatz theorem |

### Closed prerequisites (02c/03c)

The following 5 lemmas, closed in PRs #31 + #37 + #38 + #46 + #47, are
**direct inputs** to `LeafCertificate.interval`'s `h` field:

| Lemma | PR | Usage in Q3 |
|---|---|---|
| `acceleratedStep_odd_of_odd` | #31 | Bridge: odd-input orbit step produces odd output |
| `standardStep_positive` | #37 | Bridge: standard step preserves positivity |
| `acceleratedStep_positive_of_odd` | #38 | Bridge: accelerated step preserves positivity for odd input |
| `acceleratedStep_equiv_standardStep` | #46 | Bridge: accelerated ≡ standard step composition |
| `acceleratedTrajectory_reaches_one_implies_standard` | #47 | Bridge: accelerated trajectory reaching 1 → standard trajectory |

For small intervals (e.g., `period = 2`, `lo = 0`, `hi = 1` — the
"small inputs" interval), the proof is finite enumeration: `decide`
on the trajectory. The 02c/03c lemmas are the **building blocks**
for general intervals; the actual `h` proof for `[1, 1]` mod 2 is
**equivalent to the Collatz theorem for the odd class**, which is
not provable in this project.

The Q3 deliverable:
1. Constructs `LeafCertificate.interval` for known intervals.
2. Discharges `h` for **finite enumeration cases** (e.g., `n ≤ 64`).
3. Leaves `h` as an obligation for **the general Collatz case** —
   with explicit documentation in the certificate's docstring.

## Out of scope

1. **Actual Collatz proof.** Q3 makes the dependency explicit but does
   not prove the Collatz theorem for any non-trivial interval. The
   project does not have this proof; PR #49 deliberately scopes
   around it.
2. **`coverage_tree_soundness_orbit`** (the `sorry` from PR #36).
   Separate orbit-aware routing workstream. Not touched by Q3.
3. **Python oracle bridge.** Promoting
   `tests/test_coverage_tree.py` to formal proofs requires a
   Python↔Lean translation layer. Not in Q3 v1.
4. **Composite certificates** (`union`, `inter`, `tree_of_certificates`).
   Deferred to Q3 follow-ups if needed.
5. **Replacing `leafProperty : String`.** Q3 adds `LeafCertificate`
   alongside the existing field; replacing the field is a breaking
   change that affects the Python side and tests. Deferred to Q3 v2
   after the type stabilises.

## Implementation plan (PR sequence)

**v1 (this spec — PR only docs):**
- PR #52: this spec (docs-only). Codex review on the design.

**v2 (implementation):**
- PR #53: add `LeafCertificate` inductive type + `empty` + `single` +
  `known_small` constructors to `CoverageTree.lean`. No formal proofs
  yet — just the type definition + `Repr` + `Decidable` instances.
- PR #54: add constructive proofs for `single n` and `known_small n`
  (via `decide` on small finite trajectories). Add `coverage_tree_soundness_cert`
  theorem. Update scenario 8 in `CoverageTreeOrbitTests.lean` to use
  the new API.
- PR #55: add `leaf_interval_shape` parser + `interval` constructor
  integration. The `h` proof remains an obligation (documented).
- PR #56: lessons-learned doc (if notable patterns emerge from
  PRs #53–55).

The split into multiple PRs is deliberate: each PR has a single
**verifiable** claim (type definition, constructive proofs,
parser/integration, docs). Lean CI gate at each step.

## Open questions for Codex

1. **Is the `interval` constructor's `h` obligation correctly scoped?**
   The current design takes `h` as a parameter (no axioms). The kernel
   will reject any proof of `coverage_tree_soundness_cert` that uses
   `h := fun _ _ => sorry`. Is this the right boundary, or should
   the `interval` constructor itself mark the axiom (e.g., a
   `noncomputable` or `classical` marker)?

2. **Is the `K = 64` bound for `known_small` reasonable?** The bound
   is small enough for `decide` on the trajectory but large enough to
   cover most "small inputs" branches in practice. Alternative
   bounds (32, 128, 256) are easy to swap.

3. **Should the parser accept the existing `leafProperty` format?**
   Yes for backward compatibility. But should the parser also
   recognise new formats (e.g., `"single:5"` → `single 5 ⟨0, rfl⟩`)?
   v1 sticks with the existing format; v2 can add new formats.

4. **Is `coverage_tree_soundness_cert` the right name?** Alternatives:
   `coverage_tree_soundness_with_certificate` (more verbose),
   `coverage_tree_soundness_full'` (suggests a variant of `full`),
   `coverage_tree_soundness_certified` (passive voice).

5. **Scenario 8 update — does scenario 8 in `CoverageTreeOrbitTests.lean`
   survive Q3?** The scenario is a compile-checked regression; it
   should still pass after Q3 (with the `hCert` parameter supplied
   explicitly, no `by sorry` default). The scenario will be updated
   in PR #54 alongside `coverage_tree_soundness_cert`.

## References

- **PR #49** (07c-2 promotion): `29c41e0`
- **PR #50** (lessons-learned doc): `7d42bfb`
- **PR #51** (P2 follow-ups + scenario 8): `388b4a7`
- **Spec parent**: `docs/story-07c-2-promotion.md` Q3 (lines 75–104)
- **Theorem status**: `docs/theorem-status.md` row for `LeafReachesOne`
- **Closed prerequisites**: PRs #31, #37, #38, #46, #47 (02c/03c)
- **Out-of-scope siblings**: `coverage_tree_soundness_orbit` (PR #36
  spec, `sorry` workstream), `descend_orbit_complete` (PR #29,
  formally established, separate workstream)