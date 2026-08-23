/-
Coverage trees (Story 07b / round-4, M4 Finite coverage) — REVISED.

After Codex re-review on commit a3f7127 (review 4922482533,
submitted 2026-08-13T00:57:51Z) + CI run 31657397630:

- **P0 (merge-blocking):** the proof used
  `induction depth using Nat.rec generalizing n with` — but `n` is not
  in scope at the induction site, so the parser raised
  `unknown identifier 'n'` at line 140.
  Codex's recommendation: use induction on an explicit `d : Nat` with
  the helper shape `∀ d n, ValidNode d n → IsCompleteAux t n → ...
  descendFrom d n ...`; base `d = 0` eliminates internal nodes via
  `ValidNode` (since `ValidNode 0 (.internal _) = False`); successor
  internal case invokes IH at `d` using child validity from
  `ValidNode (d+1)`.

- **P1 (parser):** `section regression` keyword wasn't being parsed
  correctly in this Lean version. Once the theorem is rewritten to a
  complete syntactic proof, the `section` issue resolves; the
  examples are now placed outside any `section` wrapper.

This commit applies Codex's full recommendation:

1. **Helper without `depth > 0` precondition.** Drops the positive-
   depth premise; the base case (`d = 0`) eliminates internal nodes
   via `ValidNode 0 (.internal _) = False` and the leaf case uses
   `descendFrom 0 (.leaf l) _ = some l` directly.
2. **Dropped `generalizing n` from `Nat.rec`.** The motive is implicit;
   `n` is introduced inside each case via `intro n hvn hic x hx`.
3. **`cases n` (not `induction n`) on `CoverageNode`.** Plain
   pattern matching avoids the nested-inductive elimination issue.
4. **`False.elim hvn` in the base-case internal branch.** The
   contradiction `ValidNode 0 (.internal _) = False` discharges the
   goal via ex falso.
5. **Removed `section regression` wrapper.** The regression examples
   stand alone in the namespace.

Claim level remains `preparatory` per the v2 github-pr-workflow
skill (see ed80287 demotion rationale; promotion criteria still
require a semantic leafProperty-indexed predicate + proof that
descend lands a satisfying witness).

Mirrored by Python `tree.py` regression test for the same depth
cases (`tests/test_coverage_tree.py`).
-/

import Mathlib.Data.String.Lemmas
import CollatzResearch.Basic
import CollatzResearch.Dynamics
import CollatzResearch.Equivalence

namespace CollatzResearch

/-- A leaf in the coverage tree. -/
structure CoverageLeaf where
  leafId : String
  leafProperty : String
  deriving Repr

/-- A node: either a leaf or an internal node carrying a modulus and a
    list of `(residue, child)` pairs (sorted by residue ascending). -/
inductive CoverageNode : Type where
  | leaf (l : CoverageLeaf)
  | internal (modulus : Nat) (children : List (Nat × CoverageNode))
  deriving Repr

/-- A coverage tree: a root `CoverageNode` + the top-level descriptor list. -/
structure CoverageTree where
  root : CoverageNode
  leaves : List CoverageLeaf
  maxDepth : Nat
  deriving Repr

/-- A partition is valid: residues are in `[0, m)`, distinct, sorted ascending. -/
def ValidPartition (modulus : Nat) (children : List (Nat × α)) : Prop :=
  (∀ p ∈ children, p.1 < modulus) ∧
  children.Pairwise (fun a b => a.1 < b.1)

/-- A coverage node is well-formed at the given `depth`. A leaf is
    always valid; an internal node requires positive modulus, a valid
    partition, and all children valid at depth-1. -/
def ValidNode : Nat → CoverageNode → Prop
  | _, .leaf _ => True
  | depth + 1, .internal m children =>
    m > 0 ∧ ValidPartition m children ∧
    (∀ c ∈ children, ValidNode depth c.2)
  | 0, .internal _ _ => False

/-- A coverage tree is well-formed: depth is positive and root is valid. -/
def ValidTree (t : CoverageTree) : Prop :=
  t.maxDepth > 0 ∧ ValidNode t.maxDepth t.root

/-- Leaf-first descent: a leaf is always reachable (returns `some l`
    regardless of remaining depth); depth only governs internal
    recursion. At depth 0 on an internal node, returns `none` (depth
    exhausted).

    Mirrors Python `tree.descend` (Story 07b / round-4 regression). -/
def descendFrom : Nat → CoverageNode → Nat → Option CoverageLeaf
  | _, .leaf l, _ => some l
  | 0, .internal _ _, _ => none
  | depth + 1, .internal m children, x =>
    let r := x % m
    match children.lookup r with
    | some child => descendFrom depth child x
    | none => none

/-- descend: walk down the tree from root. -/
def descend (t : CoverageTree) (x : Nat) : Option CoverageLeaf :=
  descendFrom t.maxDepth t.root x

/-- The accelerated orbit: `accelerated_orbit n 0 = n`,
    `accelerated_orbit n (k+1) = acceleratedStep (accelerated_orbit n k)`.
    (Story 07c / round-5, 07c-2.) -/
def accelerated_orbit : Nat → Nat → Nat
  | n, Nat.zero => n
  | n, k + 1 => acceleratedStep (accelerated_orbit n k)

/-- `@[simp]` lemma so `simp` can unfold `accelerated_orbit n 0` to `n`
    (the base case). Needed by executable-spec reductions where the
    recursive computation must fully close at concrete inputs. -/
@[simp] theorem accelerated_orbit_zero (n : Nat) : accelerated_orbit n 0 = n := rfl

/-- `@[simp]` lemma so `simp`/`rw` can unfold `accelerated_orbit n (k + 1)`
    to `acceleratedStep (accelerated_orbit n k)` (the inductive step).
    Companion to `accelerated_orbit_zero`. NEW Q4 v3 / PR #56 —
    needed by `accelerated_orbit_compose` (induction on `k'` uses
    `rw [accelerated_orbit_succ]` on both sides of the goal). -/
@[simp] theorem accelerated_orbit_succ (n k : Nat) :
    accelerated_orbit n (k + 1) = acceleratedStep (accelerated_orbit n k) := rfl

/-- Orbit-additive composition: stepping forward by `k + k'` equals
    stepping forward by `k` then by `k'` more. Proof by induction on
    `k'` (the outer index, NOT `k`); the IH directly matches the
    post-`rw` goal after both sides are unfolded with `accelerated_orbit_succ`.

    This is the elementary orbit-composition lemma: stepping forward
    by `k + k'` is the same as stepping forward by `k` then by `k'`
    more. It is the foundation for `orbit_predecessor_reaches_one`,
    which is in turn the "close the orbit" step of the Q4 v3 companion
    theorem's proof. NEW Q4 v3 / PR #56 — the actual Q4 mechanism;
    without it PR #58 cannot establish the advertised
    `coverage_tree_soundness_orbit_cert` theorem.

    (Story Q4 v3 / PR #56.) -/
theorem accelerated_orbit_compose (x : Nat) (k k' : Nat) :
    accelerated_orbit x (k + k') = accelerated_orbit (accelerated_orbit x k) k' := by
  induction k' with
  | zero =>
    rw [Nat.add_zero, accelerated_orbit_zero]
  | succ k' ih =>
    rw [Nat.add_succ, accelerated_orbit_succ, accelerated_orbit_succ, ih]

/-- `ReachesOne n` iff applying `acceleratedStep` repeatedly to `n`
    eventually reaches 1. (Story 07c / round-5, 07c-2.) -/
def ReachesOne (n : Nat) : Prop := ∃ k, accelerated_orbit n k = 1

/-- Orbit-predecessor closure: if some future state of `x`'s orbit
    reaches 1, then `x` reaches 1. Built on `accelerated_orbit_compose`.

    Proof sketch: given `accelerated_orbit x k = y` and `ReachesOne y`
    (i.e., `∃ k', accelerated_orbit y k' = 1`), compose via
    `accelerated_orbit_compose` to get `accelerated_orbit x (k + k') = 1`,
    so `ReachesOne x`.

    This is the "close the orbit" lemma: any future orbit state that
    reaches 1 propagates reachability back to the original input.
    NEW Q4 v3 / PR #56 — the Q4 mechanism's final composition step.
    PR #58's `coverage_tree_soundness_orbit_cert` proof uses this
    lemma as the closing step after `cert.claim_reaches_one` derives
    `ReachesOne (accelerated_orbit x' k)`.

    Placed after `def ReachesOne` so the `ReachesOne` references in
    the type signature resolve; each declaration follows its
    dependencies. PR history (v1→v2→v3 forward-reference fixes)
    lives in the PR #56 squash-merge commit body.

    (Story Q4 v3 / PR #56.) -/
theorem orbit_predecessor_reaches_one (x : Nat) (k : Nat) (y : Nat)
    (h_eq : accelerated_orbit x k = y) (h_reaches : ReachesOne y) :
    ReachesOne x := by
  obtain ⟨k', hk'⟩ := h_reaches
  exact ⟨k + k', by rw [accelerated_orbit_compose, h_eq, hk']⟩

/-- `LeafReachesOne t l` is a leaf-level semantic certificate: any
    starting `x` that descends to leaf `l` under `descend t` reaches
    1 via the accelerated orbit. The certificate is the leaf's
    semantic content; `coverage_tree_soundness` only proves the tree
    routes correctly. Promoting the global Collatz convergence claim
    would require proving `LeafReachesOne` for every verified leaf in
    some certified partition (see `docs/story-07c-2-promotion.md`
    Q3 — structured certificate design). (Story 07c / round-5, 07c-2.) -/
def LeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descend t x = some l → ReachesOne x

/-- Orbit-aware descent: at each internal level, the residue lookup
    uses `accelerated_orbit x k % m` instead of `x % m`, where `k` is
    the depth index (incremented at each internal step). Structural
    recursion matches `descendFrom`; only the residue computation is
    orbit-aware. (Story 07c / round-5, 07c-3.) -/
def descendFromOrbit : Nat → CoverageNode → Nat → Nat → Option CoverageLeaf
  | _, .leaf l, _, _ => some l
  | 0, .internal _ _, _, _ => none
  | depth + 1, .internal m children, x, k =>
    let r := accelerated_orbit x k % m
    match children.lookup r with
    | some child => descendFromOrbit depth child x (k + 1)
    | none => none

/-- Orbit-aware descent entry point. -/
def descendOrbit (t : CoverageTree) (x : Nat) (k : Nat) : Option CoverageLeaf :=
  descendFromOrbit t.maxDepth t.root x k

/-- Orbit-routing leaf-level semantic predicate, parallel to
    `LeafReachesOne` (which is defined over the residue-only router
    `descend`). `OrbitLeafReachesOne t l` asserts: every input `x`
    that the orbit-aware router `descendOrbit` selects for leaf `l`
    reaches 1 via the accelerated orbit.

    This is the predicate concluded by
    `coverage_tree_soundness_orbit_cert` (PR #58 deliverable). It is
    **NOT** interchangeable with `LeafReachesOne t l` — the two certify
    different routing relations (orbit-aware vs residue-only).

    NEW Q4 v3 / PR #56 — required to resolve the routing-relation
    mismatch in the v2 companion theorem (which concluded
    `LeafReachesOne t l` over `descendOrbit` routing). The v3 spec
    (PR #55) concludes `OrbitLeafReachesOne t l` instead, so the
    theorem conclusion type matches the routing evidence used in
    the proof (per Codex run-21848 P1 review on PR #55).

    Placed after `def descendOrbit` (and after `def ReachesOne` via
    the v2 fix on `orbit_predecessor_reaches_one`) so the body's
    `descendOrbit t x 0 = some l → ReachesOne x` references resolve;
    each declaration follows its dependencies. PR history
    (v1→v2→v3 forward-reference fixes) lives in the PR #56
    squash-merge commit body.

    (Story Q4 v3 / PR #56.) -/
def OrbitLeafReachesOne (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  ∀ x, descendOrbit t x 0 = some l → ReachesOne x

/-- The root domain: defined INDEPENDENTLY of `descend` (per Codex P0). -/
def rootDomain : Nat → Prop := fun n => n > 0

/-- At an internal node, every residue in `[0, m)` has a child. -/
def HasAllResidues (m : Nat) (children : List (Nat × α)) : Prop :=
  m > 0 ∧ (∀ r, r < m → (children.lookup r).isSome)

/-- A verified leaf: it's in `t.leaves` and both `leafId` and
    `leafProperty` are non-empty. -/
def verified (t : CoverageTree) (l : CoverageLeaf) : Prop :=
  l ∈ t.leaves ∧ l.leafProperty ≠ "" ∧ l.leafId ≠ ""

/-- Parse the leaf's declared interval: `"<period>:<lo>-<hi>"` →
    `Option (Nat × Nat × Nat)`. Strict format; returns `none` on any
    deviation. (Story 07c / round-5, 07c-1.) -/
def leanInterval (l : CoverageLeaf) : Option (Nat × Nat × Nat) :=
  match (l.leafProperty.split (· = ':')).toList.map (·.toString) with
  | [periodStr, rangeStr] =>
    match (rangeStr.split (· = '-')).toList.map (·.toString) with
    | [loStr, hiStr] =>
      match periodStr.toNat?, loStr.toNat?, hiStr.toNat? with
      | some period, some lo, some hi => some (period, lo, hi)
      | _, _, _ => none
    | _ => none
  | _ => none

/-- Semantic predicate: `x` is in the leaf's declared interval.
    The leaf declares a `(period, lo, hi)` tuple via `leanInterval`;
    `x` is in the interval iff `x % period ∈ [lo, hi]`.
    (Story 07c / round-5, 07c-1.) -/
def Sat (_t : CoverageTree) (x : Nat) (l : CoverageLeaf) : Prop :=
  match leanInterval l with
  | some (period, lo, hi) => lo ≤ x % period ∧ x % period ≤ hi
  | none => False

instance Sat.decidable (t : CoverageTree) (x : Nat) (l : CoverageLeaf) :
    Decidable (Sat t x l) := by
  unfold Sat
  cases h : leanInterval l with
  | none => infer_instance
  | some interval =>
      cases interval with
      | mk period rest =>
          cases rest with
          | mk lo hi => infer_instance

/-- Static property of a leaf: its declared interval is structurally
    valid. The interval is a residue range modulo `period`: we need
    `period > 0`, `lo ≤ hi`, and `hi < period` (which also forces
    `lo < period`). Without `hi < period`, e.g. `3:0-100` would make
    `Sat` trivially true for every residue. (Story 07c / round-5, 07c-1.) -/
def WellFormed (l : CoverageLeaf) : Prop :=
  match leanInterval l with
  | some (period, lo, hi) => period > 0 ∧ lo ≤ hi ∧ hi < period
  | none => False

instance WellFormed.decidable (l : CoverageLeaf) : Decidable (WellFormed l) := by
  unfold WellFormed
  cases h : leanInterval l with
  | none => infer_instance
  | some interval =>
      cases interval with
      | mk period rest =>
          cases rest with
          | mk lo hi => infer_instance

/-- Orbit-aware semantic predicate: `x`'s accelerated orbit reaches
    the leaf's declared interval at some step `k`. (Story 07c /
    round-5, 07c-3.) Decidable instance is intentionally omitted —
    the existential over `k` is unbounded, so no finite instance
    exists. Downstream code uses this for proof obligations, not for
    `decide`. -/
def SatOrbit (_t : CoverageTree) (x : Nat) (l : CoverageLeaf) : Prop :=
  match leanInterval l with
  | some (period, lo, hi) =>
      ∃ k, lo ≤ accelerated_orbit x k % period ∧
           accelerated_orbit x k % period ≤ hi
  | none => False

/-- A claim about which inputs reach a leaf. Pure data — equality-
    comparable, serializable, no proof content. The Lean proof that
    the claim holds for the routed inputs (and that every claimed
    input reaches 1) is in `LeafCertificate` (PR #54).

    **Q3 v3 scope:** `.interval` is the only **structurally
    plausible claim shape** under current `descend` semantics
    (residue-only routing), pending a dedicated alignment
    invariant that will be defined in PR #54. The other
    constructors (`.empty`, `.singleton`, `.bounded`) are kept
    in the type for forward compatibility with the
    bounded-orbit workstream (depends on `descend_orbit_complete`
    from PR #29 + `coverage_tree_soundness_orbit` from PR #36
    spec). See `docs/story-q3-leaf-certificate.md`
    § "Why finite claims are out of Q3 scope".

    No `routed_implies_claim` proof exists for any claim shape
    yet — the structural `descend t x = some l → claim.Holds x`
    obligation requires an alignment invariant that is not yet
    formalized. Finite claims (`.empty`, `.singleton`,
    `.bounded`) additionally require the future orbit-reduction
    relation (`descendOrbit` + bounded orbit images).

    (Story Q3 / PR #53.) -/
inductive LeafClaim where
  | empty                       -- no inputs
  | singleton (n : Nat)         -- exactly one input: n
  | bounded (K : Nat)           -- inputs ≤ K (finite enumeration)
  | interval (period lo hi : Nat)  -- residue interval [lo, hi] mod period
  deriving Repr, DecidableEq

namespace LeafClaim

/-- The set of inputs claimed by a `LeafClaim`. Pure predicate. -/
def Holds (c : LeafClaim) (x : Nat) : Prop :=
  match c with
  | .empty => False
  | .singleton n => x = n
  | .bounded K => x ≤ K
  | .interval period lo hi => lo ≤ x % period ∧ x % period ≤ hi

/-- Decidability instance for `LeafClaim.Holds`. Cases:
    - `.empty` → `Decidable False`
    - `.singleton n` → `Decidable (x = n)` via `Nat.decEq`
    - `.bounded K` → `Decidable (x ≤ K)` via `Nat.decLe`
    - `.interval period lo hi` → `Decidable (lo ≤ x % period ∧ x % period ≤ hi)`
      via `And.decidable` composed with `Nat.decLe`. -/
instance Holds.decidable (c : LeafClaim) (x : Nat) :
    Decidable (c.Holds x) := by
  unfold Holds
  cases c with
  | empty => exact (inferInstance : Decidable False)
  | singleton n => exact (inferInstance : Decidable (x = n))
  | bounded K => exact (inferInstance : Decidable (x ≤ K))
  | interval period lo hi =>
    exact (inferInstance : Decidable (lo ≤ x % period ∧ x % period ≤ hi))

/-- Well-formedness for a `LeafClaim` (data-level invariant):
    - `.empty`, `.singleton n`, `.bounded K` are always well-formed.
    - `.interval period lo hi` requires `period > 0 ∧ lo ≤ hi ∧ hi < period`
      (same conjunction as the existing `WellFormed` predicate on
      `CoverageLeaf`, kept in sync).

    `parse_leaf_claim` already enforces this invariant via the
    existing `WellFormed l` guard (so parsed claims satisfy
    `LeafClaim.WellFormed`), but the public `LeafClaim` constructor
    still permits malformed values like `.interval 0 0 0` or
    `.interval 2 2 1` to be constructed directly. The forthcoming
    `LeafCertificate t l` Prop (PR #54) should require
    `LeafClaim.WellFormed` as an explicit field so that a certificate
    cannot carry a malformed/noncanonical claim.

    Per Codex P2 at PR #53 review run 199 (2026-08-22T00:13:50Z):
    "Define a claim well-formedness predicate before PR #54."

    (Story Q3 / PR #53 v2.) -/
def WellFormed : LeafClaim → Prop
  | .empty => True
  | .singleton _ => True
  | .bounded _ => True
  | .interval period lo hi => period > 0 ∧ lo ≤ hi ∧ hi < period

instance WellFormed.decidable (c : LeafClaim) : Decidable c.WellFormed := by
  cases c with
  | empty => exact (inferInstance : Decidable True)
  | singleton _ => exact (inferInstance : Decidable True)
  | bounded _ => exact (inferInstance : Decidable True)
  | interval period lo hi =>
    exact (inferInstance : Decidable (period > 0 ∧ lo ≤ hi ∧ hi < period))

end LeafClaim

/-- A claim about which **orbit states** reach a leaf, restricted to
    finite shapes. The `.interval` constructor (from `LeafClaim`) is
    intentionally omitted — interval claims are residue-only routing
    territory (Q3 v4 `LeafCertificate`), not orbit-aware routing
    territory (Q4 v3 `BoundedOrbitCertificate`).

    `Holds y` is interpreted as `y` being an **orbit state** (a value
    `accelerated_orbit x k` for some `k : Nat`), NOT the original
    routing input `x` directly. This orbit-state-relative shape is
    what makes finite claims constructively inhabitable under
    `descendOrbit`.

    Equality-comparable, serializable. `DecidableEq` via `deriving`.
    Sibling to `LeafClaim` (Q3 v4 data layer); the two types are
    independent — `FiniteOrbitClaim` excludes `.interval` by
    construction; `LeafClaim` retains `.interval` for residue-only
    routing.

    (Story Q4 / PR #57.) -/
inductive FiniteOrbitClaim where
  | empty                       -- no orbit states
  | singleton (n : Nat)         -- exactly one orbit state: n
  | bounded (K : Nat)           -- orbit state ≤ K (finite enumeration)
  deriving Repr, DecidableEq

namespace FiniteOrbitClaim

/-- Set-membership predicate on `Nat` for a `FiniteOrbitClaim`.
    `Holds y` is interpreted as "y is an orbit state reachable from
    some input routed to this leaf, AND y is claimed to reach 1".

    Note: `y` is a `Nat` value that the **caller** interprets as an
    orbit state (e.g., `accelerated_orbit x k` for some `k`); the
    predicate itself is just a structural match. -/
def Holds (c : FiniteOrbitClaim) (y : Nat) : Prop :=
  match c with
  | .empty => False
  | .singleton n => y = n
  | .bounded K => y ≤ K

/-- Decidability instance for `FiniteOrbitClaim.Holds`. Per-
    constructor dispatch:
    - `.empty` → `Decidable False`
    - `.singleton n` → `Decidable (y = n)` via `Nat.decEq`
    - `.bounded K` → `Decidable (y ≤ K)` via `Nat.decLe`

    Uses `cases c with` form (mirrors `LeafClaim.Holds.decidable`).
    `.interval` is structurally excluded by `FiniteOrbitClaim`'s
    constructor set. -/
instance Holds.decidable (c : FiniteOrbitClaim) (y : Nat) :
    Decidable (c.Holds y) := by
  unfold Holds
  cases c with
  | empty => exact (inferInstance : Decidable False)
  | singleton n => exact (inferInstance : Decidable (y = n))
  | bounded K => exact (inferInstance : Decidable (y ≤ K))

/-- `IsFiniteClaim : LeafClaim → Prop` predicate. Returns `True` for
    the three finite constructors (`.empty`, `.singleton n`,
    `.bounded K`) and `False` for `.interval`.

    Reusable across Q3/Q4 boundaries: any code that needs to check
    "is this `LeafClaim` finite-shaped?" can call this predicate
    without committing to the orbit-routing machinery. Companion
    decidability instance enables `decide` for closed `LeafClaim`
    values.

    (Story Q4 / PR #57.) -/
def IsFiniteClaim : LeafClaim → Prop
  | .empty => True
  | .singleton _ => True
  | .bounded _ => True
  | .interval _ _ _ => False

/-- Decidability instance for `IsFiniteClaim`. Per-constructor
    dispatch:
    - `.empty`, `.singleton _`, `.bounded _` → `Decidable True`
    - `.interval _ _ _` → `Decidable False`

    Uses the explicit `cases c with` form (matching
    `LeafClaim.WellFormed.decidable` for `LeafClaim`, which uses
    the same form) rather than the equations-form `| .empty =>
    inferInstance | ...` from the Q4 v3 spec sketch. The reason:
    equations-form doesn't unfold `IsFiniteClaim c` to `True` /
    `False` before invoking `inferInstance`, so the bare
    `inferInstance` (without explicit type annotation) cannot
    resolve `Decidable (IsFiniteClaim .empty)` — it sees
    `Decidable (IsFiniteClaim .empty)` and tries to find an
    instance for that unreduced type, failing because no such
    instance exists (only `Decidable True` and `Decidable False`
    are core instances). The `cases c with` form unfolds
    `IsFiniteClaim c` via pattern matching, and the explicit
    `(inferInstance : Decidable True)` /
    `(inferInstance : Decidable False)` annotations tell
    `inferInstance` which core instance to look for.

    Uses `cases c with` + explicit `Decidable True/False`
    annotations on `inferInstance`, matching
    `LeafClaim.WellFormed.decidable` style. -/
instance IsFiniteClaim.decidable (c : LeafClaim) :
    Decidable (IsFiniteClaim c) := by
  cases c with
  | empty => exact (inferInstance : Decidable True)
  | singleton _ => exact (inferInstance : Decidable True)
  | bounded _ => exact (inferInstance : Decidable True)
  | interval _ _ _ => exact (inferInstance : Decidable False)

end FiniteOrbitClaim

/-- Untrusted structural decoder: parses a `CoverageLeaf`'s
    `leafProperty` into a `LeafClaim` (data only). Does NOT
    construct the Lean proof. The proof is supplied by the caller.

    **Q3 v3 scope:** the decoder recognises only the existing
    `"<period>:<lo>-<hi>"` format (via `leanInterval`) and produces
    the `.interval` claim. Other claim shapes (`.singleton`,
    `.bounded`) require new `leafProperty` formats and are
    deferred. The `WellFormed` guard ensures the interval is
    structurally valid (modulo the conjunction `period > 0 ∧
    lo ≤ hi ∧ hi < period`).

    **Critical:** this is a STRUCTURAL DECODER, not a SEMANTIC
    DECODER. It must never be used to manufacture semantic
    evidence. The `leafProperty` string is an untrusted input;
    the caller is responsible for verifying the resulting claim's
    semantic obligations (`routed_implies_claim` +
    `claim_reaches_one`, defined in PR #54).

    (Story Q3 / PR #53.) -/
def parse_leaf_claim (l : CoverageLeaf) : Option LeafClaim :=
  match leanInterval l with
  | some (period, lo, hi) =>
    if hWF : WellFormed l then
      some (LeafClaim.interval period lo hi)
    else none
  | none => none

/-- A structured certificate that a leaf `l` in tree `t` carries
    to prove `LeafReachesOne t l`. The certificate has two
    distinct obligations:

    1. `routed_implies_claim`: every input routed to `l` satisfies
       the claim. (Routing-to-claim obligation.)
    2. `claim_reaches_one`: every input satisfying the claim
       reaches 1. (Reachability obligation.)

    Composing these gives `LeafReachesOne t l`.

    The `well_formed` field enforces `LeafClaim.WellFormed` so
    that direct construction of `.interval 0 0 0` or `.interval
    2 2 1` etc. cannot slip through as a purported certificate.
    Per Codex P2 at PR #53 review run 199
    (2026-08-22T00:13:50Z): "Define a claim well-formedness
    predicate before PR #54" — now enforced as a mandatory field.

    `parse_leaf_claim` already produces well-formed claims (it
    gates on the existing `WellFormed l` predicate, which
    matches `LeafClaim.WellFormed` for the `.interval` case), so
    parsed claims satisfy this field trivially.

    **Sort rationale (`: Type`, not `: Prop`).** The `claim` field is
    `Type`-valued (`LeafClaim` is data). Lean 4 rejects `Type`-valued
    fields in `: Prop`-valued structures (Prop structures cannot carry
    data fields). The two obligation fields are still `Prop`s, so the
    kernel still verifies them — only the structure's outer sort is
    `Type`. This makes `LeafCertificate t l` a **proof-carrying data
    bundle**: inspectable data (`claim`, `well_formed`) plus
    kernel-checked proof fields (`routed_implies_claim`,
    `claim_reaches_one`). It is **NOT** proof-irrelevant evidence;
    the structure is intended to be constructed, pattern-matched on,
    and projected through.

    The companion theorem `coverage_tree_soundness_cert` takes
    `(hCert : ∀ l ∈ t.leaves, verified t l → LeafCertificate t l)`
    as an **explicit** hypothesis (no default, no `by sorry`) per
    the project "no new sorry" discipline (PR #51 P1).

    (Story Q3 / PR #54.) -/
structure LeafCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : LeafClaim
  well_formed : claim.WellFormed
  routed_implies_claim :
    ∀ x, descend t x = some l → claim.Holds x
  claim_reaches_one :
    ∀ x, claim.Holds x → ReachesOne x

/-- A structured certificate that a leaf `l` in tree `t` carries to
    prove `OrbitLeafReachesOne t l` for a **finite**
    `FiniteOrbitClaim` shape (`.empty`, `.singleton n`, `.bounded K`).

    `: Type`-valued proof-carrying data bundle (NOT `: Prop`): the
    `claim : FiniteOrbitClaim` data field requires `Type`-valued sort
    (Lean 4 elaboration rejects `Type`-valued fields in `: Prop`
    structures). The two obligation fields remain `Prop`s and are
    kernel-checked.

    **Orbit-state-relative claim shape.** `orbit_hits_claim` asserts
    the routed input's orbit reaches a state satisfying the claim,
    NOT the original input. This is what makes finite claims
    constructively inhabitable under `descendOrbit`.

    **Two obligation fields:**
    1. `orbit_hits_claim`: every input routed (orbit-aware) to `l`
       reaches an orbit state satisfying the claim.
    2. `claim_reaches_one`: every orbit state satisfying the claim
       reaches 1.

    **NO `wellFormed` field.** The finite-shape restriction is
    enforced at the **type level** by `FiniteOrbitClaim`'s
    constructor set (which excludes `.interval`).
    `IsFiniteClaim : LeafClaim → Prop` is a separate reusable
    predicate (in `namespace FiniteOrbitClaim`) for code that needs
    to discriminate between finite vs `.interval` `LeafClaim`
    values, but is NOT carried as a certificate field.

    **Trust boundary.** This is proof-carrying data: a data field
    plus kernel-checked Lean proof fields. External computation
    (e.g., Python oracles) may propose witnesses but cannot
    construct `BoundedOrbitCertificate` as proof authority without
    Lean-checked proofs or a separately proved checker.

    **No `hCert` default, no `by sorry`.** The companion theorem
    `coverage_tree_soundness_orbit_cert` (PR #58 deliverable) takes
    `(hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l)`
    as an explicit hypothesis per the project "no new sorry"
    discipline (PR #51 P1).

    **Companion to `LeafCertificate`.** NO mutual exclusion — a leaf
    can carry both `LeafCertificate t l` (Q3 v4, residue-only routing)
    and `BoundedOrbitCertificate t l` (Q4 v3, orbit-aware routing) as
    independent views of its semantic content. They conclude different
    leaf-level predicates (`LeafReachesOne t l` vs
    `OrbitLeafReachesOne t l`) and certify different routing
    relations (`descend` vs `descendOrbit`).

    Inserted after `LeafCertificate` (all deps in scope).

    API-shape regression: `def boundedCertificateClaim` + polymorphic
    obligation projections in `FiniteOrbitClaimTests.lean`. -/
structure BoundedOrbitCertificate (t : CoverageTree) (l : CoverageLeaf) : Type where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y

/-- Structural alignment: every leaf's declared `period` matches the
    modulus of its parent internal node at the leaf's depth. Captures
    the invariant needed for `descendOrbit` to imply `SatOrbit`.
    (Story 07c / round-5, 07c-3.) Defined alongside `IsCompleteAux`
    so the two structural proofs can co-evolve. -/
inductive OrbitAlignedAux : CoverageNode → Prop where
  | leafA : ∀ (l : CoverageLeaf),
      WellFormed l →
      OrbitAlignedAux (.leaf l)
  | internalA : ∀ (m : Nat) (children : List (Nat × CoverageNode)),
      (∀ c ∈ children, OrbitAlignedAux c.2) →
      OrbitAlignedAux (.internal m children)

/-- A coverage tree is orbit-aligned: its root subtree is aligned. -/
def OrbitAlignedTree (t : CoverageTree) : Prop := OrbitAlignedAux t.root

/-- Structural completeness of a subtree (no `descend` in the definition). -/
inductive IsCompleteAux (t : CoverageTree) : CoverageNode → Prop where
  | leafC : ∀ (l : CoverageLeaf),
    l ∈ t.leaves → verified t l →
    IsCompleteAux t (.leaf l)
  | internalC : ∀ (m : Nat) (children : List (Nat × CoverageNode)),
    m > 0 →
    HasAllResidues m children →
    (∀ c ∈ children, IsCompleteAux t c.2) →
    IsCompleteAux t (.internal m children)

def IsComplete (t : CoverageTree) : Prop := IsCompleteAux t t.root

/-- An input satisfies a leaf's property: `descend t x` returns `l`. -/
def satisfies (t : CoverageTree) (x : Nat) (l : CoverageLeaf) : Prop :=
  descend t x = some l

/-- Orbit-aware routing relation (Story 07c-4).

    At an internal node with modulus `m` at orbit index `i`, the selected
    edge is labelled `accelerated_orbit x i % m`. A terminal node contains
    the returned leaf. The structural recursion mirrors `descendFromOrbit`. -/
inductive OrbitRoute (t : CoverageTree) (x : Nat) :
    Nat → CoverageNode → CoverageLeaf → Prop
  | leaf {i : Nat} {l : CoverageLeaf} :
      OrbitRoute t x i (.leaf l) l
  | internal {i : Nat} {m : Nat} {children : List (Nat × CoverageNode)}
      {child : CoverageNode} {l : CoverageLeaf}
      (hpair_mem : (accelerated_orbit x i % m, child) ∈ children)
      (hrest : OrbitRoute t x (i + 1) child l) :
      OrbitRoute t x i (.internal m children) l

/-- Structural soundness for `CoverageTree` (Story 07c / round-5, 07c-2).

The tree model currently proves only that a valid, complete tree descends to
a verified leaf. The accelerated-orbit definitions above are available for a
future semantic invariant, but this theorem intentionally does not conclude
`ReachesOne x`; that would require a proof connecting tree descent to the
Collatz trajectory. -/
theorem coverage_tree_soundness (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l := by
  suffices h : ∀ (depth : Nat),
      ∀ (n : CoverageNode), ValidNode depth n → IsCompleteAux t n →
      ∀ x, x > 0 →
        ∃ l, l ∈ t.leaves ∧ verified t l ∧ descendFrom depth n x = some l by
    exact h t.maxDepth t.root hv.2 hic x hx
  intro depth
  induction depth using Nat.rec with
  | zero =>
    intro n hvn hic x hx
    cases n with
    | leaf l =>
      cases hic with
      | leafC _ hleaf hver =>
        exact ⟨l, hleaf, hver, rfl⟩
    | internal m children =>
      exact False.elim hvn
  | succ depth' ih =>
    intro n hvn hic x hx
    cases n with
    | leaf l =>
      cases hic with
      | leafC _ hleaf hver => exact ⟨l, hleaf, hver, rfl⟩
    | internal m children =>
      cases hic with
      | internalC _ _ hm halls hall =>
        have hx_mod : x % m < m := Nat.mod_lt x hm
        have hlookup : (children.lookup (x % m)).isSome := halls.2 (x % m) hx_mod
        obtain ⟨child, hchild_lookup⟩ := Option.isSome_iff_exists.mp hlookup
        obtain ⟨before, after, hchildren, _⟩ :=
          List.lookup_eq_some_iff.mp hchild_lookup
        have hpair_mem : (x % m, child) ∈ children := by
          rw [hchildren]
          simp
        obtain ⟨_, _, hvn_rest⟩ := hvn
        have hchild_vn : ValidNode depth' child := by
          exact hvn_rest (x % m, child) hpair_mem
        have hchild_ic : IsCompleteAux t child := by
          exact hall (x % m, child) hpair_mem
        have hresult := ih child hchild_vn hchild_ic x hx
        obtain ⟨l, hl, hv', hdesc_child⟩ := hresult
        refine ⟨l, hl, hv', ?_⟩
        simpa [descendFrom, hchild_lookup] using hdesc_child

/-- Semantic-leaf soundness for `CoverageTree` (Story 07c / round-5, 07c-2).

Strengthens `coverage_tree_soundness` by adding a leaf-level
`LeafReachesOne t l` certificate to the conclusion. The certificate
is taken as an explicit hypothesis `hLeaf` rather than derived from
`ValidTree t ∧ IsComplete t`, because the unconditional conclusion
(`ReachesOne x` for every `x > 0` under any valid complete tree)
would amount to the global Collatz theorem — a tree-soundness
bridge cannot entail that. The conditional form makes the semantic
gap explicit (see `docs/story-07c-2-promotion.md`).

**Proof status: formally established.** No new `sorry`/`admit`/`axiom`.
The proof applies `coverage_tree_soundness`, unfolds `LeafReachesOne`
via `intro`, and re-applies `hLeaf` to the unfolded binders to obtain
`ReachesOne`. -/
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l := by
  obtain ⟨l, hl, hver, hdesc⟩ := coverage_tree_soundness t hv hic x hx
  refine ⟨l, hl, hver, hdesc, ?_⟩
  intro x' hdesc'
  exact hLeaf l hl hver x' hdesc'

/-- Typed-certificate variant of `coverage_tree_soundness_full`
    (Story Q3 / PR #54).

    Takes an indexed `LeafCertificate t l` (with mandatory
    `well_formed` field per Codex P2 at PR #53 review run 199)
    per verified leaf, and produces the same conclusion as
    `coverage_tree_soundness_full` by composing
    `routed_implies_claim` and `claim_reaches_one`.

    A **sound, typed refinement** of `coverage_tree_soundness_full`:
    the proof is `exact (hCert l hl hver).claim_reaches_one x'
    ((hCert l hl hver).routed_implies_claim x' hdesc')` — no
    axioms, no `sorry`. The new `hCert` hypothesis is **strictly
    stronger** than `coverage_tree_soundness_full`'s `hLeaf` (a
    `LeafCertificate t l` factors through `LeafReachesOne t l` via
    `claim_reaches_one ∘ routed_implies_claim`; the reverse is not
    supplied and generally cannot construct a well-formed claim plus
    its all-claim reachability proof from `hLeaf` alone). PR #54
    does **NOT** establish any new global or per-leaf Collatz
    reachability result.

    **Easier to audit** — the two obligations are explicit at the
    call site, the certificate is data (with kernel-checked proof
    witnesses), and the mandatory `well_formed` field prevents
    malformed `.interval` claims from slipping through as
    purported certificates.

    Per v3 spec § "API integration" (lines 167–217 in
    `docs/story-q3-leaf-certificate.md`).

    (Story Q3 / PR #54.) -/
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

/-- Orbit-aware soundness for `CoverageTree` (Story 07c / round-5, 07c-3).

Strengthens `coverage_tree_soundness` with the orbit-aware `SatOrbit`
predicate. The orbit depth at the leaf is bounded by `t.maxDepth`
(each internal step advances `k` by 1, and the tree has at most
`t.maxDepth` internal levels).

**Proof status: preparatory.** The proof is admitted via `sorry`
pending:
1. A formal proof of `OrbitAlignedTree t` from the existing
   `ValidTree t ∧ IsComplete t` hypotheses — currently `OrbitAlignedTree`
   is taken as an explicit hypothesis, and the implication
   `ValidTree ∧ IsComplete → OrbitAligned` is open.
2. Mathlib `Nat.factorization` + `omega` extensions for the residue
   bounds arithmetic in the `SatOrbit` witness construction.

Promotion to `formally established` requires closing both. -/
theorem coverage_tree_soundness_orbit (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (ha : OrbitAlignedTree t)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         SatOrbit t x l := by
  sorry

/-- Orbit-aware routing completeness (Story 07c-4).

    Strengthens `coverage_tree_soundness` with orbit-aware routing. For
    each positive input `x`, `descendOrbit t x 0` returns a leaf in
    `t.leaves`, verifies it, and constructs the
    `OrbitRoute t x 0 t.root l` witness (each internal edge is selected
    by `accelerated_orbit x i % m`).

    **Proof strategy:** mirror `coverage_tree_soundness` (Nat induction
    on depth, `cases n` on `CoverageNode`). Orbit-aware residue
    `accelerated_orbit x k % m` instead of `x % m`. `OrbitRoute`
    witness threaded through the induction hypothesis.

    **Claim level: formally established.** No `sorry`, no `admit`, no
    axiom. Companion to `coverage_tree_soundness`; does NOT modify
    `coverage_tree_soundness_orbit` or its `sorry` (separate workstream). -/
theorem descend_orbit_complete (t : CoverageTree) (hv : ValidTree t) (hc : IsComplete t)
    (x : Nat) (hx : 0 < x) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         OrbitRoute t x 0 t.root l := by
  suffices h : ∀ (depth : Nat),
      ∀ (n : CoverageNode), ValidNode depth n → IsCompleteAux t n →
      ∀ (k : Nat), ∀ x, x > 0 →
        ∃ l, l ∈ t.leaves ∧ verified t l ∧
             descendFromOrbit depth n x k = some l ∧
             OrbitRoute t x k n l by
    exact h t.maxDepth t.root hv.2 hc 0 x hx
  intro depth
  induction depth using Nat.rec with
  | zero =>
    intro n hvn hic k x hx
    cases n with
    | leaf l =>
      cases hic with
      | leafC _ hleaf hver =>
        exact ⟨l, hleaf, hver, rfl, OrbitRoute.leaf⟩
    | internal m children =>
      exact False.elim hvn
  | succ depth' ih =>
    intro n hvn hic k x hx
    cases n with
    | leaf l =>
      cases hic with
      | leafC _ hleaf hver =>
        exact ⟨l, hleaf, hver, rfl, OrbitRoute.leaf⟩
    | internal m children =>
      cases hic with
      | internalC _ _ hm halls hall =>
        have hx_mod : accelerated_orbit x k % m < m :=
          Nat.mod_lt (accelerated_orbit x k) hm
        have hlookup : (children.lookup (accelerated_orbit x k % m)).isSome :=
          halls.2 (accelerated_orbit x k % m) hx_mod
        obtain ⟨child, hchild_lookup⟩ := Option.isSome_iff_exists.mp hlookup
        obtain ⟨before, after, hchildren, _⟩ :=
          List.lookup_eq_some_iff.mp hchild_lookup
        have hpair_mem : (accelerated_orbit x k % m, child) ∈ children := by
          rw [hchildren]; simp
        obtain ⟨_, _, hvn_rest⟩ := hvn
        have hchild_vn : ValidNode depth' child :=
          hvn_rest (accelerated_orbit x k % m, child) hpair_mem
        have hchild_ic : IsCompleteAux t child :=
          hall (accelerated_orbit x k % m, child) hpair_mem
        have hresult := ih child hchild_vn hchild_ic (k + 1) x hx
        obtain ⟨l, hl, hv', hdesc_child, hroute_child⟩ := hresult
        refine ⟨l, hl, hv', ?_, ?_⟩
        · simpa [descendFromOrbit, hchild_lookup] using hdesc_child
        · exact OrbitRoute.internal hpair_mem hroute_child

/-- Bounded-orbit companion theorem for `FiniteOrbitClaim` shapes
    (`.empty`, `.singleton n`, `.bounded K`) — **parallel** to (NOT a
    refinement of) `coverage_tree_soundness_full` /
    `coverage_tree_soundness_cert`.

    Certifies the **orbit-aware routing relation** (`descendOrbit t x 0`)
    rather than the residue-only routing relation (`descend t x`).
    Concludes `OrbitLeafReachesOne t l` (NEW Q4 v3 predicate), defined
    over `descendOrbit`, NOT `LeafReachesOne t l` (defined over `descend`).

    Per Codex run-21848 P1: the previous v2 spec concluded
    `LeafReachesOne t l` while constructing a proof over `descendOrbit`;
    the kernel rejected this because `descend t x = some l` and
    `descendOrbit t x 0 = some l` are different routing relations.
    v3 introduces `OrbitLeafReachesOne` so the conclusion type matches
    the routing evidence used in the proof.

    Proof sketch:
      1. `descend_orbit_complete` provides orbit-aware routing with
         `OrbitRoute` witness.
      2. `cert.orbit_hits_claim` lifts the routing to an orbit-state
         claim (`∃ k, claim.Holds (accelerated_orbit x' k)`).
      3. `cert.claim_reaches_one` derives
         `ReachesOne (accelerated_orbit x' k)`.
      4. `orbit_predecessor_reaches_one` closes: original `x'` reaches 1
         via the orbit-predecessor closure lemma.

    **Q4 v3 scope:** the theorem is universally quantified over
    `FiniteOrbitClaim` shapes. For `.interval` claims, use
    `coverage_tree_soundness_cert` (Q3 v4) instead. The two theorems
    certify DIFFERENT routing relations and are PARALLEL, not
    refinements of each other.

    **Hypothesis-bearing.** Does NOT prove any new global or per-leaf
    Collatz reachability result beyond what `BoundedOrbitCertificate t l`
    packages. External computation may propose witnesses, but
    `BoundedOrbitCertificate` requires Lean-checked proof fields (or a
    separately proved Lean checker).

    **Position note.** Declared after `descend_orbit_complete` — the
    theorem's proof body uses `descend_orbit_complete` for orbit-
    aware routing + `OrbitRoute` witness, so it must be in scope.

    (Story Q4 / PR #58.) -/
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

-- Depth-0/1/2 regression examples (per Codex 4922430978).
example : descendFrom 0 (.leaf { leafId := "L0", leafProperty := "P0" }) 5 = some { leafId := "L0", leafProperty := "P0" } := rfl

example : descendFrom 0 (.internal 4 [(1, .leaf { leafId := "L0", leafProperty := "P0" })]) 5 = none := rfl

example : descendFrom 1 (.internal 4 [(1, .leaf { leafId := "L1", leafProperty := "P1" })]) 1 = some { leafId := "L1", leafProperty := "P1" } := rfl

example : descendFrom 1 (.internal 4 [(1, .leaf { leafId := "L1", leafProperty := "P1" })]) 2 = none := rfl

example :
    descendFrom 2
      (.internal 4 [(3, .internal 2 [(1, .leaf { leafId := "L2", leafProperty := "P2" })])])
      7 = some { leafId := "L2", leafProperty := "P2" } := rfl

-- PR #56 compile-checked scenario: `OrbitLeafReachesOne` def unfolds
-- correctly to `∀ x, descendOrbit t x 0 = some l → ReachesOne x`.
-- This is the API-shape guard that the predicate type-matches the
-- companion theorem conclusion (PR #58 deliverable) and the orbit-
-- routing hypothesis used in the proof. Mirrors the parallel
-- `LeafReachesOne` def (Story 07c / round-5, 07c-2) — both defs are
-- simple lambdas whose def-equality is closed by `rfl`.
example (t : CoverageTree) (l : CoverageLeaf) :
    OrbitLeafReachesOne t l = ∀ x, descendOrbit t x 0 = some l → ReachesOne x := rfl

end CollatzResearch
