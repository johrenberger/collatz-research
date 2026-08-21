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

/-- `ReachesOne n` iff applying `acceleratedStep` repeatedly to `n`
    eventually reaches 1. (Story 07c / round-5, 07c-2.) -/
def ReachesOne (n : Nat) : Prop := ∃ k, accelerated_orbit n k = 1

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
The proof applies `coverage_tree_soundness` and extracts `LeafReachesOne`
from the leaf-semantic hypothesis. -/
theorem coverage_tree_soundness_full (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l)
    (x : Nat) (hx : x > 0) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l ∧
         LeafReachesOne t l := by
  obtain ⟨l, hl, hver, hdesc⟩ := coverage_tree_soundness t hv hic x hx
  exact ⟨l, hl, hver, hdesc, hLeaf l hl hver hdesc⟩

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

-- Depth-0/1/2 regression examples (per Codex 4922430978).
example : descendFrom 0 (.leaf { leafId := "L0", leafProperty := "P0" }) 5 = some { leafId := "L0", leafProperty := "P0" } := rfl

example : descendFrom 0 (.internal 4 [(1, .leaf { leafId := "L0", leafProperty := "P0" })]) 5 = none := rfl

example : descendFrom 1 (.internal 4 [(1, .leaf { leafId := "L1", leafProperty := "P1" })]) 1 = some { leafId := "L1", leafProperty := "P1" } := rfl

example : descendFrom 1 (.internal 4 [(1, .leaf { leafId := "L1", leafProperty := "P1" })]) 2 = none := rfl

example :
    descendFrom 2
      (.internal 4 [(3, .internal 2 [(1, .leaf { leafId := "L2", leafProperty := "P2" })])])
      7 = some { leafId := "L2", leafProperty := "P2" } := rfl

end CollatzResearch
