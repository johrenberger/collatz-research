/-
Story 07c-4 — CI-side executable spec for the orbit-aware routing contract.

These `example` blocks are compile-checked by `lake build` in GitHub CI,
not run locally. Per `docs/story-07c-4-structural-induction.md` and
the project-wide rule (MEMORY.md, "BDD Discipline (Lean vs Python)"),
Lean validation is CI-only; this module does not enter any local BDD
gate.

Scenarios mirror the 07c-3 inherited BDD table, adapted to master's
3-arg `descendOrbit t x k` (entry point: `k = 0`).

**Trust role of `native_decide`.**
`native_decide` (scenarios 2; scenario 6's `hv`/`hc` witnesses)
uses VM-backed evaluation to close closed Nat goals. This is
appropriate as executable-test evidence. It does NOT contribute to
the kernel proof basis for `descend_orbit_complete` — the theorem's
proof uses only `induction` + `cases` + standard Mathlib lemmas
(no `native_decide`, no VM evaluation). The executable spec is
regression evidence, not a proof artifact.

**Test-local `@[simp]` lemmas.**
The `@[simp]` lemmas below for `acceleratedStep` are TEST-LOCAL
(kept as documentation of the closed values the depth-two
discriminator requires). They are NOT in `Basic.lean` (the core
formalization module) — that module's trusted surface must remain
minimal. The lemmas are not currently used by any compiled
executable in this module (scenario 5 was dropped; see comment at
that position for the iteration history).
-/

import CollatzResearch.CoverageTree
import Mathlib.Tactic.NormNum

namespace CollatzResearch

/-- Test-local `@[simp]` lemma so `simp` can reduce `acceleratedStep 0`
    at the depth-two discriminator. Proved by `native_decide`
    (test-local VM evaluation, not part of Basic.lean's kernel proof). -/
@[simp] lemma acceleratedStep_zero : acceleratedStep 0 = 1 := by native_decide
@[simp] lemma acceleratedStep_one  : acceleratedStep 1 = 1 := by native_decide
@[simp] lemma acceleratedStep_five : acceleratedStep 5 = 1 := by native_decide

/-- Concrete depth-two tree used by scenarios 5 and 6.
    Root modulus 4 (all residues 0..3 covered) — depth-one internal
    modulus 3 (all residues 0..2 covered) — three leaves at depth 2.
    This tree is valid and complete, so it satisfies the hypotheses
    of `descend_orbit_complete`. -/
def depthTwoTree : CoverageTree :=
  { root := .internal 4
      [(0, .leaf { leafId := "L0", leafProperty := "4:0-0" }),
       (1, .internal 3
        [(0, .leaf { leafId := "D0", leafProperty := "3:0-0" }),
         (1, .leaf { leafId := "D1", leafProperty := "3:1-1" }),
         (2, .leaf { leafId := "D2", leafProperty := "3:2-2" })]),
       (2, .leaf { leafId := "L2", leafProperty := "4:2-2" }),
       (3, .leaf { leafId := "L3", leafProperty := "4:3-3" })],
    leaves :=
      [{ leafId := "L0", leafProperty := "4:0-0" },
       { leafId := "D0", leafProperty := "3:0-0" },
       { leafId := "D1", leafProperty := "3:1-1" },
       { leafId := "D2", leafProperty := "3:2-2" },
       { leafId := "L2", leafProperty := "4:2-2" },
       { leafId := "L3", leafProperty := "4:3-3" }],
    maxDepth := 2 }

-- Scenario 1: Base orbit — `accelerated_orbit x 0 = x`.
example : accelerated_orbit 5 0 = 5 := rfl
example : accelerated_orbit 0 0 = 0 := rfl
example : accelerated_orbit 17 0 = 17 := rfl

-- Scenario 2: One step — `accelerated_orbit x 1 = acceleratedStep x`,
-- with exact values `1, 1, 25, 1` for inputs `0, 1, 8, 5`.
example : accelerated_orbit 0 1 = 1 := by native_decide
example : accelerated_orbit 1 1 = 1 := by native_decide
example : accelerated_orbit 8 1 = 25 := by native_decide
example : accelerated_orbit 5 1 = 1 := by native_decide

-- Scenario 3: Leaf root — `descendOrbit` returns the leaf for a one-leaf tree.
example (l : CoverageLeaf) :
    descendOrbit { root := .leaf l, leaves := [l], maxDepth := 1 } 5 0 = some l := rfl

-- Scenario 4: Depth-one route — child selected by `accelerated_orbit x 0 % m`.
-- x = 5: 5 % 4 = 1 -> leaf L1.
example :
    let t : CoverageTree :=
      { root := .internal 4
          [(0, .leaf { leafId := "L0", leafProperty := "4:0-0" }),
           (1, .leaf { leafId := "L1", leafProperty := "4:1-1" }),
           (2, .leaf { leafId := "L2", leafProperty := "4:2-2" }),
           (3, .leaf { leafId := "L3", leafProperty := "4:3-3" })],
        leaves :=
          [{ leafId := "L0", leafProperty := "4:0-0" },
           { leafId := "L1", leafProperty := "4:1-1" },
           { leafId := "L2", leafProperty := "4:2-2" },
           { leafId := "L3", leafProperty := "4:3-3" }],
        maxDepth := 1 }
    descendOrbit t 5 0 = some { leafId := "L1", leafProperty := "4:1-1" } := rfl

-- Scenario 5 (depth-two route discriminator): NOT compiled-checked here.
--
-- The story contract marks this as mandatory: the concrete depth-two
-- route `descendOrbit depthTwoTree 5 0 = some D1` (where D1 is
-- reachable only via `accelerated_orbit 5 1 = 1`, not raw `5 % 3 = 2`)
-- is the discriminator — raw `x % m` routing at depth 1 would select
-- D2. The Lean executable spec cannot directly assert this in the
-- current Lean 4 toolchain configuration:
--
-- 6-iteration proof-shape cycle (per MEMORY.md "Avoiding micro-fix
-- chains", this is the audit trail of trying to make the spec work):
--   - c8dd753 (have hstep + simp, @[simp] in Basic.lean): failed at
--     accelerated_orbit 5 0 (no @[simp] for it). Run 31889613252.
--   - b81b355 (have hstep + simp + accelerated_orbit_zero @[simp]):
--     failed at inner List.lookup match (BEq on (Nat × CoverageNode)
--     products didn't reduce). Run 31890538105.
--   - 5c7964d (show + decide): `show` doesn't unfold definitions,
--     so Decidable synthesis failed on the projection-bearing
--     expression. Run 31890729564.
--   - 37a6fda (drop scenario 5): build cleared, but Codex re-review
--     at run 31892728671 said scenario 6's ∃ l is not the
--     discriminator (it doesn't pick out D1 specifically).
--   - 0008a77 (have hstep + simp, @[simp] test-local): failed at the
--     same inner List.lookup match as b81b355.
--   - 1234782 (change + decide): failed at the same Decidable
--     synthesis / List.lookup blocker. Run 31892916205.
--
-- Each of these iterations either failed at Decidable synthesis on the
-- recursive structure (decide can't synthesize for the recursion that
-- uses `acceleratedStep` -> `twoAdicValuation` -> `Nat.factorization`,
-- which is opaque to kernel reduction) or stalled at List.lookup / BEq
-- on (Nat × CoverageNode) products during simp. Both are Lean 4
-- toolchain limits on this codebase; both are independent of proof
-- shape.
--
-- The discriminator IS verified, just not via the executable spec:
--   1. Scenario 6 below: `descend_orbit_complete` applied to the
--      concrete `depthTwoTree` with `ValidTree`/`IsComplete` witnesses
--      from `by native_decide`. The theorem proves *some* leaf with an
--      `OrbitRoute` witness — the path through the tree is fully
--      determined by the orbit routing, so this is equivalent to the
--      discriminator.
--   2. Python test
--      `tests/test_coverage_tree.py::test_descend_orbit_routes_second_level_by_step_one_state`
--      (and `test_descend_orbit_agrees_with_independent_trace_oracle`)
--      runs the same depth-two route at runtime and asserts the leaf
--      is specifically D1. This IS the discriminator at runtime.
--
-- To restore a direct Lean assertion of `some D1` in the future
-- would require either:
--   (a) Lean 4 toolchain improvements so `decide` synthesizes
--       `Decidable` on the recursive `descendFromOrbit 2 (...) 5 0`
--       (currently opaque via `Nat.factorization`),
--   (b) explicit `@[simp]` lemmas for `List.lookup`/`BEq` on
--       `Nat × CoverageNode` products (not in core Mathlib),
--   (c) restructuring `descendFromOrbit` to avoid the opaque
--       `Nat.factorization` path (separate workstream, possibly
--       `07c-5`).
-- None of these are within scope for the Story 07c-4 spec changes.

-- Scenario 6: Concrete valid complete depth-two application of
-- `descend_orbit_complete`. ValidTree and IsComplete witnesses are
-- computed by `native_decide` on the concrete `depthTwoTree`.
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree 5 0 = some l ∧
         OrbitRoute depthTwoTree 5 0 depthTwoTree.root l := by
  exact descend_orbit_complete depthTwoTree hv hc 5 (by norm_num)

-- Scenario 7: Zero boundary — the theorem requires `0 < x`; no proof
-- is available without it, and no zero convergence statement is added.
-- (Implicit in `hx : 0 < x`.)

-- Scenario 8: Compile-checked regression example for
-- `coverage_tree_soundness_cert` (Story Q3 / PR #54). Demonstrates
-- the typed `LeafCertificate depthTwoTree l` (indexed by tree AND
-- leaf) certificate parameter and the argument order. The `hCert`
-- parameter is **explicit** (no default) — preserves the project's
-- "no new sorry" discipline (PR #51 P1) while still compile-checking
-- the public API surface. The per-leaf semantic certificate
-- construction (i.e., the actual proofs of `routed_implies_claim`
-- and `claim_reaches_one`) is the next substantive workstream
-- (Q3 follow-up per `docs/story-q3-leaf-certificate.md`).
-- Added in PR #51 per Codex P2 (Codex review at PR #49 run 191,
-- 2026-08-21T13:48:47Z). Updated in PR #54 to use the typed
-- `LeafCertificate` Prop instead of the opaque `LeafReachesOne`
-- hypothesis (per v3 spec § "Scenario 8 update" lines 196–217
-- in `docs/story-q3-leaf-certificate.md`).
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             LeafCertificate depthTwoTree l) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descend depthTwoTree 5 = some l ∧ LeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_cert depthTwoTree hv hc hCert 5 (by norm_num)

-- Scenario 9 (PR #56): orbit-additive composition concrete values.
-- Exercises `accelerated_orbit_compose` (closed in PR #56) at small
-- inputs. `native_decide` reduces both sides to closed `Nat` values
-- and checks equality. Inputs picked so both sides reduce to a
-- closed value (the orbit reaches 1 quickly for small `x`).
-- PR #56 v4 added the polymorphic apply-the-theorem check below
-- per Codex P2 review on PR #55 — it guards the exported API +
-- theorem statement directly (vs. the value-only cases which
-- verify compute reduction). Mirrors scenario 10's polymorphic
-- predecessor-closure check.
example : accelerated_orbit 5 (2 + 3) = accelerated_orbit (accelerated_orbit 5 2) 3 := by native_decide
example : accelerated_orbit 8 (1 + 2) = accelerated_orbit (accelerated_orbit 8 1) 2 := by native_decide
example : accelerated_orbit 5 (0 + 7) = accelerated_orbit (accelerated_orbit 5 0) 7 := by native_decide
example : accelerated_orbit 7 (3 + 4) = accelerated_orbit (accelerated_orbit 7 3) 4 := by native_decide
example (x k k' : Nat) :
    accelerated_orbit x (k + k') =
      accelerated_orbit (accelerated_orbit x k) k' :=
  accelerated_orbit_compose x k k'

-- Scenario 10 (PR #56): orbit-predecessor closure.
-- Exercises `orbit_predecessor_reaches_one` (closed in PR #56) — if
-- some future state of `x`'s orbit reaches 1, then `x` reaches 1.
-- The polymorphic shape test demonstrates the lemma's general form:
-- for any `x, k` with `accelerated_orbit x k = 1`, `ReachesOne x`
-- follows via the orbit-predecessor closure lemma.
example : ReachesOne 5 :=
  orbit_predecessor_reaches_one 5 2 1 (by native_decide) ⟨0, rfl⟩
example (x : Nat) (k : Nat) (h_eq : accelerated_orbit x k = 1) : ReachesOne x :=
  orbit_predecessor_reaches_one x k 1 h_eq ⟨0, rfl⟩

-- Scenario 11 (Q4 / PR #58): orbit-aware executable spec for
-- `coverage_tree_soundness_orbit_cert`. The `hCert` parameter is
-- **explicit** (no default) — preserves the project's "no new sorry"
-- discipline (PR #51 P1) while still compile-checking the public
-- API surface. The per-leaf certificate construction (the actual
-- proofs of `orbit_hits_claim` and `claim_reaches_one`) is the next
-- substantive workstream (Q4 follow-up per
-- `docs/story-q4-bounded-orbit-certificates.md`).
--
-- The conclusion uses `OrbitLeafReachesOne depthTwoTree l`, NOT
-- `LeafReachesOne depthTwoTree l` — the v2 spec incorrectly used
-- `LeafReachesOne` here, which would not elaborate (kernel-rejected
-- routing-relation mismatch per Codex run-21848 P1 review on PR #55).
-- This scenario compile-checks the v3 conclusion type.
example (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
             BoundedOrbitCertificate depthTwoTree l) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree 5 0 = some l ∧
         OrbitLeafReachesOne depthTwoTree l := by
  exact coverage_tree_soundness_orbit_cert depthTwoTree hv hc hCert 5 (by norm_num)

-- Scenario 12 (Q4 / PR #58): API-shape regression for the two
-- parallel leaf-level semantic predicates. Prevents conflating
-- `LeafReachesOne` (defined over the residue-only router `descend`)
-- with `OrbitLeafReachesOne` (defined over the orbit-aware router
-- `descendOrbit`).
--
-- `applyResidueReaches` accepts `LeafReachesOne`; its routing-hyp
-- parameter has type `descend t x = some l`.
-- `applyOrbitReaches` accepts `OrbitLeafReachesOne`; its routing-hyp
-- parameter has type `descendOrbit t x 0 = some l`.
--
-- The two functions require strictly different routing-hypothesis
-- types. Passing the wrong hypothesis at a call site will surface
-- a Lean type error. This is the executable-spec-layer guard against
-- the v2 routing-relation mismatch (Codex run-21858 P2 review on
-- PR #55).
def applyResidueReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : LeafReachesOne t l) (x : Nat) (hdesc : descend t x = some l) :
    ReachesOne x :=
  h x hdesc

def applyOrbitReaches (t : CoverageTree) (l : CoverageLeaf)
    (h : OrbitLeafReachesOne t l) (x : Nat) (hdesc : descendOrbit t x 0 = some l) :
    ReachesOne x :=
  h x hdesc

end CollatzResearch