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
`native_decide` (scenarios 2, 5, 6; the `hv` and `hc` witnesses in
scenario 6) uses VM-backed evaluation to close goals of the form
`closed_Nat_computation = expected_value`. This is appropriate as
executable-test evidence for closed `Nat` computations. It does NOT
contribute to the kernel proof basis for `descend_orbit_complete` —
the theorem's proof uses only `induction` + `cases` + standard Mathlib
lemmas (no `native_decide`, no VM evaluation). The executable spec is
regression evidence, not a proof artifact.

The reviewer's preferred proof shape for scenario 5 was
`have hstep := by native_decide; simp [descendOrbit, descendFromOrbit, hstep]`
(native_decide only on the closed `accelerated_orbit 5 1 = 1`, then
`simp` symbolically to reduce the route). In practice `simp` did not
fully reduce the goal — the `depthTwoTree.maxDepth` / `depthTwoTree.root`
projections blocked the recursion under the default simp set, and
adding `depthTwoTree` to the simp set still left the outer
`descendFromOrbit` match cases un-driven. Falling back to
`native_decide` on the full concrete expression matches the P2
reviewer's note ("fine for closed regression checks").
-/

import CollatzResearch.CoverageTree

namespace CollatzResearch

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

-- Scenario 5: Depth-two route — second edge uses `accelerated_orbit x 1 % m₁`,
-- never raw `x % m₁`. For x = 5: 5 % 4 = 1 -> child with modulus 3;
-- accelerated_orbit 5 1 = 1; 1 % 3 = 1 -> leaf D1.
-- Raw `x % 3 = 5 % 3 = 2` would pick D2, which is WRONG.
example : descendOrbit depthTwoTree 5 0 = some { leafId := "D1", leafProperty := "3:1-1" } := by
  native_decide

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

end CollatzResearch