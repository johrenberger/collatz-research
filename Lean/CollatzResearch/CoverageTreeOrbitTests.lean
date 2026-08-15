/-
Story 07c-4 — CI-side executable spec for the orbit-aware routing contract.

These `example` blocks are compile-checked by `lake build` in GitHub CI,
not run locally. Per `docs/story-07c-4-structural-induction.md` and
the project-wide rule (MEMORY.md, "BDD Discipline (Lean vs Python)"),
Lean validation is CI-only; this module does not enter any local BDD
gate.

Scenarios mirror the 07c-3 inherited BDD table, adapted to master's
3-arg `descendOrbit t x k` (entry point: `k = 0`).
-/

import CollatzResearch.CoverageTree

namespace CollatzResearch

-- Scenario 1: Base orbit — `accelerated_orbit x 0 = x`.
example : accelerated_orbit 5 0 = 5 := rfl
example : accelerated_orbit 0 0 = 0 := rfl
example : accelerated_orbit 17 0 = 17 := rfl

-- Scenario 2: One step — `accelerated_orbit x 1 = acceleratedStep x`,
-- with exact values `1, 1, 25, 1` for inputs `0, 1, 8, 5`.
example : accelerated_orbit 0 1 = 1 := rfl
example : accelerated_orbit 1 1 = 1 := rfl
example : accelerated_orbit 8 1 = 25 := rfl
example : accelerated_orbit 5 1 = 1 := rfl

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
example :
    let t : CoverageTree :=
      { root := .internal 4
          [(1, .internal 3
            [(0, .leaf { leafId := "D0", leafProperty := "3:0-0" }),
             (1, .leaf { leafId := "D1", leafProperty := "3:1-1" }),
             (2, .leaf { leafId := "D2", leafProperty := "3:2-2" })])],
        leaves :=
          [{ leafId := "D0", leafProperty := "3:0-0" },
           { leafId := "D1", leafProperty := "3:1-1" },
           { leafId := "D2", leafProperty := "3:2-2" }],
        maxDepth := 2 }
    descendOrbit t 5 0 = some { leafId := "D1", leafProperty := "3:1-1" } := rfl

-- Scenario 6: Completeness — `descend_orbit_complete` provides leaf
-- membership, verification, exact `descendOrbit` result, and `OrbitRoute`
-- witness.
example (t : CoverageTree) (hv : ValidTree t) (hc : IsComplete t)
    (x : Nat) (hx : 0 < x) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         OrbitRoute t x 0 t.root l :=
  descend_orbit_complete t hv hc x hx

-- Scenario 7: Zero boundary — the theorem requires `0 < x`; no proof
-- is available without it, and no zero convergence statement is added.
-- (Implicit in `hx : 0 < x`.)

end CollatzResearch