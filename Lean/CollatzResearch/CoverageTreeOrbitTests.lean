/-
Story 07c-3 — test-first orbit routing contract (BDD executable specifications).

These `example` blocks are written BEFORE the implementation per the BDD
test-first gate (see `docs/story-07c-3-proof-rewrite.md`). They reference
`descendOrbit`, `OrbitRoute`, and `descend_orbit_complete` which do not yet
exist (or exist with the wrong signature). The file is expected to fail to
compile at this point; the implementation commit makes the same examples
pass without weakening their assertions.
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
example (l : CoverageLeaf) (x : Nat) (hx : 0 < x) :
    descendOrbit { root := .leaf l, leaves := [l], maxDepth := 1 } x = some l := rfl

-- Scenario 4: Depth-one route — child selected by `accelerated_orbit x 0 % m`.
-- At a root internal node with modulus 4, `accelerated_orbit x 0 = x`, so
-- the child is selected by `x % 4`.
example (x : Nat) (hx : 0 < x) :
    (let t : CoverageTree :=
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
     descendOrbit t x = some
       ({ leafId :=
           (if x % 4 = 0 then "L0"
            else if x % 4 = 1 then "L1"
            else if x % 4 = 2 then "L2"
            else "L3"),
          leafProperty := s!"4:{x % 4}-{x % 4}" })) := rfl

-- Scenario 5: Depth-two route — second edge uses `accelerated_orbit x 1 % m₁`,
-- never raw `x % m₁`. Choose `x` where `x % m₀` differs from `T(x) % m₁`.
example (x : Nat) (hx : 0 < x) :
    (let t : CoverageTree :=
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
     -- For x = 5: x % 4 = 1 → child with modulus 3; accelerated_orbit 5 1 = 1 →
     -- 1 % 3 = 1 → leaf D1. Raw `x % 3 = 5 % 3 = 2` would pick D2, which is WRONG.
     descendOrbit t 5 = some { leafId := "D1", leafProperty := "3:1-1" }) := rfl

-- Scenario 6: Completeness — `descend_orbit_complete` gives leaf membership,
-- verification, exact `descendOrbit` result, and `OrbitRoute` witness.
-- (Will fail to compile until `descend_orbit_complete` is defined.)
example (t : CoverageTree) (hv : ValidTree t) (hc : IsComplete t)
    (x : Nat) (hx : 0 < x) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x = some l ∧
         OrbitRoute t x 0 t.root l :=
  descend_orbit_complete t hv hc x hx

-- Scenario 7: Zero boundary — the theorem requires `0 < x`; no proof is
-- available without it, and no zero convergence statement is added.
-- (Implicit: the theorem signature includes `hx : 0 < x`.)

end CollatzResearch
