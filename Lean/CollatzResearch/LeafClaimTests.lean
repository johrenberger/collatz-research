/-
Story Q3 — CI-side executable spec for `LeafClaim` data type +
`parse_leaf_claim` structural decoder.

These `example` blocks are compile-checked by `lake build` in GitHub
CI, not run locally. Per the project-wide rule (MEMORY.md,
"BDD Discipline (Lean vs Python)"), Lean validation is CI-only;
this module does not enter any local BDD gate.

**Scope (per Codex P1 at PR #53 review run 199, 2026-08-22T00:13:50Z).**
The scenarios preserve the required malformed-input and
modulo-boundary behavior for `parse_leaf_claim` + `LeafClaim.Holds`.
This is the release guard for a parser that later becomes a
certificate-input boundary (PR #54).

Scenarios:
1.  Valid legacy decoding: `"2:1-1"` → `some (.interval 2 1 1)`.
2.  Malformed syntax rejection (no colon).
3.  Zero-period rejection: `"0:0-0"` → `none` (period > 0 guard).
4.  Invalid range (lo > hi): `"2:2-1"` → `none`.
5.  Invalid range (hi ≥ period): `"2:0-2"` → `none`.
6.  `.interval 2 1 1` accepts odd positive `5` (5 % 2 = 1 ∈ [1, 1]).
7.  `.interval 2 1 1` rejects even `4` (4 % 2 = 0 ∉ [1, 1]).
8.  `.empty.Holds 0 = False` (no inputs claimed).
9.  `.singleton 5 .Holds 5 = True`.
10. `.singleton 5 .Holds 4 = False`.
11. `.bounded 10 .Holds 0 = True`.
12. `.bounded 10 .Holds 10 = True` (boundary inclusive).
13. `.bounded 10 .Holds 11 = False` (just past boundary).

Uses `native_decide` for propositional equalities on closed
values. No `native_decide` leaks into formal proofs.

This is a sibling test module to `CoverageTreeOrbitTests.lean` and
`DynamicsHelpersTests.lean`. Lean CI compiles this module as part
of the `CollatzResearch` library build.
-/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Helper: construct a `CoverageLeaf` from a `leafProperty` string. -/
def leafWith (prop : String) : CoverageLeaf :=
  { leafId := "test", leafProperty := prop }

/-- Scenario 1: valid legacy decoding `"2:1-1"` → `some (.interval 2 1 1)`. -/
example : parse_leaf_claim (leafWith "2:1-1") = some (LeafClaim.interval 2 1 1) := by
  native_decide

/-- Scenario 2: malformed syntax (no colon) → `none`. -/
example : parse_leaf_claim (leafWith "garbage") = none := by
  native_decide

/-- Scenario 3: zero-period `"0:0-0"` → `none` (period > 0 guard). -/
example : parse_leaf_claim (leafWith "0:0-0") = none := by
  native_decide

/-- Scenario 4: invalid range `"2:2-1"` → `none` (lo > hi). -/
example : parse_leaf_claim (leafWith "2:2-1") = none := by
  native_decide

/-- Scenario 5: invalid range `"2:0-2"` → `none` (hi ≥ period). -/
example : parse_leaf_claim (leafWith "2:0-2") = none := by
  native_decide

/-- Scenario 6: `.interval 2 1 1` accepts odd positive `5`
    (`5 % 2 = 1 ∈ [1, 1]`). -/
example : (LeafClaim.interval 2 1 1).Holds 5 = True := by
  native_decide

/-- Scenario 7: `.interval 2 1 1` rejects even `4`
    (`4 % 2 = 0 ∉ [1, 1]`). -/
example : (LeafClaim.interval 2 1 1).Holds 4 = False := by
  native_decide

/-- Scenario 8: `.empty.Holds 0 = False` (no inputs claimed). -/
example : LeafClaim.empty.Holds 0 = False := by
  native_decide

/-- Scenario 9: `.singleton 5 .Holds 5 = True`. -/
example : (LeafClaim.singleton 5).Holds 5 = True := by
  native_decide

/-- Scenario 10: `.singleton 5 .Holds 4 = False`. -/
example : (LeafClaim.singleton 5).Holds 4 = False := by
  native_decide

/-- Scenario 11: `.bounded 10 .Holds 0 = True`. -/
example : (LeafClaim.bounded 10).Holds 0 = True := by
  native_decide

/-- Scenario 12: `.bounded 10 .Holds 10 = True` (boundary inclusive). -/
example : (LeafClaim.bounded 10).Holds 10 = True := by
  native_decide

/-- Scenario 13: `.bounded 10 .Holds 11 = False` (just past boundary). -/
example : (LeafClaim.bounded 10).Holds 11 = False := by
  native_decide

end CollatzResearch