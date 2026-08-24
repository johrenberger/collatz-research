/-
Q5 PR #62 v3 — CI-side executable spec for the bounded-input certificate
data + checker (preparatory PR; no soundness theorem yet).

Per the Q5 spec § 6.2 (Q5 PR #2 scope) + the v4 Codex review
(REQUEST CHANGES, 2026-08-23T20:53:23Z, review #5003345398):
- v3 redesign (per Codex P0): `CertWitness (x : Nat)` parameterizes
    on canonical input; `witnesses : (i : Fin N) → CertWitness
    (i.val + 1)` makes input identity canonical by construction.
    External `N : Nat` parameter removed from `checkBoundedCertificate`
    (the bound comes from `d.N` directly, eliminating the transport bug).
- v3 redesign (per Codex P1): `checkCertWitness` requires
    `decide (claim.Holds last)` — the documented "trajectory … to a
    claim-satisfying value" contract is now enforced.

Removed in v3 (per the v4 redesign):
- `BoundedInputOrbitCertificate` structure — removed in v4 (`bd3d8b7`)
- `checkBoundedCertificate_sound` theorem — removed in v4 (`bd3d8b7`)
- Scenario E (polymorphic apply-the-theorem) — references the removed
    `checkBoundedCertificate_sound`

Scenarios (7 total, all compile-checked by `lake build CollatzResearch.Q5VerifierTests` in GitHub CI):
- A: positive — basic valid (N=1, claim `.singleton 1`, trajectory `[1]`)
- B: negative — step + terminal mismatch (trajectory `[1, 2]`)
- C: negative — head mismatch (trajectory `[2]` for x=1)
- D: positive — N=2 with two canonical witnesses (regression for `Fin N → CertWitness (i.val + 1)`)
- E: NEW per Codex P0 — canonical-input regression (N=3, all canonical)
- F: NEW per Codex P1 — terminal-claim negative, simple
- G: NEW per Codex P1 — terminal-claim negative, non-degenerate

-/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-- A simple tree with one leaf. Used to avoid the routing complexity
    of `depthTwoTree` for the executable spec — every `x > 0` routes
    to the single leaf `L`. -/
def singleLeafTree : CoverageTree :=
  { root := .leaf { leafId := "L", leafProperty := "0:0-0" },
    leaves := [{ leafId := "L", leafProperty := "0:0-0" }],
    maxDepth := 1 }

/-- Scenario A (positive — basic valid): N=1, claim `.singleton 1`,
    witness at i=0 (type-level `CertWitness 1`) with trajectory `[1]`.
    Head matches `x = 1`; no steps to verify; terminal `1 ∈ .singleton 1`.
    `acceleratedStep 1 = 1` because `3*1+1 = 4`, `ν₂(4) = 2`,
    so `4 / 2^2 = 1`. The trajectory from `x = 1` is `[1]`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] } } = true := by
  native_decide

/-- Scenario B (negative — step + terminal mismatch): N=1, claim
    `.singleton 1`, witness at i=0 (type-level `CertWitness 1`) with
    trajectory `[1, 2]`. Head matches (1=1), but the step
    `2 = acceleratedStep 1 = 1` fails, AND the terminal `2 ∉ .singleton 1`.
    Both checks fail (consistent with v3 review's P1 demand for explicit
    terminal claim check). -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1, 2] } } = by
  native_decide

/-- Scenario C (negative — head mismatch): N=1, claim `.singleton 1`,
    witness at i=0 (type-level `CertWitness 1`) with trajectory `[2]`.
    Head `2 ≠ x = 1`; the head check fails. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [2] } } = by
  native_decide

/-- Scenario D (positive — N=2 with two canonical witnesses per
    Codex P0 fix): N=2, claim `.singleton 1`. Witness at i=0
    (type-level `CertWitness 1`) with `[1]` (terminal 1 ∈ `.singleton 1`).
    Witness at i=1 (type-level `CertWitness 2`) with
    `[2, 7, 11, 17, 13, 5, 1]` (terminal 1 ∈ `.singleton 1`).
    Each consecutive pair is an `acceleratedStep` transition:
      acceleratedStep 2 = 7, acceleratedStep 7 = 11,
      acceleratedStep 11 = 17, acceleratedStep 17 = 13,
      acceleratedStep 13 = 5, acceleratedStep 5 = 1.

    The witness at index `i` is structurally `CertWitness (i.val + 1)`
    — type-level canonical input identity (Codex P0 fix). -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 1,
      N := 2,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] }
        | ⟨1, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [2, 7, 11, 17, 13, 5, 1] } } = true := by
  native_decide

/-- Scenario E (NEW per Codex P0 — canonical-input regression):
    N=3, claim `.singleton 1`. Three witnesses with canonical inputs:
      i=0 (type-level `CertWitness 1`) → trajectory `[1]`
      i=1 (type-level `CertWitness 2`) → trajectory `[2, 7, 11, 17, 13, 5, 1]`
      i=2 (type-level `CertWitness 3`) → trajectory `[3, 5, 1]`
          (acceleratedStep 3 = 5, acceleratedStep 5 = 1)

    A v4-style witness with mismatched `x` would NOT typecheck
    (the type parameter `CertWitness (i.val + 1)` is canonical by
    construction). This v3 regression shows the type-level constraint
    is enforced across multiple indices. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 1,
      N := 3,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] }
        | ⟨1, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [2, 7, 11, 17, 13, 5, 1] }
        | ⟨2, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [3, 5, 1] } } = true := by
  native_decide

/-- Scenario F (NEW per Codex P1 — terminal-claim negative, simple):
    N=1, claim `.singleton 2`. Witness at i=0 (type-level
    `CertWitness 1`) with trajectory `[1]`. The trajectory is VALID
    (head matches `x = 1`, no steps to verify), but the terminal
    value `1` is NOT in `.singleton 2`. The new `checkCertWitness`
    terminal check (`decide (claim.Holds last)`) catches this. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 2,
      N := 1,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] } } = by
  native_decide

/-- Scenario G (NEW per Codex P1 — terminal-claim negative, non-
    degenerate): N=2, claim `.singleton 100`. Witness at i=0
    (type-level `CertWitness 1`) with `[1]` (terminal 1 NOT in
    `.singleton 100`). Witness at i=1 (type-level `CertWitness 2`)
    with `[2, 7]` (terminal 7 NOT in `.singleton 100`; step
    `7 = acceleratedStep 2` is valid).

    Both trajectories have valid head + steps, but the terminal claim
    check fails for both. The list-level `checkBoundedCertificate`
    returns `false`. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    { claim := FiniteOrbitClaim.singleton 100,
      N := 2,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] }
        | ⟨1, _⟩ => { l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [2, 7] } } = by
  native_decide

end CollatzResearch
