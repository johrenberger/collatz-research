/-
Q5 PR #62 v4 — CI-side executable spec for the wire/checked split
(preparatory PR; no soundness theorem yet).

Per the v3 Codex review
(REQUEST CHANGES, 2026-08-24T11:57:44Z, review
`PRR_kwDOTuMD788AAAABKnjGrA`) on `a6ea9ad`:
- v4 redesign (per Codex P1): wire/checked split. The `witnesses`
    field that was a Lean function `(i : Fin N) → CertWitness (i.val + 1)`
    is replaced by:
      * `BoundedInputCertificateWire` — wire payload (plain `List`,
        NO proof fields, NO `x` field on each witness). What Python
        emits as JSON.
      * `BoundedInputCertificateData` — checked bundle (wire +
        `length_ok : wire.rawWitnesses.length = wire.N`).
      * `decodeBoundedInputCertificateData` — returns `none` on
        malformed wire (length mismatch).
      * `BoundedInputCertificateData.certWitness` — RECONSTRUCTED
        indexed view `(i : Fin d.wire.N) → CertWitness (i.val + 1)`
        via `List.get` (with the length proof transporting
        `i.val < wire.N` to `i.val < wire.rawWitnesses.length`).

Removed in v4:
- The structure field `witnesses : (i : Fin N) → CertWitness (i.val + 1)`
    (replaced by derived `certWitness` def + wire `rawWitnesses` field)
- The structure field `N : Nat` directly on the checked data
    (moved inside `wire.N`)

Tests scope across both wire and checked surfaces:
- Scenarios A–G: construct via the checked bundle (with the
    length-equality proof discharged by `rfl` when definitional).
- Scenario H (NEW per Codex P1): wire-list length mismatch causes
    `decodeBoundedInputCertificateData` to return `none`.

Removed in earlier cycles:
- v3 removed `BoundedInputOrbitCertificate` + `checkBoundedCertificate_sound`
    (v4 in commit sequence, `bd3d8b7`).
- v3 removed Scenario E (polymorphic apply-the-theorem) — that
    referenced the now-removed soundness theorem.

Scenarios (8 total, all compile-checked by `lake build CollatzResearch.Q5VerifierTests` in GitHub CI):
- A: positive — basic valid (N=1, claim `.singleton 1`, trajectory `[1]`)
- B: negative — step + terminal mismatch (trajectory `[1, 2]`)
- C: negative — head mismatch (trajectory `[2]` for x=1)
- D: positive — N=2 with two canonical witnesses (regression for wire list)
- E: positive — N=3 with three canonical witnesses (regression for wire list)
- F: negative — terminal-claim mismatch, simple (claim `.singleton 2`)
- G: negative — terminal-claim mismatch, non-degenerate (claim `.singleton 100`)
- H: NEW per Codex P1 — malformed-length rejection (decoder returns `none`)
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
    witness at list index 0 (canonical input `i.val + 1 = 1`) with
    trajectory `[1]`. Head matches `x = 1`; no steps to verify;
    terminal `1 ∈ .singleton 1`.

    `acceleratedStep 1 = 1` because `3*1+1 = 4`, `ν₂(4) = 2`,
    so `4 / 2^2 = 1`. The trajectory from `x = 1` is `[1]`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 1,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1] }],
         claim := FiniteOrbitClaim.singleton 1 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario B (negative — step + terminal mismatch): N=1, claim
    `.singleton 1`, witness at list index 0 (canonical input 1) with
    trajectory `[1, 2]`. Head matches (1=1), but the step
    `2 = acceleratedStep 1 = 1` fails, AND the terminal `2 ∉
    .singleton 1`. Both checks fail. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 1,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1, 2] }],
         claim := FiniteOrbitClaim.singleton 1 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario C (negative — head mismatch): N=1, claim `.singleton 1`,
    witness at list index 0 (canonical input 1) with trajectory `[2]`.
    Head `2 ≠ x = 1`; the head check fails. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 1,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [2] }],
         claim := FiniteOrbitClaim.singleton 1 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario D (positive — N=2 with two canonical witnesses per
    Codex P0 fix): N=2, claim `.singleton 1`.
      rawWitnesses[0] (canonical input 1) → `[1]`
      rawWitnesses[1] (canonical input 2) →
        `[2, 7, 11, 17, 13, 5, 1]` (terminal 1 ∈ `.singleton 1`).
    Each consecutive pair is an `acceleratedStep` transition:
      acceleratedStep 2 = 7, acceleratedStep 7 = 11,
      acceleratedStep 11 = 17, acceleratedStep 17 = 13,
      acceleratedStep 13 = 5, acceleratedStep 5 = 1.

    The witness at list index `i` is reconstructed as
    `CertWitness (i.val + 1)` via `certWitness` (v4 derived view) —
    type-level canonical-input identity preserved (Codex P0 fix).
    The wire list is plain serializable data (Codex P1 fix). -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 2,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1] },
            { l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [2, 7, 11, 17, 13, 5, 1] }],
         claim := FiniteOrbitClaim.singleton 1 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario E (positive — N=3, three canonical witnesses, regression
    for wire list): N=3, claim `.singleton 1`.
      rawWitnesses[0] (canonical input 1) → `[1]`
      rawWitnesses[1] (canonical input 2) → `[2, 7, 11, 17, 13, 5, 1]`
      rawWitnesses[2] (canonical input 3) → `[3, 5, 1]`
          (acceleratedStep 3 = 5, acceleratedStep 5 = 1)

    A v3-style witness with mismatched `x` (e.g. rawWitnesses[1]
    carrying `trajectory := [99, 7, …]` whose head isn't the
    canonical input 2) would not pass `checkCertWitness` — the
    head check catches it. The wire list is in canonical order
    (Python emits index-by-index), but the trajectory HEAD inside
    each witness must equal the canonical input. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 3,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1] },
            { l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [2, 7, 11, 17, 13, 5, 1] },
            { l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [3, 5, 1] }],
         claim := FiniteOrbitClaim.singleton 1 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario F (NEW per Codex P1 of the v2 review — terminal-claim
    negative, simple): N=1, claim `.singleton 2`. Witness at list
    index 0 (canonical input 1) with trajectory `[1]`. The
    trajectory is VALID (head matches `x = 1`, no steps to verify),
    but the terminal value `1` is NOT in `.singleton 2`. The
    `checkCertWitness` terminal check (`decide (claim.Holds last)`)
    catches this. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 1,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1] }],
         claim := FiniteOrbitClaim.singleton 2 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario G (NEW per Codex P1 of the v2 review — terminal-claim
    negative, non-degenerate): N=2, claim `.singleton 100`.
      rawWitnesses[0] (canonical input 1) → `[1]` (terminal 1 NOT in
        `.singleton 100`).
      rawWitnesses[1] (canonical input 2) → `[2, 7]` (terminal 7 NOT
        in `.singleton 100`; step `7 = acceleratedStep 2` is valid).

    Both trajectories have valid head + steps, but the terminal
    claim check fails for both. The list-level
    `checkBoundedCertificate` returns `false`. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" }
    (⟨{ N := 2,
         rawWitnesses :=
           [{ l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [1] },
            { l := { leafId := "L", leafProperty := "0:0-0" },
              trajectory := [2, 7] }],
         claim := FiniteOrbitClaim.singleton 100 },
      rfl⟩ : BoundedInputCertificateData)
    = true := by
  native_decide

/-- Scenario H (NEW per Codex P1 of the v3 review — malformed-length
    rejection): the wire payload claims `N = 2` but supplies only
    ONE witness. `decodeBoundedInputCertificateData` returns `none`
    because `rawWitnesses.length = 1 ≠ N = 2`. -/
example : (decodeBoundedInputCertificateData
    { N := 2,
      rawWitnesses :=
        [{ l := { leafId := "L", leafProperty := "0:0-0" },
           trajectory := [1] }],
      claim := FiniteOrbitClaim.singleton 1 }
    : Option BoundedInputCertificateData) = none := by
  native_decide

end CollatzResearch
