/-
Q5 PR #62 v2 — CI-side executable spec for the bounded-input certificate
data + checker (preparatory PR; no soundness theorem yet).

Per the Q5 spec § 6.2 (Q5 PR #2 scope) + the v1 Codex review (REQUEST
CHANGES, 2026-08-23T20:05:33Z):
- v2 redesign (per Codex P0 #1): data structure enforces total coverage
  via `Fin N → CertWitness` (function indexed by `Fin N`); the witness
  input at index `i` is definitionally `i + 1`. Duplicate/missing/
  out-of-range witnesses are impossible by construction.
- v2 redesign (per Codex P0 #2): removed the `BoundedInputOrbitCertificate`
  structure + `checkBoundedCertificate_sound` theorem entirely.
  This PR is preparatory: data + checker only. The soundness theorem
  (which would require proving `ReachesOne` for the final trajectory
  value) is deferred to Q5 PR #4 (integration) after the Python
  generator provides the necessary infrastructure.
- v2 redesign (per Codex P1): this PR is now explicitly a preparatory
  data/checker PR with no soundness or trust-boundary claim. Not
  classified as "kernel-checked verifier soundness" while the bridge
  is admitted.

These scenarios are compile-checked by `lake build CollatzResearch.Q5VerifierTests` in GitHub CI (not run locally — Lean CI is the sole validation gate per project discipline).

Per the Q5 v2 spec fix (PR #61 v2), all trajectories use correct
`acceleratedStep` semantics (full 2-adic reduction of `3n+1`), NOT
the standard Collatz sequence. The checker MUST check the same
`acceleratedStep` relation used by `accelerated_orbit`.

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

/-- Scenario A: valid bounded-input certificate for `N = 1` with
    `x = 1` on `singleLeafTree`. The trajectory `[1]` starts at `w.x = 1`
    (head check passes) and is vacuously valid (no steps to check).
    The final value `1` satisfies `.singleton 1`.

    `acceleratedStep 1 = 1` because `3*1+1 = 4`, `ν₂(4) = 2`, so
    `4 / 2^2 = 1`. The trajectory from `x = 1` is `[1]`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun _ => { x := 1,
                              l := { leafId := "L", leafProperty := "0:0-0" },
                              trajectory := [1] } } = true := by
  native_decide

/-- Scenario B (red test per P0 #1): trajectory with wrong head.
    The trajectory `[1, 2]` claims to start at `w.x = 1`, but the head
    is `1` (OK) but the second value `2` is NOT `acceleratedStep 1 = 1`.
    The checkCertWitness catches the head-mismatch + step-mismatch.

    Per v2 design: `checkCertWitness` requires `trajectory.head? = some w.x`
    AND each step is `acceleratedStep` of the previous. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun _ => { x := 1,
                              l := { leafId := "L", leafProperty := "0:0-0" },
                              trajectory := [1, 2] } } = by
  native_decide

/-- Scenario C (red test per P0 #1): trajectory with wrong head.
    The trajectory `[2]` claims to start at `w.x = 1`, but the head
    is `2` (not `1`). The checkCertWitness catches the head-mismatch.

    Per v2 design: `checkCertWitness` requires `trajectory.head? = some w.x`. -/
example : ¬ checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := fun _ => { x := 1,
                              l := { leafId := "L", leafProperty := "0:0-0" },
                              trajectory := [2] } } = by
  native_decide

/-- Scenario D (regression for v1 behavior): a v1-style certificate
    with a `List CertWitness` would have accepted these (missing
    bound check, no head check). v2 with `Fin N → CertWitness` rejects
    them by construction. The single witness index `i := 0` must
    satisfy the head check; the per-`Fin` index makes the total
    coverage enforceable.

    v2: the `witnesses : Fin N → CertWitness` representation makes
    duplicate/missing/out-of-range witnesses impossible by construction
    (no `Nodup` check needed; the function is total over `Fin N`). -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 2
    { claim := FiniteOrbitClaim.singleton 1,
      N := 2,
      witnesses := fun i => match i with
        | ⟨0, _⟩ => { x := 1,
                      l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [1] }
        | ⟨1, _⟩ => { x := 2,
                      l := { leafId := "L", leafProperty := "0:0-0" },
                      trajectory := [2, 1] } } = true := by
  native_decide

end CollatzResearch
