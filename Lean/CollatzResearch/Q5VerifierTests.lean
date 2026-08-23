/-
Q5 PR #2 (verifier) — CI-side executable spec for the bounded-input certificate
verifier (`checkBoundedCertificate`) + soundness theorem
(`checkBoundedCertificate_sound`).

Per the Q5 spec § 6.2 (Q5 PR #2 scope):
> Q5 PR #2 (verifier — Lean-only, kernel-checked)
> Implements `BoundedInputOrbitCertificate` verification + `checkBoundedTrajectory` + `checkBoundedTrajectory_sound` theorem. Lean-only — no Python integration at this stage. No `BoundedOrbitCertificate` construction; no companion theorem modifications. Just the small verifier + soundness theorem.

These scenarios are compile-checked by `lake build CollatzResearch.Q5VerifierTests` in GitHub CI (not run locally — Lean CI is the sole validation gate per project discipline).

Per the Q5 v2 spec fix (PR #61 v2), all trajectories use correct `acceleratedStep` semantics (full 2-adic reduction of `3n+1`), NOT the standard Collatz sequence. The verifier MUST check the same `acceleratedStep` relation used by `accelerated_orbit`.

-/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputOrbitCertificate

namespace CollatzResearch

/-- A simple tree with one leaf. Used to avoid the routing complexity
    of `depthTwoTree` for the executable spec — every `x > 0` routes
    to the single leaf `L`. -/
def singleLeafTree : CoverageTree :=
  { root := .leaf { leafId := "L", leafProperty := "0:0-0" },
    leaves := [{ leafId := "L", leafProperty := "0:0-0" }],
    maxDepth := 1 }

/-- Scenario A: valid bounded-input certificate for `N = 1` with `x = 1`
    on `singleLeafTree`. The trajectory `[1]` reaches value 1, which
    satisfies `.singleton 1` (since `acceleratedStep 1 = 1`, the orbit
    is a fixed point).

    `acceleratedStep 1 = 1` because `3*1+1 = 4`, `ν₂(4) = 2`, so
    `4 / 2^2 = 1`. The trajectory from `x = 1` is `[1]`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := [{ x := 1,
                     l := { leafId := "L", leafProperty := "0:0-0" },
                     trajectory := [1] }] } = true := by
  native_decide

/-- Scenario B: invalid bounded-input certificate. The trajectory
    `[1, 2]` from `x = 1` is INVALID — `acceleratedStep 1 = 1`, not 2.
    The step `1 → 2` is not a valid `acceleratedStep` transition.
    Additionally, the final value `2` does not satisfy `.singleton 1`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := [{ x := 1,
                     l := { leafId := "L", leafProperty := "0:0-0" },
                     trajectory := [1, 2] }] } = false := by
  native_decide

/-- Scenario C: invalid bounded-input certificate — size mismatch.
    `N = 3` but only 1 witness. The verifier requires one witness per
    `x ∈ {1, ..., N}`. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 3
    { claim := FiniteOrbitClaim.singleton 1,
      N := 3,
      witnesses := [{ x := 1,
                     l := { leafId := "L", leafProperty := "0:0-0" },
                     trajectory := [1] }] } = false := by
  native_decide

/-- Scenario D: invalid bounded-input certificate — claim shape
    mismatch. `.singleton 1` but trajectory ends at `2`. The
    `claim.Holds 2` (i.e., `2 = 1`) is false. -/
example : checkBoundedCertificate singleLeafTree
    { leafId := "L", leafProperty := "0:0-0" } 1
    { claim := FiniteOrbitClaim.singleton 1,
      N := 1,
      witnesses := [{ x := 1,
                     l := { leafId := "L", leafProperty := "0:0-0" },
                     trajectory := [1, 1, 2] }] } = false := by
  native_decide

/-- Scenario E: polymorphic apply-the-theorem. Names the soundness
    theorem directly. For any tree + leaf + N + data where the
    verifier returns `true`, the soundness theorem produces the
    proof-carrying `BoundedInputOrbitCertificate`. Mirrors PR #57
    scenarios 11–12 polymorphic apply-the-instance pattern. -/
example (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (d : BoundedInputCertificateData)
    (h : checkBoundedCertificate t l N d = true) :
    BoundedInputOrbitCertificate t l N :=
  checkBoundedCertificate_sound t l N d h

end CollatzResearch
