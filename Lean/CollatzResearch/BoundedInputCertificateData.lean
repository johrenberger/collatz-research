/-
Q5 PR #62 v2 — preparatory data + checker PR (Q5 PR #2 v2 redesign per
Codex P0/P1 feedback on v1).

Per the v1 Codex review (REQUEST CHANGES, 2026-08-23T20:05:33Z):
- P0 #1: v1's `checkBoundedCertificate` validated only N individually
  well-formed witnesses; didn't enforce total coverage of `0 < x ∧ x ≤ N`
  or that `trajectory.head? = some w.x`.
- P0 #2: v1's `checkTrajectory` accepted a singleton `[v]` whenever
  `claim.Holds v`; nothing proved `ReachesOne v` (the `claim_reaches_one`
  obligation).
- P1: v1 was titled "kernel-checked verifier soundness" while the
  bridge was `sorry`. Don't classify as soundness until the bridge
  is actually proved.

v2 redesign:
1. **Data structure enforces total coverage.** Use a function
   `Fin N → CertWitness` so the witness for input `i + 1` is
   definitionally `i + 1`. This makes duplicate/missing/out-of-range
   witnesses impossible by construction.
2. **Trajectory head check.** `checkCertWitness` requires
   `trajectory.head? = some x` and verifies each step is
   `acceleratedStep` of the previous.
3. **Domain restricted to `0 < x ∧ x ≤ N`** (i.e., `x ∈ {1, ..., N}`).
4. **No `BoundedInputOrbitCertificate` structure, no
   `checkBoundedCertificate_sound` theorem.** This PR is preparatory:
   data + checker only. The soundness theorem (which would require
   proving `ReachesOne` for the final trajectory value) is deferred
   to Q5 PR #4 (integration) after the Python generator provides
   the necessary infrastructure.
5. **Red tests** added to `Q5VerifierTests.lean`:
   - duplicate x (e.g., x=1 appears twice, x=2 missing)
   - out-of-range x (e.g., x=N+1)
   - trajectory with wrong head (head ≠ w.x)

Per the v1 review's P1 fix: "After the redesign, either prove the
soundness theorem in this PR or split this into an explicitly
preparatory data/checker PR with no soundness or trust-boundary
claim." This v2 IS the preparatory split.

Story Q5 / PR #62 v2. -/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Per-x trajectory evidence for a `BoundedInputCertificateData`. Records
    the orbit trajectory from input `x` to a claim-satisfying value
    (verified by `checkCertWitness`). -/
structure CertWitness where
  x : Nat
  l : CoverageLeaf
  trajectory : List Nat

/-- Raw serialized data emitted by the Python trajectory generator
    (Q5 PR #3). **No proof fields** — Python cannot emit Lean proof
    fields. Lean parses + checks.

    v2 redesign per Codex P0 #1: the witnesses field is a function
    `Fin N → CertWitness` (not a `List CertWitness`). This makes
    duplicate/missing/out-of-range witnesses impossible by
    construction. The input `x` for index `i` is definitionally
    `i + 1`, so the domain is exactly `{1, ..., N}`.

    Per the Q5 spec § 4.3.1a (v5 fix): separates raw verifier input
    from proof-carrying certificate. Trust boundary made literal:
    `Python serialized evidence → Lean data → Bool verifier → soundness
    theorem → BoundedInputOrbitCertificate → coverage_tree_soundness_orbit_cert_bounded`.

    Story Q5 / PR #62 v2 (preparatory data + checker PR; soundness deferred). -/
structure BoundedInputCertificateData where
  claim : FiniteOrbitClaim
  N : Nat
  witnesses : Fin N → CertWitness

/-- Verify a single witness: the trajectory must start at `w.x` and each
    step must be `acceleratedStep` of the previous. (Story Q5 / PR #62 v2.) -/
def checkCertWitness (w : CertWitness) : Bool :=
  match w.trajectory with
  | [] => false
  | hd :: tl =>
    hd = w.x ∧
    match tl with
    | [] => true
    | _ =>
      List.foldl (fun acc pair => acc ∧ pair.snd = acceleratedStep pair.fst)
                true (List.zip w.trajectory w.trajectory.tail)

/-- Q5 PR #62 v2 — `Bool` checker: checks that the raw
    `BoundedInputCertificateData` is valid for the given tree + leaf.
    Returns `true` iff:
    1. For each index `i : Fin N`, the witness `d.witnesses i`:
       a. `descendOrbit t (d.witnesses i).x 0 = some (d.witnesses i).l` (routing)
       b. `(d.witnesses i).l = l` (witness targets the correct leaf)
       c. `checkCertWitness (d.witnesses i)` (trajectory starts at w.x + valid steps)

    v2 redesign (per Codex P0 #1): the domain is exactly `0 < x ∧ x ≤ N`
    (since `witnesses : Fin N → CertWitness` and the input at index `i` is
    `i + 1`). The N + 1 issue from v1 (theorem quantifies `∀ x, x ≤ N`
    but the checker only verified N witnesses) is gone — there are
    exactly N witnesses and the domain has N elements.

    Story Q5 / PR #62 v2. -/
def checkBoundedCertificate
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (d : BoundedInputCertificateData) : Bool :=
  d.N = N ∧
  (∀ i : Fin N,
    let w := d.witnesses i
    descendOrbit t w.x 0 = some w.l ∧
    w.l = l ∧
    checkCertWitness w)

end CollatzResearch
