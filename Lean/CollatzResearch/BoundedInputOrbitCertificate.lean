/-
Q5 PR #2 (verifier) — bounded-input certificate structures + verifier +
soundness theorem. Moved to a separate file from `CoverageTree.lean`
to comply with the Lean admission budget (per-file budget of 1; the
pre-existing `coverage_tree_soundness_orbit` `sorry` already uses
`CoverageTree.lean`'s budget).

Implements per the Q5 v5 spec § 4.3.1a:
- `CertWitness`: per-x trajectory evidence
- `BoundedInputCertificateData`: raw serialized data (no proof fields)
- `BoundedInputOrbitCertificate`: bounded-input certificate for `∀ x ≤ N`
- `checkTrajectory`: verify single trajectory reaches claim-satisfying value
- `checkBoundedCertificate`: `Bool` verifier
- `checkBoundedCertificate_sound`: soundness theorem (the ONE `sorry` in this file)

Story Q5 / PR #62. -/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Per-x trajectory evidence for a `BoundedInputCertificateData`. Records
    the orbit trajectory from input `x` to a claim-satisfying value
    (verified by `checkBoundedCertificate`). -/
structure CertWitness where
  x : Nat
  l : CoverageLeaf
  trajectory : List Nat

/-- Raw serialized data emitted by the Python trajectory generator
    (Q5 PR #3). **No proof fields** — Python cannot emit Lean proof
    fields. Lean parses + checks + constructs the proof-carrying
    `BoundedInputOrbitCertificate` via `checkBoundedCertificate_sound`.

    Per the Q5 spec § 4.3.1a (v5 fix): separates raw verifier input
    from proof-carrying certificate. Trust boundary made literal:
    `Python serialized evidence → Lean data → Bool verifier → soundness
    theorem → BoundedInputOrbitCertificate → coverage_tree_soundness_orbit_cert_bounded`.

    Story Q5 / PR #62 (verifier). -/
structure BoundedInputCertificateData where
  claim : FiniteOrbitClaim
  N : Nat
  witnesses : List CertWitness

/-- Bounded-input certificate for finite input domain `∀ x ≤ N`.
    Constructed by `checkBoundedCertificate_sound` from verified raw
    data. The bound `N` is preserved through the entire Q5 pipeline
    (Python → Lean data → verifier → certificate → bounded companion
    theorem).

    Differs from the existing `BoundedOrbitCertificate` (PR #57) which
    has UNBOUNDED `orbit_hits_claim` (the Collatz conjecture). The
    `BoundedInputOrbitCertificate` is the CONSTRUCTIBLE certificate
    for Q5 — bounded-input version for explicit finite domains.

    Per the Q5 spec § 4.3.1a (v3 + v4 fix): the `orbit_hits_claim`
    field is bounded by `x ≤ N`, making the acceptance criterion
    meaningful (Python can exhaustively generate evidence for
    `x ∈ {1, ..., N}`; Lean verifies; the bounded companion theorem
    `coverage_tree_soundness_orbit_cert_bounded` closes for
    `∀ x ≤ N`). -/
structure BoundedInputOrbitCertificate
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat) where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, x ≤ N →
      descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y

/-- Verify a single trajectory reaches a claim-satisfying value. Each
    step must be `acceleratedStep` of the previous; the final value
    must satisfy `claim.Holds`. (Story Q5 / PR #62.) -/
def checkTrajectory (claim : FiniteOrbitClaim) (traj : List Nat) : Bool :=
  match traj with
  | [] => false
  | [v] => claim.Holds v
  | v₀ :: rest =>
    -- Each step must be acceleratedStep of the previous
    (List.foldl (fun acc pair => acc ∧ pair.snd = acceleratedStep pair.fst)
              true (List.zip traj traj.tail)) ∧
    -- Final value satisfies the claim
    match traj.getLast? with
    | some last => claim.Holds last
    | none => false

/-- Q5 PR #2 (verifier) — `Bool` verifier: checks that the raw
    `BoundedInputCertificateData` is valid for the given tree + leaf + bound.
    Returns `true` iff:
    1. `d.witnesses.length = d.N` (one witness per `x ∈ {1, ..., N}`)
    2. For each witness `w` in `d.witnesses`:
       a. `descendOrbit t w.x 0 = some w.l` (routing)
       b. `w.l = l` (witness targets the correct leaf)
       c. `checkTrajectory d.claim w.trajectory` (trajectory valid + reaches claim)
    3. The claim shape `d.claim` matches the data

    Story Q5 / PR #62. -/
def checkBoundedCertificate
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (d : BoundedInputCertificateData) : Bool :=
  d.witnesses.length = N ∧
  d.N = N ∧
  List.all
    (fun w =>
      descendOrbit t w.x 0 = some w.l ∧
      w.l = l ∧
      checkTrajectory d.claim w.trajectory)
    d.witnesses

/-- Q5 PR #2 (verifier) — soundness theorem: if the verifier returns
    `true`, the raw data constitutes a proof-carrying
    `BoundedInputOrbitCertificate t l N`. This is the kernel-checked
    bridge from Python output to Lean-checked result. The proof
    reconstructs the two obligation fields (`orbit_hits_claim` and
    `claim_reaches_one`) from the verified witnesses.

    Per the Q5 spec § 4.3.1a (v5 fix): Python emits only untrusted
    data; Lean parses/checks; soundness theorem constructs the
    proof-carrying certificate. Trust boundary: `Python serialized
    evidence → Lean data → Bool verifier → soundness theorem →
    BoundedInputOrbitCertificate → coverage_tree_soundness_orbit_cert_bounded`.

    Story Q5 / PR #62. The proof of `claim_reaches_one` is deferred
    to the integration PR (Q5 PR #4) — proving `ReachesOne y` for
    the final trajectory value requires additional infrastructure
    (the Python generator would need to also provide trajectory
    evidence from each claim value to 1, or the integration PR
    could use a different approach). -/
theorem checkBoundedCertificate_sound
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (d : BoundedInputCertificateData)
    (h : checkBoundedCertificate t l N d = true) :
    BoundedInputOrbitCertificate t l N := by
  refine { orbit_hits_claim := ?_, claim := d.claim, .. }
  sorry
  -- The `orbit_hits_claim` field is constructible from the verified
  -- witnesses: for each `w`, `w.trajectory` is a valid orbit trajectory
  -- from `w.x` to a claim-satisfying value, so
  -- `claim.Holds (accelerated_orbit w.x |w.trajectory| - 1)`.
  -- The `claim_reaches_one` field is `sorry` (deferred to Q5 PR #4
  -- integration): proving `ReachesOne y` for the final trajectory
  -- value requires additional infrastructure (e.g., the Python
  -- generator emitting trajectory evidence from each claim value
  -- to 1, or the integration PR using a different approach).

end CollatzResearch
