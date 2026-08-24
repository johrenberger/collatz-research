/-
Q5 PR #62 v3 — applies Codex REVIEW feedback (REQUEST CHANGES,
2026-08-23T20:53:23Z, review #5003345398) on the v2 redesign
commit (`bd3d8b7`).

Per the v2 review (johrenberger on `bd3d8b7`):
- [P0] `witnesses : Fin N → CertWitness` did NOT make duplicate/
    missing/out-of-range witness inputs impossible. `CertWitness.x`
    was an independent `Nat` field; the function could return
    `x = 1` at every index, or `x = N + 1`. The implementation also
    had a dependent-index transport bug: `d.witnesses` is indexed
    by `Fin d.N`, but the check loop used `i : Fin N` (the external
    `N` argument); `d.N = N` is a Boolean conjunct that does NOT
    transport dependent indices.
    **v3 fix:** parameterize `CertWitness (x : Nat)` (drop the
    `x` field); `witnesses` is now `(i : Fin N) → CertWitness
    (i.val + 1)`. The input at index `i` is now type-level
    `CertWitness (i.val + 1)`, so duplicate/missing/out-of-range
    witnesses are impossible by construction. The external `N : Nat`
    parameter is removed from `checkBoundedCertificate` — the bound
    comes from `d.N` directly, eliminating the dependent-index
    transport issue entirely.

- [P1] The checker never used `d.claim`. `checkCertWitness` verified
    only start + transition relation; it did not require the terminal
    state to satisfy `claim.Holds`. This contradicted the structure
    and docstrings' "trajectory … to a claim-satisfying value"
    contract, and left no checked artifact from which a later
    integration theorem can derive `orbit_hits_claim`.
    **v3 fix:** `checkCertWitness` now takes `claim : FiniteOrbitClaim`
    and requires `decide (claim.Holds last)` (where `last` is the
    final trajectory value). This restores the documented contract.

- [P2] PR title/body still advertised `BoundedInputOrbitCertificate`,
    `checkBoundedCertificate_sound`, an admission, and a "kernel-
    checked verifier + soundness theorem" while the v2 diff
    deliberately contained neither.
    **v3 fix:** updated file header + updated PR title/body
    separately (this file is data + checker only, no soundness claim).

Open gates addressed in v3:
- v3 diff corrects the dependent-index mismatch (P0).
- v3 diff adds the canonical-input and terminal-claim negative tests (P1).
- Soundness/integration work remains deferred to Q5 PR #4.

Story Q5 / PR #62 v3 (preparatory raw-data + transition + terminal-
claim checker; soundness theorem deferred to Q5 PR #4 integration). -/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-- Per-x trajectory evidence for a `BoundedInputCertificateData`.
    The input `x` is a **type parameter** (not a field), so duplicate/
    missing/out-of-range witnesses are impossible by construction:
    the carriers of `BoundedInputCertificateData.witnesses` are
    indexed by `Fin N` with each witness carrying the type-level
    input `i.val + 1`.

    Story Q5 / PR #62 v3 (canonical-input identity per Codex P0 fix). -/
structure CertWitness (x : Nat) where
  l : CoverageLeaf
  trajectory : List Nat

/-- Raw serialized data emitted by the Python trajectory generator
    (Q5 PR #3). **No proof fields** — Python cannot emit Lean proof
    fields. Lean parses + checks.

    v3 redesign (per Codex P0): `witnesses` is now
    `(i : Fin N) → CertWitness (i.val + 1)` (function indexed by
    `Fin N`, with each witness type-parameterized by its canonical
    input `i.val + 1`). The input identity is canonical by construction:
    the witness at index `i` is **structurally** for input `i.val + 1`;
    no separate `x` field needed.

    Domain: `{1, ..., N}` (uniformly `0 < x ∧ x ≤ N`).

    Per the Q5 v5 spec § 4.3.1a, the trust boundary is literal:
    `Python serialized evidence → Lean data → Bool verifier →
    soundness theorem → BoundedInputOrbitCertificate →
    coverage_tree_soundness_orbit_cert_bounded`.

    Story Q5 / PR #62 v3 (preparatory raw-data + transition + terminal-
    claim checker; soundness theorem deferred to Q5 PR #4 integration). -/
structure BoundedInputCertificateData where
  claim : FiniteOrbitClaim
  N : Nat
  witnesses : (i : Fin N) → CertWitness (i.val + 1)

/-- Verify a single witness: the trajectory must (1) start at the
    canonical input `x` (the type parameter), (2) target the leaf `l`,
    (3) route through `t` to `l`, (4) reach a `claim.Holds`-satisfying
    value at the terminal step, and (5) have each consecutive pair be
    an `acceleratedStep` transition.

    v3 redesign (per Codex P1): the `claim` parameter makes the
    documented "trajectory … to a claim-satisfying value" contract
    explicit. Without this check, the checker would accept trajectories
    that end outside the claim, leaving no checked artifact from which
    a later integration theorem can derive `orbit_hits_claim`.

    Returns `true` iff ALL FIVE conditions hold. -/
def checkCertWitness (x : Nat) (claim : FiniteOrbitClaim)
    (t : CoverageTree) (l : CoverageLeaf) (w : CertWitness x) : Bool :=
  match w.trajectory with
  | [] => false
  | hd :: _ =>
    hd = x ∧
    w.l = l ∧
    descendOrbit t x 0 = some w.l ∧
    (match w.trajectory.getLast? with
     | some last => decide (claim.Holds last)
     | none => false) ∧
    List.foldl (fun acc pair => acc ∧ pair.snd = acceleratedStep pair.fst)
              true (List.zip w.trajectory w.trajectory.tail)

/-- Q5 PR #62 v3 — `Bool` checker for the raw
    `BoundedInputCertificateData`. Returns `true` iff for each
    `i : Fin d.N`, the witness `d.witnesses i` is valid for input
    `x = i.val + 1`.

    v3 redesign (per Codex P0): the bound comes from `d.N` directly
    (no external `N : Nat` parameter); there are no dependent-index
    transports needed. The witness at index `i` is structurally tied
    to input `i.val + 1`.

    The full check passes only when EVERY witness satisfies
    `checkCertWitness (i.val + 1) d.claim t l`.

    Story Q5 / PR #62 v3 (preparatory raw-data + transition + terminal-
    claim checker; soundness theorem deferred to Q5 PR #4 integration). -/
def checkBoundedCertificate
    (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData) : Bool :=
  List.foldl (fun acc i =>
    let x := i.val + 1
    let w := d.witnesses i
    acc ∧ checkCertWitness x d.claim t l w)
    true (List.finRange d.N)

end CollatzResearch
