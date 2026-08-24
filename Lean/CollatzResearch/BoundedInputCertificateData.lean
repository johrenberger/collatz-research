/-
Q5 PR #62 v4 — wire/checked split per Codex REVIEW feedback
(REQUEST CHANGES, 2026-08-24T11:57:44Z, review `PRR_kwDOTuMD788AAAABKnjGrA`)
on the v3 redesign commit (`a6ea9ad`).

Per the v3 review (johrenberger on `a6ea9ad`):
- [P1] `witnesses : (i : Fin N) → CertWitness (i.val + 1)` is an
    excellent INTERNAL checked representation, but it is NOT raw
    serialized certificate data: a JSON/Python producer cannot
    directly emit a Lean function/closure. The Q5 trust-boundary
    contract explicitly requires Python to emit serialized data
    that Lean parses.

    **v4 fix:** introduce a two-layer representation that
    explicitly distinguishes the wire payload (what Python emits;
    plain `List`, no `x` field, no proofs) from the checked
    bundle (what Lean uses internally; wire + length-equality
    proof). The canonical-index design is preserved by reconstructing
    the indexed view via `List.get`:
      - Wire: `BoundedInputCertificateWire` (NO proof fields)
                — `N : Nat`, `rawWitnesses : List CertWitnessWire`,
                  `claim : FiniteOrbitClaim`.
      - Checked: `BoundedInputCertificateData`
                — `wire : BoundedInputCertificateWire`,
                  `length_ok : wire.rawWitnesses.length = wire.N`.
      - Decoder: `decodeBoundedInputCertificateData` returns
        `Option` — `none` iff the wire list length does not match
        `wire.N` (malformed wire rejection).
      - Indexed view: `BoundedInputCertificateData.certWitness`
        returns `(i : Fin d.wire.N) → CertWitness (i.val + 1)`,
        computed from `List.get` with the length proof transporting
        `i.isLt`. The type-level identity (Codex P0 fix from review
        `#5003345398`) is preserved.

    The witness at list index `i` represents canonical input
    `i + 1` — the canonical-input identity is implicit in list
    position, not encoded as a field. Python emits a plain list,
    Lean recovers the type-level identity at the check boundary.

Open gates addressed in v4:
- v4 diff adds the wire/checked split (P1).
- v4 diff adds the malformed-length rejection test (Scenario H).
- Soundness/integration work remains deferred to Q5 PR #4.

Story Q5 / PR #62 v4 (wire/checked split + Indexed view reconstructed
via `List.get`; soundness theorem deferred to Q5 PR #4 integration). -/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-! ## Wire format — what Python emits (Q5 PR #3 external generator)

These types are directly serializable (JSON-compatible). NO proof
fields (Lean proofs are kernel artifacts; Python cannot emit them).
NO `x` parameter on `CertWitnessWire` — the canonical input is
encoded by list position (`rawWitnesses[i]` represents input `i + 1`).

Per the Q5 v5 spec § 4.3.1a, the trust boundary is literal:
  `Python serialized evidence → Lean wire → Lean checked → Bool verifier
   → soundness theorem (Q5 PR #4) → BoundedInputOrbitCertificate
   → coverage_tree_soundness_orbit_cert_bounded`. -/

/-- Per-input trajectory evidence — wire format. The canonical input
    `x` is NOT stored here; it is encoded by the witness's POSITION
    in the list (witness at index `i` carries canonical input `i + 1`).
    This keeps the wire format directly serializable from Python
    without requiring the producer to recompute / re-emit canonical
    indices per witness entry. -/
structure CertWitnessWire where
  l : CoverageLeaf
  trajectory : List Nat

/-- Wire payload — what Python emits and Lean parses. NO proof
    fields. The canonical list-position interpretation:
      witness at list index `i` carries canonical input `i + 1`.
    Domain: `{1, ..., N}` (uniformly `0 < x ∧ x ≤ N`). -/
structure BoundedInputCertificateWire where
  N : Nat
  rawWitnesses : List CertWitnessWire
  claim : FiniteOrbitClaim

/-! ## Checked format — what Lean uses internally after parsing

`BoundedInputCertificateData` is the wire payload PLUS a
length-equality proof. Inhabitation follows from
`decodeBoundedInputCertificateData` (returns `none` on length
mismatch). -/

/-- Checked bundle: wire payload + length-equality proof. The
    proof is REQUIRED at construction time (no default), so a
    malformed wire payload (`length ≠ N`) cannot inhabit
    `BoundedInputCertificateData` via the public surface. -/
structure BoundedInputCertificateData where
  wire : BoundedInputCertificateWire
  length_ok : wire.rawWitnesses.length = wire.N

/-- Decoder: returns `none` when `raw.length ≠ N` (malformed wire
    data — e.g. truncated, padded, or duplicated witness entries
    that violate the canonical list-position interpretation). -/
def decodeBoundedInputCertificateData (raw : BoundedInputCertificateWire) :
    Option BoundedInputCertificateData :=
  if h : raw.rawWitnesses.length = raw.N then
    some ⟨raw, h⟩
  else none

/-! ## Indexed canonical view — reconstructed from the wire list

The v3 Codex review (`PRR_kwDOTuMD788AAAABKjj99g`) established the
type-level canonical-input identity:
  `Fin N → CertWitness (i.val + 1)`.

The v4 Codex review (P1) requires the indexed view to be
RECONSTRUCTED from the wire list (not stored as a Lean function
field). `certWitness` is therefore a DEF (not a field) — it uses
`List.get` with the length-equality proof to transport
`i.val < wire.N` across `length_ok` to `i.val < wire.rawWitnesses.length`,
then lifts the wire witness to `CertWitness (i.val + 1)` via field
copy (the only fields are `l` and `trajectory`; no proof reattachment). -/

/-- Wire witness lifted to a `CertWitness (x : Nat)`. Trivial because
    `CertWitness` carries no proof fields — the wire values `l` and
    `trajectory` are unchanged. -/
def CertWitnessWire.toCertWitness (w : CertWitnessWire) (x : Nat) :
    CertWitness x :=
  { l := w.l, trajectory := w.trajectory }

/-- Canonical indexed view: the witness at index `i` carries
    type-level input `i.val + 1`. Reconstructed from the wire list
    via `List.get` (with the length-equality proof transporting
    `i.val < wire.N` to `i.val < wire.rawWitnesses.length`).

    This view RECONSTRUCTS the v3 type-level identity from the v4
    wire representation. -/
def BoundedInputCertificateData.certWitness (d : BoundedInputCertificateData) :
    (i : Fin d.wire.N) → CertWitness (i.val + 1) := fun i =>
  have h_pos : i.val < d.wire.rawWitnesses.length := by
    rw [d.length_ok]
    exact i.isLt
  (d.wire.rawWitnesses.get ⟨i.val, h_pos⟩).toCertWitness (i.val + 1)

/-- Verify a single witness: (1) trajectory non-empty with head
    matching `x` (the type parameter, supplied by `certWitness`
    as `i.val + 1`), (2) leaf `l` matches the witness's leaf,
    (3) `descendOrbit t x 0` routes through `t` to `l`,
    (4) terminal value satisfies `claim.Holds`, (5) every
    consecutive pair is an `acceleratedStep` transition.

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

/-- Q5 PR #62 v4 — top-level `Bool` checker for the parsed
    `BoundedInputCertificateData`. Returns `true` iff for each
    `i : Fin d.wire.N`, the reconstructed witness
    `d.certWitness i` is valid for input `x = i.val + 1`.

    The wire payload is parsed ONCE at decoder time
    (`length_ok` proof); `checkBoundedCertificate` only sees the
    checked bundle and consumes the derived canonical view.

    Story Q5 / PR #62 v4 (wire/checked split; soundness theorem
    deferred to Q5 PR #4 integration). -/
def checkBoundedCertificate
    (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData) : Bool :=
  List.foldl (fun acc i =>
    let w := d.certWitness i
    let x : Nat := i.val + 1
    acc ∧ checkCertWitness x d.wire.claim t l w)
    true (List.finRange d.wire.N)

end CollatzResearch
