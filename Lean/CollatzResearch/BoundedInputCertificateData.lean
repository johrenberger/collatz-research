/-
Q5 PR #62 v5 — re-scope per Codex REVIEW feedback
(REQUEST CHANGES, 2026-08-24T12:12:18Z, review `PRR_kwDOTuMD788AAAABKnp6Ug`)
on the v4 wire/checked-split commit (`b8b3687`).

Per the v4 review (johrenberger on `b8b3687`):
- [P1] `BoundedInputCertificateWire` is an in-memory Lean record, not
    a serialized-certificate parser. `decodeBoundedInputCertificateData`
    accepts an already-constructed Lean value and checks only list
    length; it never consumes JSON/text, rejects malformed fields/types,
    or establishes a format/schema-version boundary. Consequently, the
    module does not yet implement the documented path "Python serialized
    evidence → Lean wire."

    **v5 fix (re-scope, not parser):** the wire/checked split is the
    right architecture, but this PR is correctly described as
    "in-memory wire model + structural validation" — NOT a complete
    parser. The v4 file incorrectly called the records "directly
    serializable from Python"; that wording is removed in v5. JSON
    parsing (consuming `String`/`ByteArray` → `BoundedInputCertificateWire`
    with explicit rejection of malformed JSON, wrong schema version,
    missing fields, wrong field types, malformed trajectory entries)
    is deferred to **Q5 PR #3 (Python external generator + Lean JSON
    parser)**.

    Alternative P1 path (NOT taken): add the small JSON-to-
    `BoundedInputCertificateWire` parser and parser-rejection tests
    here. Trade-off: makes this PR larger (~100 lines of parser code +
    tests) but keeps Q5 PR #3 producer-only. Re-scoping was chosen
    because (a) the Q5 4-PR split already places producer-side work in
    PR #3, (b) keeping PR #62 small preserves the architectural-review
    surface (wire/checked split) as the main change, (c) JSON parsing
    is mechanical plumbing that pairs naturally with the producer
    (one PR, both sides of the same boundary).

- [P2] PR body — it still described the removed v3 API and seven
    scenarios. **v5 fix:** PR body updated to the v4
    `CertWitnessWire` + `BoundedInputCertificateWire` + checked-bundle
    API and 8 scenarios (A–G + new H malformed-length rejection). The
    title was already correctly re-scoped in v3 (`bd3d8b7`).

Open gates addressed in v5:
- v5 diff updates the in-memory-model wording (P1): the records are
    no longer called "directly serializable"; JSON parsing is
    explicitly deferred to Q5 PR #3.
- v5 diff updates the PR body to match the v4 API + 8 scenarios (P2).
- Wire/checked split (v4) preserved as-is.
- Soundness/integration work remains deferred to Q5 PR #4.

Story Q5 / PR #62 v5 (in-memory wire model + structural validation;
JSON parsing deferred to Q5 PR #3; soundness theorem deferred to
Q5 PR #4). -/

import CollatzResearch.CoverageTree

namespace CollatzResearch

/-! ## Wire model — IN-MEMORY representation of the wire format

These structures model the wire payload that Python emits and Lean
checks. They are an IN-MEMORY representation only — JSON parsing
(consuming a `String`/`ByteArray` and producing one of these values,
with explicit rejection of malformed JSON, wrong schema version,
missing fields, wrong field types, malformed trajectory entries) is
deferred to **Q5 PR #3 (Python external generator + Lean JSON parser)**.

What is established in this PR:
  * The shape of the payload (`BoundedInputCertificateWire`):
    `N : Nat` + `rawWitnesses : List CertWitnessWire` + `claim : FiniteOrbitClaim`.
  * Structural validation: `decodeBoundedInputCertificateData` rejects
    mismatched list length (returns `none`).
  * The wire/checked split: `BoundedInputCertificateData` is the
    checked bundle (wire + `length_ok` proof).
  * The indexed view: `BoundedInputCertificateData.certWitness`
    reconstructs `(i : Fin d.wire.N) → CertWitness (i.val + 1)` via
    `List.get` (type-level canonical-input identity preserved).

What is NOT established in this PR (deferred to Q5 PR #3):
  * Parsing JSON strings / byte arrays into `BoundedInputCertificateWire`.
  * Schema versioning (the on-wire `schemaVersion` field).
  * Rejection of malformed field types, missing fields, malformed
    trajectory entries, unsupported claim tags.
  * Producer-side generation (Python trajectory generator emitting JSON).

NO proof fields on the wire model (Lean proofs are kernel artifacts;
Python cannot emit them). NO `x` parameter on `CertWitnessWire` —
the canonical input is encoded by list position
(`rawWitnesses[i]` represents input `i + 1`).

Per the Q5 v5 spec § 4.3.1a, the trust boundary is literal:
  `Python serialized evidence → (Q5 PR #3 JSON parser) →
   Lean wire → Lean checked → Bool verifier → soundness theorem
   (Q5 PR #4) → BoundedInputOrbitCertificate →
   coverage_tree_soundness_orbit_cert_bounded`. -/

/-- Per-input trajectory evidence — wire model. The canonical input
    `x` is NOT stored here; it is encoded by the witness's POSITION
    in the list (witness at index `i` carries canonical input `i + 1`).
    This is an IN-MEMORY model; external serialization (JSON /
    byte-array encoding) is Q5 PR #3. -/
structure CertWitnessWire where
  l : CoverageLeaf
  trajectory : List Nat

/-- Checked per-input trajectory evidence. The index `x` is phantom in the
    runtime payload, but records the canonical input at the type level once a
    wire witness has been selected by list position. -/
structure CertWitness (x : Nat) where
  l : CoverageLeaf
  trajectory : List Nat

/-- Wire payload — IN-MEMORY model. NO proof fields. The canonical
    list-position interpretation:
      witness at list index `i` carries canonical input `i + 1`.
    Domain: `{1, ..., N}` (uniformly `0 < x ∧ x ≤ N`).

    External JSON serialization/parsing is Q5 PR #3 (Python external
    generator + Lean JSON parser with rejection tests). -/
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
