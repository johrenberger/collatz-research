/-
Q5 PR #3 v3 — parser rejection tests (per Codex review on PR #63 v2).

The v2 Codex review (`PRR_kwDOTuMD788AAAABLG_dzA`, 2026-08-27T12:02:23Z)
identified two issues with v2's test suite:
  - [P2] All rejection tests asserted only `.isError`; none asserted
    the documented stable machine-readable category/prefix. Per
    Codex: "permits regressions from `UNSUPPORTED_SCHEMA_VERSION` to
    an unrelated generic error while CI stays green."
  - [P2] `ParseError` taxonomy declared but unused in the API.

The v2 review reply (`issuecomment-5420047917`) claimed:
  "Each assertion checks the documented rejection category via
   `Except.isError` + `String.startsWith` prefix match — not just
   `.isError`. Asserting category (not just failure) is what the
   review asked for."
This overstated what was implemented. Codex disproved this by
inspecting `BoundedInputCertificateParserTests.lean:17-209` directly.
v3 fixes this honestly by pattern-matching on the `ParseError`
constructor itself (compiler-evaluated via `native_decide` -- which
    rests on the core native-decide axiom, not kernel-checked --), not via
brittle `String.startsWith` on the `toString` rendering.

v3 contract:
  - Each rejection test asserts `parseBoundedInputCertificateWire "..."
    = .error .ConstructorName` (or `.error (.ConstructorName args)`
    for constructors with arguments).
  - The constructor + arguments uniquely identify the rejection
    category + relevant field. No more `.isError = true`.
  - The positive test asserts `.isOk = true` (no need to name the
    specific `FiniteOrbitClaim` constructor in the test).

### v4 (PR #63, review `PRR_kwDOTuMD788AAAABLVa5sw`, 2026-08-28T22:46:03Z)

Two findings from v3 review, addressed in v4:

  - [P1] Python CI red on `ruff format --check .` — handled in
    `python/collatz_research/bounded_input_certificate.py` (formatting-
    only); this test file already formatted.
  - [P2] Typed error API still conflated an absent field with a
    present field of the wrong type — R6 supplied numeric
    `schemaVersion: 42` yet expected `.missingField "schemaVersion"`,
    contradicting the documented `WRONG_TYPE` category. **R6 now
    asserts `.wrongTypeAt "string" "$.schemaVersion"`.** New scenarios
    R6b–R6g assert wrong-type rejection for `N`, `claim`,
    `rawWitnesses`, `leafId`, `leafProperty`, and `trajectory` (the
    field-level split that the v4 parser enforces). New scenarios
    R5b/R5c/R5e/R5h assert the matching missing-field rejection (the
    complementary half of the absent-vs-wrong-type split).

Q5 PR #3 v3 also adds R15/R16 (non-ASCII leafId / leafProperty) + R17
(surrogate half in `\uXXXX` escape) for the ASCII-only contract
required by Codex P1 (`PRR_kwDOTuMD788AAAABLG_dzA`).

All tests use `native_decide` for compiler-evaluated reduction. This
rests on the core native-decide axiom rather than on kernel reduction: the
parser is a `partial def` mutual block, so the kernel cannot reduce
it and plain `decide` does not apply here. Per the
Q5 v4 spec, parser correctness is established by these scenarios
executing to the expected Bool value.

Story Q5 / PR #3 v3 (parser + 20 rejection tests; soundness
integration deferred to Q5 PR #4). -/

import CollatzResearch.BoundedInputCertificateParser
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## Test helpers -/

/-- True iff the parse failed with exactly the given error category. Keeps the
    rejection-category assertion compiler-evaluated without needing a
    `DecidableEq` instance for the whole wire payload. -/
def rejectedWith {α : Type} (r : Except ParseError α) (e : ParseError) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

/-! ## POSITIVE: valid producer fixture parses correctly -/

/-- POSITIVE — valid producer fixture (N=1, claim `.singleton 1`,
    trajectory `[1]`). Matches PR #62 v5 scenario A. -/
example : (parseBoundedInputCertificateWire ("{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"0:0-0\"}," ++
    "\"trajectory\":[1]}]}")).isOk = true := by
  native_decide

/-! ## P1 #2 — Strict JSON parsing (rejections) -/

/-- R1 — malformed JSON (unbalanced brace: missing closing brace).
    The parser tries to read the first key as a string, so the
    actual rejection is `.expectedChar '"'` on the literal 'm'. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{malformed}")
    )
    (.expectedChar '"' "'m'") = true := by
  native_decide

/-- R2 — leading zero in number (N=01). Per strict JSON, integers
    cannot have leading zeros (only "0" itself is allowed). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":01," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    .leadingZeroNumber = true := by
  native_decide

/-- R3 — duplicate top-level key (`schemaVersion` appears twice). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.duplicateKey "schemaVersion" "$") = true := by
  native_decide

/-! ## P1 #1 — Schema constraints (rejections) -/

/-- R4 — wrong schema version (`"2.0"` instead of `"1.0"`). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"2.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.unsupportedSchemaVersion "2.0") = true := by
  native_decide

/-- R5 — missing required field `claim`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.missingField "claim") = true := by
  native_decide

/-- R6 — wrong type for `schemaVersion` (int instead of string).
    v4: changed from `.missingField "schemaVersion"` (v3, which conflated
    absent with wrong type) to `.wrongTypeAt "string" "$.schemaVersion"`.
    Per Codex review `PRR_kwDOTuMD788AAAABLVa5sw` P2. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":42," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.wrongTypeAt "string" "$.schemaVersion") = true := by
  native_decide

/-- R5b — missing required field `schemaVersion`. Complements R6:
    R6 covers wrong-type (key present, wrong JSON type); R5b covers
    missing (key absent). v4 per Codex review
    `PRR_kwDOTuMD788AAAABLVa5sw` P2 (split absent from wrong type). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.missingField "schemaVersion") = true := by
  native_decide

/-- R5c — missing required field `N`. Complements R8 (zero value). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.missingField "N") = true := by
  native_decide

/-- R5d — missing required field `rawWitnesses`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1}")
    )
    (.missingField "rawWitnesses") = true := by
  native_decide

/-- R5e — missing required field `l` inside a witness. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"trajectory\":[1]}]}")
    )
    (.missingField "l") = true := by
  native_decide

/-- R5f — missing required field `leafId` inside `l`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.missingField "leafId") = true := by
  native_decide

/-- R5g — missing required field `leafProperty` inside `l`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.missingField "leafProperty") = true := by
  native_decide

/-- R5h — missing required field `trajectory` inside a witness. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}}]}")
    )
    (.missingField "trajectory") = true := by
  native_decide

/-- R6b — wrong type for `N` (string instead of non-negative integer).
    v4 per Codex review `PRR_kwDOTuMD788AAAABLVa5sw` P2. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":\"x\"," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.wrongTypeAt "non-negative integer" "$.N") = true := by
  native_decide

/-- R6c — wrong type for `claim` (number instead of object).
    `parseFiniteOrbitClaim` delegates the wrong-type case to
    `.notAnObject "claim"`, which is in the WRONG_TYPE category
    (consistent with `.wrongTypeAt` for top-level scalar fields). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":42," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.notAnObject "claim") = true := by
  native_decide

/-- R6d — wrong type for `rawWitnesses` (string instead of array). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":\"x\"}")
    )
    (.wrongTypeAt "non-empty array" "$.rawWitnesses") = true := by
  native_decide

/-- R6e — wrong type for `leafId` (number instead of string). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":42,\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.wrongTypeAt "string" "rawWitnesses[0].l.leafId") = true := by
  native_decide

/-- R6f — wrong type for `leafProperty` (number instead of string). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":42}," ++
        "\"trajectory\":[1]}]}")
    )
    (.wrongTypeAt "string" "rawWitnesses[0].l.leafProperty") = true := by
  native_decide

/-- R6g — wrong type for `trajectory` (string instead of array). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":\"x\"}]}")
    )
    (.wrongTypeAt "non-empty array" "rawWitnesses[0].trajectory") = true := by
  native_decide

/-- R7 — unknown nested field inside `claim` (`extra` not in schema). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"singleton\",\"n\":1,\"extra\":1}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.unknownField "extra" "claim") = true := by
  native_decide

/-- R7b — unknown nested field inside witness `l` (`bogus` not in schema). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"singleton\",\"n\":1}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\",\"bogus\":1}," ++
        "\"trajectory\":[1]}]}")
    )
    (.unknownField "bogus" "rawWitnesses[0].l") = true := by
  native_decide

/-- R8 — numeric lower bound violated: `N = 0` (must be ≥ 1). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":0," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    .nMustBePositive = true := by
  native_decide

/-- R8b — numeric lower bound violated: singleton `n = 0`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"singleton\",\"n\":0}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    .singletonNMustBePositive = true := by
  native_decide

/-- R8c — numeric lower bound violated: bounded `K = 0`. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"bounded\",\"K\":0}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    .boundedKMustBePositive = true := by
  native_decide

/-- R9 — empty `leafId` (must be non-empty string). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    .emptyLeafId = true := by
  native_decide

/-- R10 — empty `trajectory` array (must have ≥ 1 entry). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[]}]}")
    )
    .emptyTrajectory = true := by
  native_decide

/-- R11 — zero trajectory entry (must be ≥ 1). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[0]}]}")
    )
    (.trajectoryEntryMustBePositive 0) = true := by
  native_decide

/-- R12 — unsupported claim tag (`{"type":"interval"}` is not a
    FiniteOrbitClaim constructor). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"interval\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.unknownClaimTag "interval") = true := by
  native_decide

/-- R13 — top-level is not a JSON object (it's an array). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("[]")
    )
    (.notAnObject "$") = true := by
  native_decide

/-- R14 — unknown top-level field (`debug` not in schema v1.0). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]," ++
        "\"debug\":1}")
    )
    (.unknownField "debug" "$") = true := by
  native_decide

/-! ## P1 (v3) — ASCII-only contract on `leafId` / `leafProperty`

Per Codex review `PRR_kwDOTuMD788AAAABLG_dzA` P1: parser must reject
non-ASCII chars in identifier fields (mirroring schema `pattern` +
producer `_validate_ascii_identifier`). The parser enforces this via
`checkAscii` at the schema layer in `parseCertWitnessWire`. -/

/-- R15 — non-ASCII char in `leafId` (U+00E9 LATIN SMALL LETTER E
    WITH ACUTE = 0xE9). Mirrors the v2 surrogate-pair bug: a UTF-8
    byte sequence the parser used to accept silently. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"" ++ s!"{Char.ofNat 0xE9}" ++
        "\",\"leafProperty\":\"p\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.nonAsciiChar "rawWitnesses[0].l.leafId" 0xE9) = true := by
  native_decide

/-- R16 — non-ASCII char in `leafProperty` (U+00E9 = 0xE9). -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\"," ++
        "\"claim\":{\"type\":\"empty\"}," ++
        "\"N\":1," ++
        "\"rawWitnesses\":[" ++
        "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"" ++ s!"{Char.ofNat 0xE9}" ++
        "\"}," ++
        "\"trajectory\":[1]}]}")
    )
    (.nonAsciiChar "rawWitnesses[0].l.leafProperty" 0xE9) = true := by
  native_decide

/-- R17 — surrogate half in `\uXXXX` escape (U+D83D = 0xD83D, the
    high half of an emoji surrogate pair). The v2 parser rejected
    this correctly but the producer (`ensure_ascii=True`) emitted
    these pairs from non-BMP input. v3's ASCII-only contract makes
    the producer reject such input upstream; the parser still rejects
    it defensively. -/
example : rejectedWith
    (parseBoundedInputCertificateWire
        ("{\"schemaVersion\":\"1.0\",\"claim\":{\"type\":\"empty\"},\"N\":1,\"rawWitnesses\":[{\"l\":{\"leafId\":\"\\uD83D\",\"leafProperty\":\"p\"},\"trajectory\":[1]}]}")
    )
    .surrogateInUnicodeEscape = true := by
  native_decide

end CollatzResearch
