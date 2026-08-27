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
constructor itself (kernel-checked via `native_decide`), not via
brittle `String.startsWith` on the `toString` rendering.

v3 contract:
  - Each rejection test asserts `parseBoundedInputCertificateWire "..."
    = .error .ConstructorName` (or `.error (.ConstructorName args)`
    for constructors with arguments).
  - The constructor + arguments uniquely identify the rejection
    category + relevant field. No more `.isError = true`.
  - The positive test asserts `.isOk = true` (no need to name the
    specific `FiniteOrbitClaim` constructor in the test).

Q5 PR #3 v3 also adds R15/R16 (non-ASCII leafId / leafProperty) + R17
(surrogate half in `\uXXXX` escape) for the ASCII-only contract
required by Codex P1 (`PRR_kwDOTuMD788AAAABLG_dzA`).

All tests use `native_decide` for kernel-checked reduction. Per the
Q5 v4 spec, parser correctness is established by these scenarios
executing to the expected Bool value.

Story Q5 / PR #3 v3 (parser + 20 rejection tests; soundness
integration deferred to Q5 PR #4). -/

import CollatzResearch.BoundedInputCertificateParser
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## Test helpers -/

def Except.isOk : Except ε α → Bool
  | .ok _ => true
  | _ => false

/-! ## POSITIVE: valid producer fixture parses correctly -/

/-- POSITIVE — valid producer fixture (N=1, claim `.singleton 1`,
    trajectory `[1]`). Matches PR #62 v5 scenario A. -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"0:0-0\"}," ++
    "\"trajectory\":[1]}]}").isOk = true := by
  native_decide

/-! ## P1 #2 — Strict JSON parsing (rejections) -/

/-- R1 — malformed JSON (unbalanced brace: missing closing brace).
    The parser tries to read the first key as a string, so the
    actual rejection is `.expectedChar '"'` on the literal 'm'. -/
example : parseBoundedInputCertificateWire "{malformed}" = .error (.expectedChar '"' "'m'") := by
  native_decide

/-- R2 — leading zero in number (N=01). Per strict JSON, integers
    cannot have leading zeros (only "0" itself is allowed). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":01," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error .leadingZeroNumber := by
  native_decide

/-- R3 — duplicate top-level key (`schemaVersion` appears twice). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.duplicateKey "schemaVersion" "$") := by
  native_decide

/-! ## P1 #1 — Schema constraints (rejections) -/

/-- R4 — wrong schema version (`"2.0"` instead of `"1.0"`). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"2.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.unsupportedSchemaVersion "2.0") := by
  native_decide

/-- R5 — missing required field `claim`. -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.missingField "claim") := by
  native_decide

/-- R6 — wrong type for `schemaVersion` (int instead of string). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":42," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.missingField "schemaVersion") := by
  native_decide

/-- R7 — unknown nested field inside `claim` (`extra` not in schema). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1,\"extra\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.unknownField "extra" "claim") := by
  native_decide

/-- R7b — unknown nested field inside witness `l` (`bogus` not in schema). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\",\"bogus\":1}," ++
    "\"trajectory\":[1]}]}" = .error (.unknownField "bogus" "rawWitnesses[0].l") := by
  native_decide

/-- R8 — numeric lower bound violated: `N = 0` (must be ≥ 1). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":0," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error .nMustBePositive := by
  native_decide

/-- R8b — numeric lower bound violated: singleton `n = 0`. -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":0}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error .singletonNMustBePositive := by
  native_decide

/-- R8c — numeric lower bound violated: bounded `K = 0`. -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"bounded\",\"K\":0}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error .boundedKMustBePositive := by
  native_decide

/-- R9 — empty `leafId` (must be non-empty string). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error .emptyLeafId := by
  native_decide

/-- R10 — empty `trajectory` array (must have ≥ 1 entry). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[]}]}" = .error .emptyTrajectory := by
  native_decide

/-- R11 — zero trajectory entry (must be ≥ 1). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[0]}]}" = .error (.trajectoryEntryMustBePositive 0) := by
  native_decide

/-- R12 — unsupported claim tag (`{"type":"interval"}` is not a
    FiniteOrbitClaim constructor). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"interval\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}" = .error (.unknownClaimTag "interval") := by
  native_decide

/-- R13 — top-level is not a JSON object (it's an array). -/
example : parseBoundedInputCertificateWire "[]" = .error (.notAnObject "$") := by
  native_decide

/-- R14 — unknown top-level field (`debug` not in schema v1.0). -/
example : parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]," ++
    "\"debug\":1}" = .error (.unknownField "debug" "$") := by
  native_decide

/-! ## P1 (v3) — ASCII-only contract on `leafId` / `leafProperty`

Per Codex review `PRR_kwDOTuMD788AAAABLG_dzA` P1: parser must reject
non-ASCII chars in identifier fields (mirroring schema `pattern` +
producer `_validate_ascii_identifier`). The parser enforces this via
`checkAscii` at the schema layer in `parseCertWitnessWire`. -/

/-- R15 — non-ASCII char in `leafId` (U+00E9 LATIN SMALL LETTER E
    WITH ACUTE = 0xE9). Mirrors the v2 surrogate-pair bug: a UTF-8
    byte sequence the parser used to accept silently. -/
example : parseBoundedInputCertificateWire
    ("{\"schemaVersion\":\"1.0\"," ++
     "\"claim\":{\"type\":\"empty\"}," ++
     "\"N\":1," ++
     "\"rawWitnesses\":[" ++
     "{\"l\":{\"leafId\":\"" ++ s!"{Char.ofNat 0xE9}" ++
       "\",\"leafProperty\":\"p\"}," ++
     "\"trajectory\":[1]}]}") = .error (.nonAsciiChar "rawWitnesses[0].l.leafId" 0xE9) := by
  native_decide

/-- R16 — non-ASCII char in `leafProperty` (U+00E9 = 0xE9). -/
example : parseBoundedInputCertificateWire
    ("{\"schemaVersion\":\"1.0\"," ++
     "\"claim\":{\"type\":\"empty\"}," ++
     "\"N\":1," ++
     "\"rawWitnesses\":[" ++
     "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"" ++ s!"{Char.ofNat 0xE9}" ++
       "\"}," ++
     "\"trajectory\":[1]}]}") = .error (.nonAsciiChar "rawWitnesses[0].l.leafProperty" 0xE9) := by
  native_decide

/-- R17 — surrogate half in `\uXXXX` escape (U+D83D = 0xD83D, the
    high half of an emoji surrogate pair). The v2 parser rejected
    this correctly but the producer (`ensure_ascii=True`) emitted
    these pairs from non-BMP input. v3's ASCII-only contract makes
    the producer reject such input upstream; the parser still rejects
    it defensively. -/
example : parseBoundedInputCertificateWire
    (String.mk
      "{\"schemaVersion\":\"1.0\",\"claim\":{\"type\":\"empty\"},\"N\":1,\"rawWitnesses\":[{\"l\":{\"leafId\":\"\\uD83D\",\"leafProperty\":\"p\"},\"trajectory\":[1]}]}".data) =
    .error .surrogateInUnicodeEscape := by
  native_decide

end CollatzResearch
