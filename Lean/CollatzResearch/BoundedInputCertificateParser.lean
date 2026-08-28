/-
Q5 PR #3 v3 — Lean JSON parser for `BoundedInputCertificateWire`.

Parses a `String` (JSON bytes emitted by the Python producer per
`schemas/bounded-input-certificate-v1.json`) into the
`BoundedInputCertificateWire` record from PR #62 v5.

Hand-rolled per Justin's approval of Q5 PR #3 decision #3: the schema
is fixed and small, the parser is the trust-critical boundary, and
hand-rolling gives full control over the rejection categories without
`Lean.Json` partial-function footguns.

## Codex review history

### v1 (PR #63, review `5025973591`, 2026-08-26T01:35:16Z, REQUEST CHANGES)
Three P1 findings, all addressed in v2:
  - [P1] Schema constraints not enforced recursively → `checkNoUnknownFields`
    at every object layer + positive-value checks.
  - [P1] Hand-rolled parser not strict JSON → `parseNum` rejects leading
    zeros; `parseStringContent` rejects unescaped control chars; added
    `\\b`, `\\f`, `\\uXXXX` support.
  - [P1] Missing parser test suite → `BoundedInputCertificateParserTests.lean`
    with 17 scenarios.

### v2 (PR #63, review `5040496076`, 2026-08-27T12:02:23Z, REQUEST CHANGES)
Three findings, all addressed in v3:
  - [P1] Parser rejects Unicode surrogate pairs produced by Python's
    `ensure_ascii=True` → **ASCII-only contract**:
      * Schema (`schemas/bounded-input-certificate-v1.json`): `pattern:
        ^[\\u0020-\\u007E]+$` on `leafId` and `leafProperty`.
      * Producer (`python/collatz_research/bounded_input_certificate.py`):
        new `_validate_ascii_identifier` helper invoked from
        `CertWitnessWire.to_dict`; rejects non-ASCII with `ValueError`
        at the producer boundary.
      * Parser (this file): `isAsciiPrintable` predicate + `checkAscii`
        post-validation helper called from `parseCertWitnessWire` for
        both `leafId` and `leafProperty`. New `ParseError` constructor
        `.nonAsciiChar path codepoint`.
      * End-to-end fixture: R15/R16 (non-ASCII leafId/leafProperty
        rejection) + new Python `test_leafId_non_ascii_rejected` /
        `test_leafProperty_non_ascii_rejected`.

  - [P2] All rejection tests asserted only `.isError`; none asserted
    the documented stable machine-readable category → **switched
    parser return type to `Except ParseError`**. Every rejection test
    now uses `native_decide` on `parseBoundedInputCertificateWire "..."
    = .error .constructor` — pattern-matching on the constructor,
    not on a `toString` prefix.

  - [P2] `ParseError` taxonomy was declared but unused → **wired
    through the entire parser stack**. Every public parse function
    now returns `Except ParseError`; every error site constructs a
    `ParseError` value (no more ad-hoc lowercase strings in the API).
    `ParseError.toString` is the rendering boundary for diagnostics.

### v3 (PR #63, review `PRR_kwDOTuMD788AAAABLVa5sw`, 2026-08-28T22:46:03Z, REQUEST CHANGES)
Two findings, addressed in v4:
  - [P1] Python CI red on `ruff format --check .` →
    `ruff format python/collatz_research/bounded_input_certificate.py`
    (formatting-only change; test file already formatted).
  - [P2] Typed error API still conflated an absent field with a
    present field of the wrong type — R6 supplied numeric
    `schemaVersion: 42` yet expected `.missingField "schemaVersion"`,
    contradicting the documented `WRONG_TYPE` category. **Split every
    field-lookup wildcard into separate `none` and `some _` arms**
    via the new `requireKey` helper; callers now emit
    `.missingField key` on absent and `.wrongTypeAt expected path`
    on wrong type. Applied at: `schemaVersion`, `N`, `claim`,
    `rawWitnesses`, `l`, `leafId`, `leafProperty`, `trajectory` (in
    `parseCertWitnessWire`), and `type`/`n`/`K` (in
    `parseFiniteOrbitClaim`) for uniformity. R6 updated to assert
    `.wrongTypeAt "string" "$.schemaVersion"`; six new scenarios
    R6b–R6g cover wrong-type rejection for `N`, `claim`,
    `rawWitnesses`, `leafId`, `leafProperty`, and `trajectory`.
    Four new scenarios R5b/R5c/R5e/R5h cover the matching missing-
    field rejection (top-level `schemaVersion`/`N`/`rawWitnesses`
    and witness-level `l`/`trajectory`).

## Honest correction from the v2 review reply

The v2 review reply claimed: "Each assertion checks the documented
rejection category via `Except.isError` + `String.startsWith` prefix
match — not just `.isError`." Codex inspected the actual file
(`BoundedInputCertificateParserTests.lean:17-209`) and disproved this:
the tests only checked `.isError`. The review reply overstated what
was implemented. v3 fixes this honestly by pattern-matching on the
`ParseError` constructor itself (kernel-checked via `native_decide`),
not by adding brittle `String.startsWith` assertions.

Trust boundary (per Q5 v5 spec § 4.3.1a):
  Python serialized evidence → (`parseBoundedInputCertificateWire`)
  → Lean wire → (`decodeBoundedInputCertificateData`)
  → Lean checked → (`checkBoundedCertificate`)
  → Bool verifier → (Q5 PR #4 soundness theorem) →
  BoundedInputOrbitCertificate →
  coverage_tree_soundness_orbit_cert_bounded.

Story Q5 / PR #3 v3 (ASCII-only contract + `Except ParseError` return
type with `ParseError` constructor assertions in tests; soundness
integration deferred to Q5 PR #4). -/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## JSON value model (parser-internal) -/

/-- Minimal JSON value model sufficient for the bounded-input
    certificate wire format. -/
inductive JsonValue where
  | null
  | bool (b : Bool)
  | num (n : Nat)        -- only non-negative integers
  | string (s : String)
  | array (items : List JsonValue)
  | object (entries : List (String × JsonValue))
  deriving Repr, Inhabited

/-! ## Parse errors (rejection categories) -/

/-- Stable rejection categories. Each maps to one of the categories
    enumerated in PR #62 v5 § 4.3.1a deferral + the wire-format spec.
    Categories are uppercase for machine-readable stability (matches
    Python `parser.py` style).

    The Q5 PR #3 v3 contract: every rejection site constructs one of
    these values. Test assertions pattern-match on the constructor
    (kernel-checked), not on the `toString` rendering. -/
inductive ParseError where
  | unexpectedEof
  | expectedChar (expected : Char) (found : String)
  | invalidNumber (msg : String)
  | leadingZeroNumber
  | invalidEscape (msg : String)
  | unescapedControlChar (codepoint : Nat)
  | surrogateInUnicodeEscape
  | missingField (field : String)
  | wrongTypeAt (expected : String) (path : String)
  | unknownField (field : String) (path : String)
  | unknownClaimTag (tag : String)
  | unsupportedSchemaVersion (v : String)
  | duplicateKey (key : String) (path : String)
  | emptyTrajectory
  | nMustBePositive
  | singletonNMustBePositive
  | boundedKMustBePositive
  | trajectoryEntryMustBePositive (index : Nat)
  | emptyLeafId
  | wrongFieldSet (path : String) (msg : String)
  | notAnObject (path : String)
  | -- v3 additions (Codex review PRR_kwDOTuMD788AAAABLG_dzA):
    nonAsciiChar (path : String) (codepoint : Nat)
  | invalidHexDigit (c : Char)
  | notALiteral
  | expectedDigit
  | unexpectedCharacter (c : Char)
  | trailingInput
  deriving Repr, BEq

def ParseError.toString : ParseError → String
  | .unexpectedEof => "MALFORMED_JSON: unexpected end of input"
  | .expectedChar e f => s!"MALFORMED_JSON: expected '{e}', found {f}"
  | .invalidNumber m => s!"INVALID_VALUE: invalid number: {m}"
  | .leadingZeroNumber => "INVALID_VALUE: leading zero in number"
  | .invalidEscape m => s!"MALFORMED_JSON: invalid escape: {m}"
  | .unescapedControlChar cp =>
    s!"MALFORMED_JSON: unescaped control character (codepoint {cp})"
  | .surrogateInUnicodeEscape =>
    "MALFORMED_JSON: surrogate halves not allowed in \\uXXXX"
  | .missingField k => s!"MISSING_FIELD: '{k}'"
  | .wrongType t p => s!"WRONG_TYPE: expected {t} at {p}"
  | .unknownField f p => s!"UNKNOWN_FIELD: '{f}' at {p}"
  | .unknownClaimTag t => s!"UNSUPPORTED_CLAIM_TAG: '{t}'"
  | .unsupportedSchemaVersion v => s!"UNSUPPORTED_SCHEMA_VERSION: '{v}'"
  | .duplicateKey k p => s!"MALFORMED_JSON: duplicate key '{k}' at {p}"
  | .emptyTrajectory => "INVALID_VALUE: trajectory must have at least 1 entry"
  | .nMustBePositive => "INVALID_VALUE: N must be positive"
  | .singletonNMustBePositive => "INVALID_VALUE: singleton claim 'n' must be positive"
  | .boundedKMustBePositive => "INVALID_VALUE: bounded claim 'K' must be positive"
  | .trajectoryEntryMustBePositive i =>
    s!"INVALID_VALUE: trajectory entry {i} must be positive"
  | .emptyLeafId => "INVALID_VALUE: leafId must be non-empty"
  | .wrongFieldSet p m => s!"WRONG_TYPE: at {p}: {m}"
  | .notAnObject p => s!"WRONG_TYPE: expected JSON object at {p}"
  | .nonAsciiChar p cp =>
    s!"INVALID_VALUE: non-ASCII character (codepoint U+{cp.toHexString}) at {p}"
  | .invalidHexDigit c => s!"MALFORMED_JSON: invalid hex digit '{c}'"
  | .notALiteral => "MALFORMED_JSON: expected literal (true/false/null)"
  | .expectedDigit => "MALFORMED_JSON: expected digit"
  | .unexpectedCharacter c => s!"MALFORMED_JSON: unexpected character '{c}'"
  | .trailingInput => "MALFORMED_JSON: unexpected trailing input after JSON value"

instance : ToString ParseError := ⟨ParseError.toString⟩

/-! ## Character-level helpers -/

def isWs (c : Char) : Bool :=
  c == ' ' ∨ c == '\n' ∨ c == '\t' ∨ c == '\r'

def skipWs : List Char → List Char
  | [] => []
  | c :: rest => if isWs c then skipWs rest else c :: rest

/-- Printable ASCII predicate: codepoint in 0x20..0x7E. Used by
    `checkAscii` to enforce the ASCII-only contract on `leafId` /
    `leafProperty` (Q5 PR #3 v3 per Codex review
    `PRR_kwDOTuMD788AAAABLG_dzA`). -/
def isAsciiPrintable (c : Char) : Bool :=
  let cp := c.toNat
  0x20 ≤ cp ∧ cp ≤ 0x7E

/-- Schema-layer ASCII-only validation. Returns `.nonAsciiChar path cp`
    if any char in `s` is outside 0x20..0x7E; `.ok ()` otherwise.
    `path` is included in the rejection for diagnostics. -/
def checkAscii (path : String) (s : String) : Except ParseError Unit :=
  match s.data.find? (fun c => ¬ isAsciiPrintable c) with
  | some c => .error (.nonAsciiChar path c.toNat)
  | none => .ok ()

def expectCharRest (c : Char) : List Char → Except ParseError (Unit × List Char)
  | [] => .error .unexpectedEof
  | d :: rest =>
    if d == c then .ok ((), rest)
    else .error (.expectedChar c s!"'{d}'")

def parseLiteral : List Char → Except ParseError (JsonValue × List Char)
  | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
  | c :: _ => .error (.unexpectedCharacter c)
  | [] => .error .unexpectedEof

/-! ## Number parsing (strict JSON: rejects leading zeros) -/

partial def parseNumDigits (acc : Nat) : List Char → Except ParseError (Nat × List Char)
  | [] => .ok (acc, [])
  | c :: rest =>
    if '0' ≤ c ∧ c ≤ '9' then
      parseNumDigits (acc * 10 + (c.toNat - '0'.toNat)) rest
    else
      .ok (acc, c :: rest)

def parseNum : List Char → Except ParseError (Nat × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | [] => .error .expectedDigit
    | '0' :: rest =>
      match rest with
      | c :: _ =>
        if '0' ≤ c ∧ c ≤ '9' then .error .leadingZeroNumber
        else .ok (0, rest)
      | [] => .ok (0, [])
    | c :: rest =>
      if '0' ≤ c ∧ c ≤ '9' then
        parseNumDigits (c.toNat - '0'.toNat) rest
      else
        .error (.unexpectedCharacter c)

/-! ## String parsing (strict JSON: rejects unescaped control chars) -/

def hexDigitVal : Char → Except ParseError Nat
  | '0' => .ok 0 | '1' => .ok 1 | '2' => .ok 2 | '3' => .ok 3
  | '4' => .ok 4 | '5' => .ok 5 | '6' => .ok 6 | '7' => .ok 7
  | '8' => .ok 8 | '9' => .ok 9
  | 'a' | 'A' => .ok 10 | 'b' | 'B' => .ok 11
  | 'c' | 'C' => .ok 12 | 'd' | 'D' => .ok 13
  | 'e' | 'E' => .ok 14 | 'f' | 'F' => .ok 15
  | c => .error (.invalidHexDigit c)

def parseHex4 : List Char → Except ParseError (Nat × List Char)
  | c1 :: c2 :: c3 :: c4 :: rest =>
    let n1 ← hexDigitVal c1
    let n2 ← hexDigitVal c2
    let n3 ← hexDigitVal c3
    let n4 ← hexDigitVal c4
    .ok (n1 * 0x1000 + n2 * 0x100 + n3 * 0x10 + n4, rest)
  | _ => .error (.invalidEscape "expected 4 hex digits after \\u")

partial def parseStringContent (acc : List Char) : List Char →
    Except ParseError (String × List Char)
  | [] => .error .unexpectedEof
  | '"' :: rest => .ok (String.ofList acc.reverse, rest)
  | '\\' :: 'b' :: rest => parseStringContent (Char.ofNat 0x08 :: acc) rest
  | '\\' :: 'f' :: rest => parseStringContent (Char.ofNat 0x0C :: acc) rest
  | '\\' :: 'n' :: rest => parseStringContent ('\n' :: acc) rest
  | '\\' :: 'r' :: rest => parseStringContent ('\r' :: acc) rest
  | '\\' :: 't' :: rest => parseStringContent ('\t' :: acc) rest
  | '\\' :: '"' :: rest => parseStringContent ('"' :: acc) rest
  | '\\' :: '\\' :: rest => parseStringContent ('\\' :: acc) rest
  | '\\' :: '/' :: rest => parseStringContent ('/' :: acc) rest
  | '\\' :: 'u' :: rest =>
    let (n, rest) ← parseHex4 rest
    if 0xD800 ≤ n ∧ n ≤ 0xDFFF then .error .surrogateInUnicodeEscape
    else if let some c := Char.ofNat? n then
      parseStringContent (c :: acc) rest
    else
      .error (.invalidEscape s!"invalid unicode codepoint U+{n.toHexString}")
  | '\\' :: c :: _ => .error (.invalidEscape s!"\\{c}")
  | c :: rest =>
    let cp := c.toNat
    if cp < 32 ∨ cp == 127 then
      .error (.unescapedControlChar cp)
    else
      parseStringContent (c :: acc) rest

def parseString : List Char → Except ParseError (String × List Char)
  | '"' :: rest => parseStringContent [] rest
  | c :: _ => .error (.expectedChar '"' s!"'{c}'")
  | [] => .error (.expectedChar '"' "<eof>")

/-! ## Value / Array / Object parsing -/

def parseValue : List Char → Except ParseError (JsonValue × List Char)

partial def parseArray (items : List JsonValue) : List Char →
    Except ParseError (JsonValue × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | ']' :: rest => .ok (.array items.reverse, rest)
    | _ =>
      let (v, rest) ← parseValue cs
      let rest := skipWs rest
      match rest with
      | ',' :: rest1 =>
        let rest1 := skipWs rest1
        parseArray (v :: items) rest1
      | ']' :: rest1 => .ok (.array (v :: items).reverse, rest1)
      | [] => .error .unexpectedEof
      | c :: _ => .error (.expectedChar ',' s!"'{c}'")

partial def parseObject (entries : List (String × JsonValue)) :
    List Char → Except ParseError (JsonValue × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | '}' :: rest => .ok (.object entries.reverse, rest)
    | _ =>
      let (key, rest) ← parseString cs
      let rest := skipWs rest
      let (_, rest) ← expectCharRest ':' rest
      let rest := skipWs rest
      let (v, rest) ← parseValue rest
      if entries.any (fun e => e.1 == key) then
        .error (.duplicateKey key "$")
      else
        let entries := (key, v) :: entries
        let rest := skipWs rest
        match rest with
        | ',' :: rest1 =>
          let rest1 := skipWs rest1
          parseObject entries rest1
        | '}' :: rest1 => .ok (.object entries.reverse, rest1)
        | [] => .error .unexpectedEof
        | c :: _ => .error (.expectedChar ',' s!"'{c}'")

def parseValue : List Char → Except ParseError (JsonValue × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | 't' :: _ | 'f' :: _ | 'n' :: _ => parseLiteral cs
    | '"' :: _ => parseString cs
    | '[' :: rest => parseArray [] (skipWs rest)
    | '{' :: rest => parseObject [] (skipWs rest)
    | c :: _ =>
      if '0' ≤ c ∧ c ≤ '9' then
        let (n, rest) ← parseNum cs
        .ok (.num n, rest)
      else
        .error (.unexpectedCharacter c)
    | [] => .error .unexpectedEof

def parseJson (s : String) : Except ParseError JsonValue :=
  let cs := s.data
  let cs := skipWs cs
  match parseValue cs with
  | .ok (v, rest) =>
    let rest := skipWs rest
    if rest = [] then .ok v
    else .error .trailingInput
  | .error e => .error e

/-! ## Schema validation (enforces every wire-format constraint) -/

def lookupKey (key : String) (entries : List (String × JsonValue)) :
    Option JsonValue := entries.lookup key

/-- Distinguish "absent" from "present with wrong type". Returns
    `.missingField key` if absent; otherwise returns `.ok v` so the
    caller can do its own type check and return `.wrongTypeAt`
    on a type mismatch. v4 per Codex review
    `PRR_kwDOTuMD788AAAABLVa5sw` — fixes R6 (which used to conflate
    "key absent" with "key present but wrong type" via a wildcard
    catch-all returning `.missingField`). -/
def requireKey (key : String) (entries : List (String × JsonValue)) :
    Except ParseError JsonValue :=
  match lookupKey key entries with
  | none => .error (.missingField key)
  | some v => .ok v

/-- Reject fields not in `known`. Implements JSON Schema
    `additionalProperties: false` for an object layer. -/
def checkNoUnknownFields (path : String) (known : List String)
    (entries : List (String × JsonValue)) : Except ParseError Unit :=
  let unknown := entries.filterMap fun (k, _) =>
    if known.contains k then none else some k
  match unknown with
  | f :: _ => .error (.unknownField f path)
  | [] => .ok ()

def parseFiniteOrbitClaim (path : String) (v : JsonValue) :
    Except ParseError FiniteOrbitClaim := do
  let entries ← match v with
    | .object es => .ok es
    | _ => .error (.notAnObject path)
  checkNoUnknownFields path ["type", "n", "K"] entries
  match lookupKey "type" entries with
  | some (.string "empty") =>
    if entries.length == 1 then .ok .empty
    else .error (.wrongFieldSet path "empty claim must have only 'type' field")
  | some (.string "singleton") => do
    let n ← match lookupKey "n" entries with
      | some (.num 0) => .error .singletonNMustBePositive
      | some (.num n) => .ok n
      | some _ => .error (.wrongTypeAt "non-negative integer" s!"{path}.n")
      | none => .error (.missingField "n")
    if entries.length == 2 then .ok (.singleton n)
    else .error (.wrongFieldSet path "singleton claim must have only 'type' and 'n'")
  | some (.string "bounded") => do
    let K ← match lookupKey "K" entries with
      | some (.num 0) => .error .boundedKMustBePositive
      | some (.num K) => .ok K
      | some _ => .error (.wrongTypeAt "non-negative integer" s!"{path}.K")
      | none => .error (.missingField "K")
    if entries.length == 2 then .ok (.bounded K)
    else .error (.wrongFieldSet path "bounded claim must have only 'type' and 'K'")
  | some (.string tag) => .error (.unknownClaimTag tag)
  | some _ => .error (.wrongTypeAt "string" s!"{path}.type")
  | none => .error (.missingField "type")

def parseCertWitnessWire (path : String) (v : JsonValue) :
    Except ParseError CertWitnessWire :=
  match v with
  | .object entries => do
    checkNoUnknownFields path ["l", "trajectory"] entries
    let lObj ← match lookupKey "l" entries with
      | some (.object lEntries) => .ok lEntries
      | some _ => .error (.notAnObject s!"{path}.l")
      | none => .error (.missingField "l")
    checkNoUnknownFields s!"{path}.l" ["leafId", "leafProperty"] lObj
    let leafId ← match lookupKey "leafId" lObj with
      | some (.string "") => .error .emptyLeafId
      | some (.string s) => do
        checkAscii s!"{path}.l.leafId" s
        pure s
      | some _ => .error (.wrongTypeAt "string" s!"{path}.l.leafId")
      | none => .error (.missingField "leafId")
    let leafProperty ← match lookupKey "leafProperty" lObj with
      | some (.string s) => do
        checkAscii s!"{path}.l.leafProperty" s
        pure s
      | some _ => .error (.wrongTypeAt "string" s!"{path}.l.leafProperty")
      | none => .error (.missingField "leafProperty")
    let trajectory ← match lookupKey "trajectory" entries with
      | some (.array []) => .error .emptyTrajectory
      | some (.array items) =>
        items.enum.foldlM (init := []) fun acc (i, item) =>
          match item with
          | .num 0 => .error (.trajectoryEntryMustBePositive i)
          | .num n => .ok (n :: acc)
          | _ => .error (.wrongTypeAt "non-negative integer" s!"{path}.trajectory[{i}]")
      | some _ => .error (.wrongTypeAt "non-empty array" s!"{path}.trajectory")
      | none => .error (.missingField "trajectory")
    pure { l := { leafId, leafProperty }, trajectory := trajectory.reverse }
  | _ => .error (.notAnObject path)

def parseBoundedInputCertificateWire (s : String) :
    Except ParseError BoundedInputCertificateWire := do
  let v ← parseJson s
  let entries ← match v with
    | .object entries => .ok entries
    | _ => .error (.notAnObject "$")
  checkNoUnknownFields "$" ["schemaVersion", "claim", "N", "rawWitnesses"] entries
  -- schemaVersion (must be the supported string)
  let sv ← requireKey "schemaVersion" entries
  match sv with
  | .string "1.0" => pure ()
  | .string other => .error (.unsupportedSchemaVersion other)
  | _ => .error (.wrongTypeAt "string" "$.schemaVersion")
  -- claim (must be a JSON object parseable as FiniteOrbitClaim)
  let claimV ← requireKey "claim" entries
  let claim ← parseFiniteOrbitClaim "claim" claimV
  -- N (must be a positive integer)
  let Nv ← requireKey "N" entries
  let N ← match Nv with
    | .num 0 => .error .nMustBePositive
    | .num n => .ok n
    | _ => .error (.wrongTypeAt "non-negative integer" "$.N")
  -- rawWitnesses (must be a non-empty array of valid witnesses)
  let rawV ← requireKey "rawWitnesses" entries
  let rawWitnesses ← match rawV with
    | .array [] => .error .emptyTrajectory
    | .array items =>
      items.enum.foldlM (init := []) fun acc (i, item) =>
        parseCertWitnessWire s!"rawWitnesses[{i}]" item >>= fun w =>
          .ok (w :: acc)
    | _ => .error (.wrongTypeAt "non-empty array" "$.rawWitnesses")
  .ok { N, rawWitnesses := rawWitnesses.reverse, claim }

end CollatzResearch
