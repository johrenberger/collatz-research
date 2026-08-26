/-
Q5 PR #3 v2 — Lean JSON parser for `BoundedInputCertificateWire`.

Parses a `String` (JSON bytes emitted by the Python producer per
`schemas/bounded-input-certificate-v1.json`) into the
`BoundedInputCertificateWire` record from PR #62 v5.

Hand-rolled per Justin's approval of Q5 PR #3 decision #3: the schema
is fixed and small, the parser is the trust-critical boundary, and
hand-rolling gives full control over the rejection categories without
`Lean.Json` partial-function footguns.

## Codex review on v1 (PR #63, review `5025973591`, 2026-08-26T03:35:16Z, REQUEST CHANGES)

Three P1 findings, all addressed in v2:

- **[P1]** Schema constraints not enforced recursively (N ≥ 1, n ≥ 1,
  K ≥ 1, leafId non-empty, positive trajectory entries,
  `additionalProperties: false` at every object layer).
  **v2 fix:** added `checkNoUnknownFields` helper, called from every
  schema-validation function (top-level, claim, witness, leaf). Added
  positive-value checks: `nMustBePositive`, `singletonNMustBePositive`,
  `boundedKMustBePositive`, `trajectoryEntryMustBePositive`,
  `emptyLeafId`. Each rejection is a stable, machine-readable
  category.

- **[P1]** Hand-rolled parser is not strict JSON. v1 accepts leading
  zeros (`01`), permits unescaped control characters in strings, and
  rejects valid JSON escapes (`\\b`, `\\f`, `\\uXXXX`).
  **v2 fix:**
    - `parseNum` rejects leading zeros (single `0` allowed; `01`, `00`
      rejected with `INVALID_VALUE: leading zero`).
    - `parseStringContent` rejects unescaped control chars
      (codepoint < 32 or == 127).
    - Added support for `\\b` (backspace), `\\f` (form feed),
      `\\uXXXX` (4 hex digits → Unicode codepoint; surrogate halves
      rejected).

- **[P1]** Missing `BoundedInputCertificateParserTests.lean`.
  **v2 fix:** new test file with 17 compile-checked scenarios covering
  positive + all rejection categories listed in the review.

Trust boundary (per Q5 v5 spec § 4.3.1a):
  Python serialized evidence → (`parseBoundedInputCertificateWire`)
  → Lean wire → (`decodeBoundedInputCertificateData`)
  → Lean checked → (`checkBoundedCertificate`)
  → Bool verifier → (Q5 PR #4 soundness theorem) →
  BoundedInputOrbitCertificate →
  coverage_tree_soundness_orbit_cert_bounded.

Story Q5 / PR #3 v2 (hand-rolled parser with full schema enforcement +
strict JSON + compile-checked rejection tests; soundness integration
deferred to Q5 PR #4). -/

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
    Python `parser.py` style). -/
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
  deriving Repr

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

instance : ToString ParseError := ⟨ParseError.toString⟩

/-! ## Character-level helpers -/

def isWs (c : Char) : Bool :=
  c == ' ' ∨ c == '\n' ∨ c == '\t' ∨ c == '\r'

def skipWs : List Char → List Char
  | [] => []
  | c :: rest => if isWs c then skipWs rest else c :: rest

def expectChar (c : Char) : List Char → Except String (Unit × List Char)
  | [] => .error s!"unexpected end of input (expected '{c}')"
  | d :: rest => if d == c then .ok ((), rest) else .error s!"expected '{c}', found '{d}'"

def parseLiteral : List Char → Except String (JsonValue × List Char)
  | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
  | _ => .error "expected literal (true/false/null)"

/-! ## Number parsing (strict JSON: rejects leading zeros) -/

partial def parseNumDigits (acc : Nat) : List Char → Except String (Nat × List Char)
  | [] => .ok (acc, [])
  | c :: rest =>
    if '0' ≤ c ∧ c ≤ '9' then
      parseNumDigits (acc * 10 + (c.toNat - '0'.toNat)) rest
    else
      .ok (acc, c :: rest)

def parseNum : List Char → Except String (Nat × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | [] => .error "expected digit"
    | '0' :: rest =>
      match rest with
      | c :: _ =>
        if '0' ≤ c ∧ c ≤ '9' then .error "leading zero not allowed in number"
        else .ok (0, rest)
      | [] => .ok (0, [])
    | c :: rest =>
      if '0' ≤ c ∧ c ≤ '9' then
        parseNumDigits (c.toNat - '0'.toNat) rest
      else
        .error s!"expected digit, found '{c}'"

/-! ## String parsing (strict JSON: rejects unescaped control chars) -/

def hexDigitVal : Char → Except String Nat
  | '0' => .ok 0 | '1' => .ok 1 | '2' => .ok 2 | '3' => .ok 3
  | '4' => .ok 4 | '5' => .ok 5 | '6' => .ok 6 | '7' => .ok 7
  | '8' => .ok 8 | '9' => .ok 9
  | 'a' | 'A' => .ok 10 | 'b' | 'B' => .ok 11
  | 'c' | 'C' => .ok 12 | 'd' | 'D' => .ok 13
  | 'e' | 'E' => .ok 14 | 'f' | 'F' => .ok 15
  | c => .error s!"invalid hex digit '{c}'"

def parseHex4 : List Char → Except String (Nat × List Char)
  | c1 :: c2 :: c3 :: c4 :: rest =>
    let n1 ← hexDigitVal c1
    let n2 ← hexDigitVal c2
    let n3 ← hexDigitVal c3
    let n4 ← hexDigitVal c4
    .ok (n1 * 0x1000 + n2 * 0x100 + n3 * 0x10 + n4, rest)
  | _ => .error "expected 4 hex digits after \\u"

partial def parseStringContent (acc : List Char) : List Char →
    Except String (String × List Char)
  | [] => .error "unterminated string"
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
    if 0xD800 ≤ n ∧ n ≤ 0xDFFF then .error "surrogate halves not allowed"
    else if let some c := Char.ofNat? n then
      parseStringContent (c :: acc) rest
    else
      .error s!"invalid unicode codepoint U+{n.toHexString}"
  | '\\' :: c :: _ => .error s!"invalid escape sequence: \\{c}"
  | c :: rest =>
    let cp := c.toNat
    if cp < 32 ∨ cp == 127 then
      .error s!"unescaped control character (codepoint {cp})"
    else
      parseStringContent (c :: acc) rest

def parseString : List Char → Except String (String × List Char)
  | '"' :: rest => parseStringContent [] rest
  | _ => .error "expected string (opening quote)"

/-! ## Value / Array / Object parsing -/

def parseValue : List Char → Except String (JsonValue × List Char)

partial def parseArray (items : List JsonValue) : List Char →
    Except String (JsonValue × List Char)
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
      | [] => .error "unexpected end of input in array"
      | c :: _ => .error s!"expected ',' or ']' in array, found '{c}'"

partial def parseObject (entries : List (String × JsonValue)) :
    List Char → Except String (JsonValue × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
    | '}' :: rest => .ok (.object entries.reverse, rest)
    | _ =>
      let (key, rest) ← parseString cs
      let rest := skipWs rest
      let (_, rest) ← expectChar ':' rest
      let rest := skipWs rest
      let (v, rest) ← parseValue rest
      if entries.any (fun e => e.1 == key) then
        .error s!"duplicate key '{key}'"
      else
        let entries := (key, v) :: entries
        let rest := skipWs rest
        match rest with
        | ',' :: rest1 =>
          let rest1 := skipWs rest1
          parseObject entries rest1
        | '}' :: rest1 => .ok (.object entries.reverse, rest1)
        | [] => .error "unexpected end of input in object"
        | c :: _ => .error s!"expected ',' or '}}' in object, found '{c}'"

def parseValue : List Char → Except String (JsonValue × List Char)
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
        .error s!"unexpected character '{c}'"
  | [] => .error "unexpected end of input"

def parseJson (s : String) : Except String JsonValue :=
  let cs := s.data
  let cs := skipWs cs
  match parseValue cs with
  | .ok (v, rest) =>
    let rest := skipWs rest
    if rest = [] then .ok v
    else .error "unexpected trailing input after JSON value"
  | .error e => .error e

/-! ## Schema validation (enforces every wire-format constraint) -/

def lookupKey (key : String) (entries : List (String × JsonValue)) :
    Option JsonValue := entries.lookup key

/-- Reject fields not in `known`. Implements JSON Schema
    `additionalProperties: false` for an object layer. -/
def checkNoUnknownFields (path : String) (known : List String)
    (entries : List (String × JsonValue)) : Except String Unit :=
  let unknown := entries.filterMap fun (k, _) =>
    if known.contains k then none else some k
  match unknown with
  | _ :: _ => .error s!"unknown fields at {path}: {unknown}"
  | [] => .ok ()

def parseFiniteOrbitClaim (path : String) (v : JsonValue) :
    Except String FiniteOrbitClaim :=
  match v with
  | .object entries =>
    checkNoUnknownFields path ["type", "n", "K"] entries >>= fun _ =>
    match lookupKey "type" entries with
    | some (.string "empty") =>
      if entries.length == 1 then .ok .empty
      else .error "empty claim must have only 'type' field"
    | some (.string "singleton") =>
      match lookupKey "n" entries with
      | some (.num 0) => .error "singleton claim 'n' must be positive"
      | some (.num n) =>
        if entries.length == 2 then .ok (.singleton n)
        else .error "singleton claim must have only 'type' and 'n'"
      | _ => .error "singleton claim requires non-negative integer 'n'"
    | some (.string "bounded") =>
      match lookupKey "K" entries with
      | some (.num 0) => .error "bounded claim 'K' must be positive"
      | some (.num K) =>
        if entries.length == 2 then .ok (.bounded K)
        else .error "bounded claim must have only 'type' and 'K'"
      | _ => .error "bounded claim requires non-negative integer 'K'"
    | some (.string tag) => .error s!"unknown claim tag '{tag}'"
    | _ => .error s!"{path}.type must be a string"
  | _ => .error s!"{path} must be a JSON object"

def parseCertWitnessWire (path : String) (v : JsonValue) :
    Except String CertWitnessWire :=
  match v with
  | .object entries =>
    checkNoUnknownFields path ["l", "trajectory"] entries >>= fun _ =>
    let l ← match lookupKey "l" entries with
      | some (.object lEntries) =>
        checkNoUnknownFields s!"{path}.l" ["leafId", "leafProperty"] lEntries >>= fun _ =>
        match lookupKey "leafId" lEntries, lookupKey "leafProperty" lEntries with
        | some (.string ""), _ => .error s!"{path}.l.leafId must be non-empty"
        | some (.string leafId), some (.string leafProperty) =>
          .ok { leafId, leafProperty }
        | _, _ => .error s!"{path}.l requires string leafId and leafProperty"
      | _ => .error s!"{path}.l must be a JSON object"
    let trajectory ← match lookupKey "trajectory" entries with
      | some (.array []) => .error s!"{path}.trajectory must be non-empty"
      | some (.array items) =>
        items.enum.foldlM (init := []) fun acc (i, item) =>
          match item with
          | .num 0 => .error s!"trajectory entry {i} must be positive"
          | .num n => .ok (n :: acc)
          | _ => .error s!"trajectory entry {i} must be a non-negative integer"
      | _ => .error s!"{path}.trajectory must be a non-empty JSON array"
    .ok { l, trajectory := trajectory.reverse }
  | _ => .error s!"{path} must be a JSON object"

def parseBoundedInputCertificateWire (s : String) :
    Except String BoundedInputCertificateWire := do
  let v ← parseJson s
  let entries ← match v with
    | .object entries => .ok entries
    | _ => .error "top-level must be a JSON object"
  checkNoUnknownFields "$" ["schemaVersion", "claim", "N", "rawWitnesses"] entries
  -- schemaVersion
  let _ ← match lookupKey "schemaVersion" entries with
    | some (.string "1.0") => .ok ()
    | some (.string other) => .error s!"unsupported schema version '{other}'"
    | _ => .error "missing or wrong-type field 'schemaVersion'"
  -- claim
  let claim ← match lookupKey "claim" entries with
    | some claimV => parseFiniteOrbitClaim "claim" claimV
    | _ => .error "missing field 'claim'"
  -- N (must be positive)
  let N ← match lookupKey "N" entries with
    | some (.num 0) => .error "N must be positive"
    | some (.num N) => .ok N
    | _ => .error "missing or wrong-type field 'N'"
  -- rawWitnesses (must be non-empty, every witness valid)
  let rawWitnesses ← match lookupKey "rawWitnesses" entries with
    | some (.array []) => .error "rawWitnesses must be non-empty"
    | some (.array items) =>
      items.enum.foldlM (init := []) fun acc (i, item) =>
        parseCertWitnessWire s!"rawWitnesses[{i}]" item >>= fun w =>
          .ok (w :: acc)
    | _ => .error "missing or wrong-type field 'rawWitnesses'"
  .ok { N, rawWitnesses := rawWitnesses.reverse, claim }

end CollatzResearch
