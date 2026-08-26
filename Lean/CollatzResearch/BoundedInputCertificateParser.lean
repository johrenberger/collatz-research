/-
Q5 PR #3 — Lean JSON parser for `BoundedInputCertificateWire`.

Parses a `String` (JSON bytes emitted by the Python producer per
`schemas/bounded-input-certificate-v1.json`) into the
`BoundedInputCertificateWire` record from PR #62 v5.

Hand-rolled per Justin's approval of Q5 PR #3 decision #3: the schema
is fixed and small, the parser is the trust-critical boundary, and
hand-rolling gives full control over the rejection categories without
`Lean.Json` partial-function footguns.

Trust boundary (per Q5 v5 spec § 4.3.1a):
  Python serialized evidence → (`parseBoundedInputCertificateWire`)
  → Lean wire → (`decodeBoundedInputCertificateData`)
  → Lean checked → (`checkBoundedCertificate`)
  → Bool verifier → (Q5 PR #4 soundness theorem) →
  BoundedInputOrbitCertificate →
  coverage_tree_soundness_orbit_cert_bounded.

Companion file: `Q5VerifierTests.lean` (compile-checked positive
scenarios for the verifier). This file's tests live in
`BoundedInputCertificateParserTests.lean`.

Open gates addressed:
- v1 implements the parser + rejection categories per PR #62 v5 § 4.3.1a
  deferral: malformed JSON, wrong schemaVersion, missing fields,
  wrong field types, malformed witness entries, unsupported claim tags.
- Lean admission budget: no new `sorry`/`admit`/`axiom`.

Story Q5 / PR #3 (producer + JSON parser + rejection tests; soundness
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
    enumerated in PR #62 v5 § 4.3.1a deferral + the wire-format spec. -/
inductive ParseError where
  | unexpectedEof
  | expectedChar (expected : Char) (found : String)
  | invalidNumber (msg : String)
  | invalidEscape (msg : String)
  | missingField (field : String)
  | wrongTypeAt (expected : String) (path : String)
  | unknownField (field : String)
  | unknownClaimTag (tag : String)
  | unsupportedSchemaVersion (v : String)
  | duplicateKey (key : String)
  | emptyTrajectory
  | notAnObject (path : String)
  deriving Repr

def ParseError.toString : ParseError → String
  | .unexpectedEof => "MALFORMED_JSON: unexpected end of input"
  | .expectedChar e f => s!"MALFORMED_JSON: expected character '{e}', found {f}"
  | .invalidNumber m => s!"INVALID_VALUE: invalid number: {m}"
  | .invalidEscape m => s!"MALFORMED_JSON: invalid string escape: {m}"
  | .missingField k => s!"MISSING_FIELD: required field '{k}' missing"
  | .wrongType t p => s!"WRONG_TYPE: expected {t} at {p}"
  | .unknownField f => s!"UNKNOWN_FIELD: '{f}' (not in schema v1.0)"
  | .unknownClaimTag t => s!"UNSUPPORTED_CLAIM_TAG: '{t}' is not a FiniteOrbitClaim"
  | .unsupportedSchemaVersion v =>
    s!"UNSUPPORTED_SCHEMA_VERSION: '{v}' is not '1.0'"
  | .duplicateKey k => s!"MALFORMED_JSON: duplicate key '{k}'"
  | .emptyTrajectory => "INVALID_VALUE: trajectory must have at least 1 entry"
  | .notAnObject p => s!"WRONG_TYPE: expected JSON object at {p}"

instance : ToString ParseError := ⟨ParseError.toString⟩

/-! ## Character-level parser helpers -/

def isWs (c : Char) : Bool :=
  c == ' ' ∨ c == '\n' ∨ c == '\t' ∨ c == '\r'

def skipWs : List Char → List Char
  | [] => []
  | c :: rest => if isWs c then skipWs rest else c :: rest

def peekChar : List Char → Except String Char
  | [] => .error "unexpected end of input"
  | c :: _ => .ok c

def expectChar (c : Char) : List Char → Except String (Unit × List Char)
  | [] => .error s!"unexpected end of input (expected '{c}')"
  | d :: rest =>
    if d == c then .ok ((), rest)
    else .error s!"expected '{c}', found '{d}'"

def parseLiteral : List Char → Except String (JsonValue × List Char)
  | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
  | _ => .error "expected literal (true/false/null)"

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
    | c :: _ =>
      if '0' ≤ c ∧ c ≤ '9' then parseNumDigits 0 cs
      else .error s!"expected digit, found '{c}'"

/-- Parse a JSON string with full escape sequence support.
    Returns the unescaped string + the remaining input. -/
partial def parseStringContent (acc : List Char) : List Char →
    Except String (String × List Char)
  | [] => .error "unterminated string"
  | '"' :: rest => .ok (String.ofList acc.reverse, rest)
  | '\\' :: c :: rest =>
    let escaped := match c with
      | '"' => "\""
      | '\\' => "\\"
      | '/' => "/"
      | 'n' => "\n"
      | 't' => "\t"
      | 'r' => "\r"
      | _ => s!"\\{c}"
    if escaped.startsWith "\\" ∧ escaped.length > 1 ∧
       (escaped.get! 1 != '"' ∧ escaped.get! 1 != '\\' ∧
        escaped.get! 1 != '/' ∧ escaped.get! 1 != 'n' ∧
        escaped.get! 1 != 't' ∧ escaped.get! 1 != 'r') then
      .error s!"invalid escape sequence: \\{c}"
    else
      parseStringContent (escaped.data.reverse ++ acc) rest
  | c :: rest => parseStringContent (c :: acc) rest

def parseString : List Char → Except String (String × List Char)
  | '"' :: rest => parseStringContent [] rest
  | _ => .error "expected string (opening quote)"

/-- Forward decl: parseValue (mutual recursion). -/
def parseValue : List Char → Except String (JsonValue × List Char)

/-- Parse `[item, item, ...]` or `[]`. -/
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

/-- Parse `{"key": value, "key": value, ...}` or `{}`. -/
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
        let rest := skipWs rest
        match rest with
        | ',' :: rest1 =>
          let rest1 := skipWs rest1
          parseObject ((key, v) :: entries) rest1
        | '}' :: rest1 => .ok (.object ((key, v) :: entries).reverse, rest1)
        | [] => .error "unexpected end of input in object"
        | c :: _ => .error s!"expected ',' or '}}' in object, found '{c}'"

def parseValue : List Char → Except String (JsonValue × List Char)
  | cs =>
    let cs := skipWs cs
    match cs with
  | 't' :: _ | 'f' :: _ | 'n' :: _ => parseLiteral cs
  | '"' :: _ => parseString cs
  | '[' :: rest =>
      let rest := skipWs rest
      parseArray [] rest
  | '{' :: rest =>
      let rest := skipWs rest
      parseObject [] rest
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
    else .error s!"unexpected trailing input after JSON value"
  | .error e => .error e

/-! ## Schema validation -/

/-- Look up a key in a JSON object. -/
def lookupKey (key : String) (entries : List (String × JsonValue)) :
    Option JsonValue :=
  entries.lookup key

/-- Parse a `FiniteOrbitClaim` from a JSON value. -/
def parseFiniteOrbitClaim (path : String) (v : JsonValue) :
    Except String FiniteOrbitClaim :=
  match v with
  | .object entries =>
    match lookupKey "type" entries with
    | some (.string "empty") => .ok .empty
    | some (.string "singleton") =>
      match lookupKey "n" entries with
      | some (.num n) => .ok (.singleton n)
      | _ => .error s!"{path}.n must be a non-negative integer"
    | some (.string "bounded") =>
      match lookupKey "K" entries with
      | some (.num K) => .ok (.bounded K)
      | _ => .error s!"{path}.K must be a non-negative integer"
    | some (.string tag) => .error s!"unknown claim tag '{tag}' at {path}"
    | _ => .error s!"{path}.type must be a string"
  | _ => .error s!"{path} must be a JSON object"

/-- Parse a `CertWitnessWire` from a JSON value. -/
def parseCertWitnessWire (path : String) (v : JsonValue) :
    Except String CertWitnessWire :=
  match v with
  | .object entries =>
    let l ← match lookupKey "l" entries with
      | some (.object lEntries) =>
        match lookupKey "leafId" lEntries, lookupKey "leafProperty" lEntries with
        | some (.string leafId), some (.string leafProperty) =>
          .ok { leafId, leafProperty }
        | _ => .error s!"{path}.l requires string leafId and leafProperty"
      | _ => .error s!"{path}.l must be a JSON object with leafId/leafProperty"
    let trajectory ← match lookupKey "trajectory" entries with
      | some (.array []) => .error "trajectory must be non-empty"
      | some (.array items) =>
        items.foldlM (init := []) fun acc item =>
          match item with
          | .num n => .ok (n :: acc)
          | _ => .error s!"trajectory entries must be non-negative integers"
      | _ => .error s!"{path}.trajectory must be a non-empty JSON array"
    .ok { l, trajectory := trajectory.reverse }
  | _ => .error s!"{path} must be a JSON object"

/-- Top-level: parse a `BoundedInputCertificateWire` from a JSON string.

    Rejection categories (stable, machine-readable, uppercase):
    - MALFORMED_JSON — syntactic JSON error
    - UNSUPPORTED_SCHEMA_VERSION — schemaVersion not "1.0"
    - MISSING_FIELD — required field absent
    - UNKNOWN_FIELD — extra field not in schema v1.0
    - WRONG_TYPE — field has wrong JSON type
    - UNSUPPORTED_CLAIM_TAG — claim.type not in {empty, singleton, bounded}
    - INVALID_VALUE — semantic value constraint violated
      (e.g., empty trajectory, negative trajectory entry)
    - MALFORMED_JSON (duplicateKey) — duplicate key in object -/
def parseBoundedInputCertificateWire (s : String) :
    Except String BoundedInputCertificateWire := do
  let v ← parseJson s
  let entries ← match v with
    | .object entries => .ok entries
    | _ => .error "top-level must be a JSON object"
  -- schemaVersion (required, must be "1.0")
  let _ ← match lookupKey "schemaVersion" entries with
    | some (.string "1.0") => .ok ()
    | some (.string other) => .error s!"unsupported schema version '{other}'"
    | _ => .error "missing or wrong-type field 'schemaVersion'"
  -- claim (required, must be a FiniteOrbitClaim)
  let claim ← match lookupKey "claim" entries with
    | some claimV => parseFiniteOrbitClaim "claim" claimV
    | _ => .error "missing field 'claim'"
  -- N (required, must be a Nat)
  let N ← match lookupKey "N" entries with
    | some (.num N) => .ok N
    | _ => .error "missing or wrong-type field 'N'"
  -- rawWitnesses (required, must be non-empty array of witnesses)
  let rawWitnesses ← match lookupKey "rawWitnesses" entries with
    | some (.array []) => .error "rawWitnesses must be non-empty"
    | some (.array items) =>
      items.enum.foldlM (init := []) fun acc (i, item) =>
        parseCertWitnessWire s!"rawWitnesses[{i}]" item >>= fun w =>
          .ok (w :: acc)
    | _ => .error "missing or wrong-type field 'rawWitnesses'"
  -- Unknown fields check (schema v1.0 has exactly 4 fields)
  let knownFields : List String := ["schemaVersion", "claim", "N", "rawWitnesses"]
  let unknownFields := entries.filterMap (fun (k, _) =>
    if knownFields.contains k then none else some k)
  match unknownFields with
  | _ :: _ => .error s!"unknown fields: {unknownFields}"
  | [] => .ok { N, rawWitnesses := rawWitnesses.reverse, claim }

end CollatzResearch
