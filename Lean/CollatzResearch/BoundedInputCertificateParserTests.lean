/-
Q5 PR #3 v2 — parser rejection tests (per Codex review on PR #63 v1).

The Codex review identified missing test coverage as a P1 finding:
the PR body explicitly deferred the test suite, but parser behavior
IS the deliverable + trust boundary of this PR. v2 adds 17
compile-checked scenarios covering positive + every rejection
category listed in the review.

All tests use `native_decide` for kernel-checked reduction. Per the
Q5 v4 spec, parser correctness is established by these scenarios
executing to the expected Bool value.

Story Q5 / PR #3 v2 (parser + rejection tests). -/

import CollatzResearch.BoundedInputCertificateParser
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## Test helpers -/

def Except.isOk : Except ε α → Bool
  | .ok _ => true
  | _ => false

def Except.isError : Except ε α → Bool
  | .error _ => true
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

/-- R1 — malformed JSON (unbalanced brace: missing closing brace). -/
example : (parseBoundedInputCertificateWire "{malformed}").isError = true := by
  native_decide

/-- R2 — leading zero in number (N=01). Per strict JSON, integers
    cannot have leading zeros (only "0" itself is allowed). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":01," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R3 — duplicate top-level key (`schemaVersion` appears twice). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-! ## P1 #1 — Schema constraints (rejections) -/

/-- R4 — wrong schema version (`"2.0"` instead of `"1.0"`). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"2.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R5 — missing required field `claim`. -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R6 — wrong type for `schemaVersion` (int instead of string). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":42," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R7 — unknown nested field inside `claim` (`extra` not in schema). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1,\"extra\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R7b — unknown nested field inside witness `l` (`bogus` not in schema). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":1}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\",\"bogus\":1}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R8 — numeric lower bound violated: `N = 0` (must be ≥ 1). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":0," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R8b — numeric lower bound violated: singleton `n = 0`. -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"singleton\",\"n\":0}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R8c — numeric lower bound violated: bounded `K = 0`. -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"bounded\",\"K\":0}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R9 — empty `leafId` (must be non-empty string). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R10 — empty `trajectory` array (must have ≥ 1 entry). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[]}]}").isError = true := by
  native_decide

/-- R11 — zero trajectory entry (must be ≥ 1). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[0]}]}").isError = true := by
  native_decide

/-- R12 — unsupported claim tag (`{"type":"interval"}` is not a
    FiniteOrbitClaim constructor). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"interval\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]}").isError = true := by
  native_decide

/-- R13 — top-level is not a JSON object (it's an array). -/
example : (parseBoundedInputCertificateWire "[]").isError = true := by
  native_decide

/-- R14 — unknown top-level field (`debug` not in schema v1.0). -/
example : (parseBoundedInputCertificateWire
    "{\"schemaVersion\":\"1.0\"," ++
    "\"claim\":{\"type\":\"empty\"}," ++
    "\"N\":1," ++
    "\"rawWitnesses\":[" ++
    "{\"l\":{\"leafId\":\"L\",\"leafProperty\":\"p\"}," ++
    "\"trajectory\":[1]}]," ++
    "\"debug\":1}").isError = true := by
  native_decide

end CollatzResearch
