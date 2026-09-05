# Lessons Learned — Story Q5 External-Certificates + Routing-Partition (PRs #61 → #62 → #63 → #64 → #66 → #67 → #68 → #69)

**Status:** Arc partial (PRs MERGED 2026-08-28 through 2026-09-04). Soundness theorem (`checkBoundedCertificate_sound`, Lemma 5) and constructive per-leaf availability theorem (`per_leaf_available_bounded_of_check`, Lemma 6) **WITHDRAWN** per Codex P0 review on 2026-09-02. Routing-partition acceptance sub-arc complete.

**Scope:** 8 PRs, ~7 calendar days (2026-08-28 to 2026-09-04). Two sub-arcs:
- **External-certificates / bounded-input integration** (PRs #61, #62, #63, #64, #66): spec → verifier → producer+parser → bounded-input integration → hotfix.
- **Routing-partition acceptance** (PRs #67, #68, #69): certificate design → acceptance facts → RP-5 reachability.

**Outcome:**
- ✅ External-certificate inhabitation: bounded-input side formally established (`BoundedInputOrbitCertificate` structure, `coverage_tree_soundness_orbit_cert_bounded` companion theorem, `per_leaf_available_bounded_of_hCert` hypothesis-eliminator, depthTwoTree conditional type-check example). Soundness theorem + constructive availability withdrawn.
- ✅ Routing-partition acceptance facts: complete (PRs #67, #68, #69).
- ✅ No `sorry`/`admit`/`axiom` in final state (`docs/lean-sorry-budget.json` Q5Integration.lean entry reverted to pre-v2b baseline by `760329a`).
- ❌ End-to-end Q5 closure: NOT achieved (soundness theorem absent). Re-attempt gates documented in §4.

This document captures the Q5 arc structure, the wire/checked split, the list-position identity, the Codex P0 rejection pattern, and the actor pattern (autonomous multi-commit bot work with independent review).

---

## 1. Arc overview

### PR #61 — Q5 spec (squash-merged at `1fa90bd`, 2026-08-28)

Docs-only PR. Establishes the Q5 v5 spec: external-certificate inhabitation via Python search + Lean verifier. Defines the trust boundary (Python UNTRUSTED, Lean TCB), the 4-PR split (extended to 5-PR with hotfix), the bounded-input vs unbounded-input scope distinction. ~574 lines.

### PR #62 — Lean-only verifier (squash-merged at `5215fd1`, 2026-09-04)

Implements the verifier: `BoundedInputCertificateWire` (in-memory representation), `BoundedInputCertificateData` (checked bundle with `length_ok` proof), `decodeBoundedInputCertificateData` (decoder rejecting length mismatch), `checkBoundedCertificate` (Bool verifier), `checkCertWitness` (single-witness checker with 5 conjuncts: anchor match + leaf match + routing + terminal claim + transition validity).

5 versions before final merge (v1 through v5). Codex reviews on the version chain:
- v4 (`b8b3687`) review: **P1** in-memory-model wording fix (records should not be called "directly serializable from Python"); **P2** PR body updated to match v4 API.
- v5 review: **P1** wire/checked split preserved as-is; **P2** PR body wording fix.

**Key architectural moves:**
- **Wire/checked split (v4):** `BoundedInputCertificateWire` is the wire payload; `BoundedInputCertificateData` is the checked bundle (wire + `length_ok` proof). Inhabitation follows from `decodeBoundedInputCertificateData` (returns `none` on length mismatch), so a malformed wire cannot inhabit the checked type via the public surface.
- **List-position identity (v3):** witness at index `i` carries canonical input `i + 1`. The type-level identity `Fin N → CertWitness (i.val + 1)` is reconstructed via `List.get` with the `length_ok` proof transporting `i.val < wire.N` to `i.val < wire.rawWitnesses.length`.
- **JSON parsing deferred to PR #63:** per Codex v4 review, the v4 file incorrectly called records "directly serializable from Python"; v5 explicitly defers JSON parsing.
- **No proof fields on wire:** Python cannot emit Lean proofs (they're kernel artifacts); `BoundedInputCertificateWire` has no proof fields.

### PR #63 — producer + parser (squash-merged at `18a948e`, 2026-09-04)

Python external generator + hand-rolled Lean JSON parser + parser-rejection tests. Closes the producer side of the trust boundary. The parser is the boundary between Python-emitted JSON text and the Lean wire representation; parser-rejection tests verify malformed JSON is rejected.

### PR #64 — bounded-input integration (squash-merged at `009efbe2`, 2026-09-04)

16 commits in one PR:
1. v1 (`1f342f5`) — initial `BoundedInputOrbitCertificate` + companion theorem
2. v2a (`dd2eae5`) — Q1 P1 fix: `0 < x` premise on `orbit_hits_claim`
3. v2b.0 (`b8f2efc`) — proof decomposition plan (docs)
4. v2b.1 (`2560731`) — Lemmas 1 + 2 (fold extraction, witness decomposition) + 5 helper predicates
5. v2b.2 (`53e8b97`) — Lemma 3 (trajectory indexing) + 2 bridging lemmas
6. v2b.3 (`bd72a3b`) — Lemma 4 (terminal-claim transport)
7. v2b.4 (`a319b79`) — Lemma 5 (soundness assembly) — **REMOVED per Codex P0**
8. v2b.5 (`a5196fc`) — Lemma 6 (per-leaf constructive availability) — **REMOVED per Codex P0**
9. v2b.6 (`5d66460`) — soundness chain tests — trimmed when Lemmas 5–6 removed
10. `8323aa9` — track v2b sorry placeholders in Lean admission budget — **REVERTED** by `760329a`
11. `760329a` — **Codex P0 + P1(1) fixes**: removed Lemmas 5–6 + restructured Lemmas 3–4 + added Q5 targets to `lean-ci.yml`
12. `bceb828` — repair v2a API and Boolean helper compatibility
13. `64417ae` — WP-2 generalized Boolean fold extraction
14. `8e1844f` — WP-3 repair trajectory index induction
15. `1fb8421` — WP-4 transport terminal claim
16. `a37cef6` — repair integration test API checks

**Codex P0 review (`PRR_kwDOTuMD788AAAABL71GQA`, 2026-09-02T22:39:09Z):**
> [P0] `docs/lean-sorry-budget.json` and `Lean/CollatzResearch/Q5Integration.lean:529,532,743,755,758,768` — this PR raises the admission budget to permit six new `sorry`s, including four in `checkBoundedCertificate_sound`. That turns the checker-to-certificate bridge into an untrusted axiom while making CI appear green. **Do not extend the budget for this path. Remove the admitted theorem/proof skeleton from the Lean module (retain the decomposition in the planning document if useful) and land only fully checked helper lemmas. The soundness theorem and constructive availability theorem must remain absent until proved.**

The Codex P0 review is **independent, not continuation bias** — it caught the budget violation that would have turned the checker-to-certificate bridge into an untrusted axiom while making CI appear green. The bot's structural pivot (remove Lemmas 5–6 + restructure Lemmas 3–4 to drop `transitionOk_implies_step` bridging lemma) was the correct response.

### PR #66 — hotfix (squash-merged, 2026-09-04)

Hotfix Q5: restore concrete `CertWitness` representation. Necessary because a prior commit had abstracted away the witness structure, breaking the integration tests' ability to exercise concrete witness scenarios. The hotfix reinstates the concrete representation without changing the verifier interface.

### PR #67 — routing-partition certificate design (squash-merged, 2026-09-04)

Designs the routing-partition certificate — a separate sub-arc that emerged from Q5's open questions about per-leaf vs single-leaf quantification. The routing-partition sub-arc was necessary because the v2b.4 soundness theorem's `dataPerLeaf` family did not match the existing `checkBoundedCertificate t l d` (which validates all inputs against ONE FIXED leaf `l`). The routing-partition sub-arc established a parallel architecture.

### PR #68 — routing-partition acceptance facts (squash-merged, 2026-09-04)

Establishes the acceptance facts for routing-partition certificates: the predicates and lemmas that characterize when a routing partition is valid, when a leaf's certificate is accepted, and how the partition relates to the per-leaf verifier check.

### PR #69 — RP-5 conditional routing-partition reachability (squash-merged, 2026-09-04)

Conditional reachability theorem for routing partitions: under explicit per-leaf hypotheses, every routed input reaches 1. Companion theorem for the routing-partition sub-arc, parallel in shape to PR #64's `coverage_tree_soundness_orbit_cert_bounded`.

---

## 2. Architectural decisions

### 2.1 The wire/checked split (PR #62 v4 → v5)

The verifier infrastructure separates the wire payload (`BoundedInputCertificateWire`) from the checked bundle (`BoundedInputCertificateData`). The wire is an in-memory record; the checked bundle adds a `length_ok : wire.rawWitnesses.length = wire.N` proof. Inhabitation of the checked bundle follows from `decodeBoundedInputCertificateData` (returns `none` on length mismatch), so a malformed wire cannot inhabit the checked type via the public surface.

```lean
structure BoundedInputCertificateWire where
  N : Nat
  rawWitnesses : List CertWitnessWire
  claim : FiniteOrbitClaim

structure BoundedInputCertificateData where
  wire : BoundedInputCertificateWire
  length_ok : wire.rawWitnesses.length = wire.N

def decodeBoundedInputCertificateData (raw : BoundedInputCertificateWire) :
    Option BoundedInputCertificateData :=
  if h : raw.rawWitnesses.length = raw.N then
    some ⟨raw, h⟩
  else none
```

The decoder is the **trust boundary** between Python-emitted wire data and Lean-verified certificates. JSON parsing (consuming `String`/`ByteArray`) is the outer layer; `decodeBoundedInputCertificateData` is the inner layer.

### 2.2 List-position identity (PR #62 v3)

The canonical input `x` is **not stored** in the wire witness. It is encoded by the witness's **position** in the list: witness at index `i` carries canonical input `i + 1`. The type-level identity is reconstructed via `List.get` with the `length_ok` proof transporting `i.val < wire.N` to `i.val < wire.rawWitnesses.length`.

```lean
def BoundedInputCertificateData.certWitness (d : BoundedInputCertificateData) :
    (i : Fin d.wire.N) → CertWitness (i.val + 1) := fun i =>
  have h_pos : i.val < d.wire.rawWitnesses.length := by
    rw [d.length_ok]
    exact i.isLt
  (d.wire.rawWitnesses.get ⟨i.val, h_pos⟩).toCertWitness (i.val + 1)
```

This pattern avoids storing the canonical input as a Lean function field (which would require a proof obligation to be reattached when lifting wire witness to typed witness). The position encoding is the canonical input identity.

### 2.3 NO `wellFormed` field (mirroring Q4 v3)

Per Q4 v3 lesson: the `BoundedInputOrbitCertificate` does NOT have a `wellFormed` field. The wire/checked split is the analogous discipline at the verifier boundary: malformed data is rejected at decode time, not carried as a field for later checking.

### 2.4 External-certificate trust boundary (Q5 v5 spec § 3)

```
Python serialized evidence → (PR #63 parser)
                            → BoundedInputCertificateWire
                            → decodeBoundedInputCertificateData (PR #62)
                            → BoundedInputCertificateData
                            → checkBoundedCertificate (PR #62)
                            → [SUSPENDED — soundness theorem withdrawn per Codex P0]
                            → BoundedInputOrbitCertificate (PR #64)
                            → coverage_tree_soundness_orbit_cert_bounded (PR #64)
                            → ∀ x, 0 < x ≤ N → ReachesOne x
```

Producer (Python) + parser (Lean) are UNTRUSTED. Only the Lean verifier + companion theorem enter the TCB. With the soundness theorem withdrawn, the TCB does NOT include a verified bridge from `checkBoundedCertificate = true` to `BoundedInputOrbitCertificate`. Re-attempt requires closing the 4 sorries in Lemma 5 without budget increase.

### 2.5 The 4-PR split extended to 5-PR (with hotfix)

Q4 v3 established the 4-PR split (spec → foundation → data → theorem → lessons). Q5 extended it with a **hotfix PR** (#66) because the integration tests needed a concrete `CertWitness` representation that an earlier commit had abstracted away. The hotfix was a 1-PR scope, additive, no scope expansion. Future arcs should anticipate this pattern: a hotfix PR is sometimes needed between the data and integration PRs if the data layer gets refactored in a way that breaks integration tests.

### 2.6 Routing-partition sub-arc (PRs #67–#69)

The routing-partition sub-arc was a parallel architecture established to address the per-leaf vs single-leaf quantification mismatch that was identified as a blocker for Lemma 5 re-attempt. The sub-arc:
- PR #67 designs the routing-partition certificate (separate from the bounded-input certificate).
- PR #68 establishes the acceptance facts (predicates + lemmas characterizing validity).
- PR #69 establishes the conditional reachability theorem (companion theorem for routing partitions).

The sub-arc does NOT depend on Lemma 5. It establishes a parallel certificate architecture that can serve as the foundation for any future Lemma 5 re-attempt that addresses the per-leaf quantification.

---

## 3. The actor pattern (NEW for Q5)

The `app-dev-discovery-bot` shipped the v2b arc (Lemmas 1–6 + Codex P0/P1 fixes + WP-2/3/4 + repair integration tests) autonomously between 2026-09-02 and 2026-09-04 — **12 commits in 48 hours**, with one independent rejection (Codex P0 on v2b.4). This is a reusable pattern.

**What worked:**
- Sub-commit sequencing matched the v2b plan exactly (v2b.1 → v2b.2 → v2b.3 → v2b.4 → v2b.5 → v2b.6 → Codex P0/P1 → WP-2/3/4 → repair).
- WP-2 generalized `foldl_and_extract` to take any `acc : Bool` — improvement over the original `acc := true`-only form, more reusable for downstream lemmas.
- WP-3 rewrote Lemma 3 induction step using `calc` blocks — more readable than nested `rw`.
- WP-4 cleaned Lemma 4 indexing (`[...]!` instead of `[...]'`, `omega` for bounds).
- Repair integration tests simplified API-shape regression (takes `cert` arg + projects fields) — removes dependence on def-equality.
- Per-PR squash-merge with descriptive commit messages — clean history even when 16 commits ship in one PR.

**What didn't work (Codex P0 caught it):**
- Lemma 5 (`checkBoundedCertificate_sound`) was attempted with 4 `sorry` placeholders for Mathlib-heavy lemmas (nested `Bool.and_eq_true` destructuring + `ix ∈ List.finRange` + `claim.Holds trajectory[length-1]!` extraction).
- Lemma 6 (`per_leaf_available_bounded_of_check`) inherited the sorry-laden status.
- The `transitionOk_implies_step` bridging lemma in v2b.2 had 2 sorries for `List.length_zip`/`List.get_zip`.
- Codex P0 directive: *"do not extend the budget for this path. Remove the admitted theorem/proof skeleton from the Lean module"*.

**The pattern is:** autonomous multi-commit work on a bounded sub-arc, with independent review (Codex) catching structural issues that the agent would not have caught via continuation. The agent's WP-* commits were polish; the Codex P0 review was the structural pivot.

This pattern is **reusable for future sub-arcs** but requires:
1. A clear sub-arc decomposition in a planning doc (the v2b plan doc).
2. A separate reviewer (Codex, or human) at the sub-arc boundary.
3. Willingness to restructure rather than extend the budget.

The bot's response to Codex P0 — removing Lemmas 5–6 + restructuring Lemmas 3–4 to drop the bridging lemma — is the canonical example of "reviewer-pivot, not reviewer-launder." The Codex review is **independent, not continuation bias**.

---

## 4. Re-attempt gates for Lemma 5 (from PR #64 body)

Per the Codex P0 review and PR #64's "Re-attempt gates" section, any future PR to re-introduce Lemma 5 must satisfy:

1. **All 4 sorries closed without budget increase** (Codex P0 directive).
2. **Architectural decision made**: per-leaf vs single-leaf quantification mismatch (Codex P1(2), unresolved). The `dataPerLeaf` family does not match `checkBoundedCertificate t l d` (which validates all inputs against ONE FIXED leaf `l`). Future re-attempt must either:
   - (a) scope the verifier/integration to single-leaf trees, OR
   - (b) redesign the wire/checker/certificate interface around an input-to-leaf routing partition (the routing-partition sub-arc PRs #67–#69 establishes infrastructure for option (b)).
3. **Codex review re-opened** on the new proofs.

The decomposition plan is retained in `docs/story-q5-pr4-v2b-proof-decomposition.md` for any future re-attempt to reference.

---

## 5. Trust boundary

- **Producer + parser (PR #63):** UNTRUSTED RUNTIME EVIDENCE.
- **Verifier (PR #62):** TCB.
- **Companion theorem (PR #64):** TCB.
- **Soundness theorem (PR #64 v2b.4):** WITHDRAWN — not in TCB.
- **Routing-partition sub-arc (PRs #67–#69):** TCB (parallel architecture; does not require the withdrawn soundness theorem).

The Lean admission budget (`docs/lean-sorry-budget.json`) does not include any Q5 module. The Q5Integration.lean entry was added in commit `8323aa9` (sorry-budget tracker) and reverted in `760329a` (Codex P0/P1 fixes). Net effect: zero `sorry`/`admit`/`axiom` budget increase from Q5.

---

## 6. Self-audit

- **No new `sorry`/`admit`/`axiom`** in final state. The 4 v2b.4 sorries + 2 v2b.2 sorries were removed by Codex P0/P1 fixes, not by closing the proofs.
- **CI now actually builds Q5 files** (Codex P1(1) fix in `760329a`): `lean-ci.yml` has explicit `lake build CollatzResearch.Q5Integration` and `lake build CollatzResearch.Q5IntegrationTests` steps.
- **No changes to `BoundedInputCertificateData.lean` or `BoundedInputCertificateParser.lean`** (PR #62 + PR #63 files were not modified in v2b).
- **Trust boundary unchanged** (`pure_lean: true`).
- **Routing-partition sub-arc is a NEW parallel architecture**, not a refinement of the bounded-input integration. The two sub-arcs address different problems and can coexist.

---

## 7. Dependency

Depends on PR #55–#60 (Q4 META + bounded-orbit infrastructure; all merged), PR #49–#51 (07c-2 conditional companion theorem; all merged), PR #30–#48 (02c/03c dynamics/equivalence; all merged).

Story Q5 closes the Q5 4-PR split (extended to 5-PR with hotfix #66) for the bounded-input integration side. The end-to-end Q5 closure claim is NOT made — the soundness theorem is absent. Re-attempt gates documented in §4.

The routing-partition sub-arc (PRs #67–#69) is complete and provides a parallel architecture for any future Lemma 5 re-attempt that chooses option (b) in §4.2.
