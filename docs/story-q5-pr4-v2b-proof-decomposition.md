# Story Q5 PR #4 — v2b Proof Decomposition Plan

Companion to `docs/story-q5-external-certificate-inhabitation.md` (Q5 spec, PR #61).
Companion to `docs/story-q4-bounded-orbit-certificates.md` (Q4 v3 proof arc).

## Goal

```
checkBoundedCertificate_sound :
    ∀ (c : BoundedInputCertificateData), c.check = true → BoundedInputOrbitCertificate t l N
```

Connects the Bool verifier (`checkBoundedCertificate = true`) to the bounded companion
theorem's certificate conclusion.

This is the missing v2a → v2b link. Without it, no externally accepted certificate yields
`ReachesOne x`. v2a establishes the bounded companion theorem + API surface + zero-boundary
regression; v2b closes the constructive bridge from wire data to certificates.

## Decomposition (per Codex Q5 verdict)

The ~200-line proof decomposes into 6 helper lemmas + final assembly. Each lemma lands as a
separate sub-commit on PR #64. v2b is its own bounded iteration cycle — **first task is
small helper lemmas, not the final theorem**.

### 1. fold/check extraction lemma

**Type:**

```lean
checkBoundedCertificate_sound_fold : ∀ (ts : List CertWitness),
    List.foldl (fun acc w => acc && checkCertWitness w) true ts = true →
    ∀ w ∈ ts, checkCertWitness w = true
```

**Strategy:** Standard `Bool.and` short-circuit extraction. Induction on `ts` (or
`List.foldl` induction lemma). The `true` seed + `&&` makes extraction clean.

**Dependencies:** None (pure `List`/`Bool` reasoning).

**Risk:** Low.

### 2. individual witness checker decomposition

**Type:**

```lean
checkCertWitness_decompose : ∀ (w : CertWitness), checkCertWitness w = true ↔
    (anchorOk w ∧ leafMatchOk w ∧ routingOk w ∧ terminalClaimOk w ∧ transitionOk w)
```

**Strategy:** Boolean decomposition of the `checkCertWitness` definition. Each conjunct
must hold; the conjunction is `true` iff all five hold. Mirrors the structure used in
`BoundedInputCertificateData.lean` (PR #62).

**Dependencies:** Lemma 1 (to lift the per-witness check from the fold result).

**Risk:** Low (mechanical).

### 3. trajectory-indexing lemma

**Type:**

```lean
trajectory_index : ∀ (x : Nat) (w : CertWitness) (k : Nat),
    k < (trajectory w).length →
    (trajectory w)[k]! = accelerated_orbit x k
```

**Strategy:** Induction on `k`.

- **Base** (`k = 0`): `accelerated_orbit_zero` (PR #56) gives `accelerated_orbit x 0 = x`;
  the witness anchor is `x`, and `trajectory w[0] = x` by construction.
- **Step** (`k + 1`): `accelerated_orbit_succ` (PR #56) gives
  `accelerated_orbit x (k + 1) = acceleratedStep (accelerated_orbit x k)`. The witness's
  `transitionOk` conjunct (Lemma 2) guarantees `(trajectory w)[k + 1]! = acceleratedStep
  (trajectory w)[k]!`. Apply induction hypothesis.

**Dependencies:** Lemma 2 (witness transition validity),
`accelerated_orbit_zero` + `accelerated_orbit_succ` (PR #56).

**Risk:** Medium — depends on `accelerated_orbit_succ` shape aligning with
`acceleratedStep` indexing. May need a bridging lemma if they diverge (Lean 4 indexing
notation vs `List.get`).

### 4. terminal-claim transport

**Type:**

```lean
terminal_claim_transport : ∀ (x : Nat) (w : CertWitness) (claim : FiniteOrbitClaim),
    claim.Holds (trajectory w).getLast (trajectory w).length - 1 →
    claim.Holds (accelerated_orbit x ((trajectory w).length - 1))
```

**Strategy:** Apply Lemma 3 with `k = (trajectory w).length - 1` to get
`(trajectory w)[(trajectory w).length - 1]! = accelerated_orbit x ((trajectory w).length
- 1)`. Substitute into the hypothesis.

**Dependencies:** Lemma 3.

**Risk:** Low.

### 5. soundness assembly

**Type:**

```lean
checkBoundedCertificate_sound : ∀ (c : BoundedInputCertificateData)
    (t : CoverageTree) (l : CoverageLeaf) (N : Nat)
    (hv : ValidTree t) (hc : IsComplete t)
    (hver : verified t l) (hcr : ∀ y, c.claim.Holds y → ReachesOne y),
    c.check = true → BoundedInputOrbitCertificate t l N
```

**Strategy:** Compose Lemma 1 → Lemma 2 → Lemma 3 → Lemma 4:

1. `c.check = true` unfolds to `foldl (&&) true c.witnesses = true` (by `checkBoundedCertificate` definition).
2. Lemma 1 lifts to `∀ w ∈ c.witnesses, checkCertWitness w = true`.
3. Lemma 2 decomposes each `checkCertWitness` into the 5 conjuncts.
4. Lemma 3 + Lemma 4 give `claim.Holds (accelerated_orbit (anchorOf w) ((trajectory w).length - 1))` for each witness.
5. `hcr` closes `ReachesOne (accelerated_orbit (anchorOf w) ((trajectory w).length - 1))` for each witness.
6. `descend_orbit_complete` (PR #29) + `orbit_predecessor_reaches_one` (PR #56) project each per-witness `ReachesOne` back to `ReachesOne x` for the input routed to leaf `l`.

Construct `BoundedInputOrbitCertificate t l N` with:

- `claim := c.claim`
- `orbit_hits_claim` from step 6
- `claim_reaches_one := hcr`

**Dependencies:** Lemmas 1–4, `hcr` external hypothesis, `descend_orbit_complete`
(PR #29), `orbit_predecessor_reaches_one` (PR #56).

**Risk:** Medium — composition is mechanical but `hcr` must be threaded through the
per-witness extraction. Same pattern as Q3 v4 + Q4 v3 + PR #58. The
`descend_orbit_complete` projection step (step 6) is where v2a's proof attempt hit a wall;
the issue is aligning witness anchors with `descendOrbit` routing.

### 6. constructive per-leaf availability theorem (OPTION C redesign — 2026-09-06)

**Architectural disposition (per Justin call message_id 23313):** **Option C** (hybrid:
per-tree verifier with per-leaf certificate projection). Supersedes the original v2b
per-leaf design (Option A) flagged as architecturally mismatched by GPT-5.6 Terra
reviewer round 2 (subagent `0ee9bf18-...`, Q9 P0 stop signal). Full disposition in
`.openclaw/followups/story-2-arch-disposition.md`; design details in
`.openclaw/followups/story-q5-option-c-spec.md`.

**Type:**

```lean
-- New per-tree wrapper (replaces the original per-leaf `dataPerLeaf` threading):
structure BoundedInputCertificateTree (t : CoverageTree) where
  perLeafData  : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData
  checkPerLeaf : ∀ l ∈ t.leaves, verified t l →
    checkBoundedCertificate t l (perLeafData l ‹_› ‹_›) = true

-- Per-tree verifier (no leaf parameter — analog of `checkRoutingPartitionCertificate`):
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool := …

-- Lemma 5 (per-tree reachability — analog of `RoutingPartitionCertificate_sound`):
theorem checkBoundedCertificateTree_sound
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l →
      ∀ y, (tree.perLeafData l …).wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true) :
    ∀ (x : Nat), 0 < x → x ≤ (tree.perLeafData l …).wire.N → ReachesOne x

-- Lemma 6 (per-leaf certificate projection — satisfies META § 3.2):
theorem per_leaf_available_bounded_of_tree
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : …)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l (tree.perLeafData l hl hver).wire.N
```

**Strategy:** Apply the per-leaf `checkBoundedCertificate_sound` (v2b kernel-clean
attempt) to `tree.perLeafData l hl hver` + `tree.checkPerLeaf l hl hver` + per-leaf
`hcr l hl hver` to construct the per-leaf certificate directly. Alternatively,
construct from the per-tree `checkBoundedCertificateTree_sound` reachability + per-
leaf routing evidence (cleaner but requires more lemmas).

Supersedes the v2a hypothesis-eliminator form `per_leaf_available_bounded_of_hCert`
and the v2b per-leaf `per_leaf_available_bounded_of_check` (Option A, architecturally
mismatched).

**Dependencies:** Lemma 5 (per-leaf, kernel-clean attempt) +
`checkBoundedCertificateTree_sound` (per-tree, NEW v2b.5) +
`descend_orbit_complete` (PR #29) + `orbit_predecessor_reaches_one` (PR #56) +
`RoutingPartitionCertificate_sound` (PR #74, kernel-clean analog).

**Risk:** Low (Option C is the kernel-clean synthesis of per-tree routing-partition
+ per-leaf constructive availability). The hybrid is the natural resolution of the
mismatch identified by reviewer round 2 Q9.

**Why Option C:**
- Matches the kernel-clean routing-partition closure pattern (PR #74) for the
  per-tree reachability piece.
- Satisfies META § 3.2 (constructive per-leaf availability) for the per-leaf
  certificate projection piece.
- Wire format compatible: `BoundedInputCertificateWire` per-leaf payload is preserved
  (the per-tree wrapper is a Lean-only construct).

## Sub-commit sequencing (OPTION C updated — 2026-09-06)

- **v2b.1** — Lemmas 1–2 + supporting definitions (mechanical extraction; kernel-clean in `Q5Integration.lean`)
- **v2b.2** — Lemma 3 + Lemma 4 (trajectory indexing + terminal-claim transport; kernel-clean in `Q5Integration.lean` after the v2b.2 Codex P0 fix)
- **v2b.3** — `transitionOk_implies_step` bridge + `transitionOk_implies_step_forall` (**MERGED** via PR #81 commit `441f878` — kernel-clean)
- **v2b.4** — `BoundedInputCertificateTree` structure + `checkBoundedCertificateTree` function (NEW per-tree wrapper + verifier — depends on v2b.1–3)
- **v2b.5** — `checkBoundedCertificateTree_sound` (per-tree reachability, kernel-clean; analog of `RoutingPartitionCertificate_sound` — depends on v2b.4)
- **v2b.6** — `per_leaf_available_bounded_of_tree` (per-leaf certificate projection; kernel-checked via per-leaf `checkBoundedCertificate_sound` direct path — depends on v2b.5)
- **v2b.7** — Tests (per-tree `check = true` regressions + soundness closure scenario + per-leaf projection regressions — mirrors PR #62 + PR #63 + PR #75 test patterns)

**Staged implementation (Option B per Justin message_id 23317):**
- Stage 1 = spec doc update (this section + design doc) — **CURRENT**
- Stage 2 = v2b.4 implementation (gated on Stage 1 approval)
- Stage 3 = v2b.5 implementation (gated on Stage 2 kernel-clean + GPT-5.6 Terra review)
- Stage 4 = v2b.6 implementation (gated on Stage 3 kernel-clean + review)
- Stage 5 = v2b.7 tests (gated on Stage 4 kernel-clean + review)

Each sub-commit triggers a Codex review round. PR `story-q5-per-tree-with-projection`
stays in DRAFT throughout the staged implementation.

Once GPT-5.6 Terra approves v2b.7 (Stage 5), retitle PR from "v2b Option C staged
implementation" to "v2 — bounded-input integration (closes Q5 4-PR split)" and
remove from draft. No Q5-end-to-end / Q5-complete claim is allowed before v2b.7.

## Open questions

1. **Anchor alignment:** Does each witness's `anchor : Nat` field coincide with the
   `descendOrbit` routing target? If not, Lemma 5 step 6 + Lemma 6 both need an additional
   bridging lemma. v2a's proof attempt hit this issue.
2. **`claim` field placement:** Where does `BoundedInputCertificateData` get its
   `claim : FiniteOrbitClaim` field — witness-level or data-level? PR #62 establishes the
   verifier structure; need to verify which placement supports the per-leaf certificate
   construction.
3. **`wellFormed` field:** Per Q4 v3 Codex run-21858 P2, `BoundedOrbitCertificate` does
   NOT have a `wellFormed` field. Confirm the same for `BoundedInputOrbitCertificate`
   (already true in v2a — verified during v2a review).
4. **Lean 4 indexing notation:** Lemma 3's use of `trajectory[k]!` may need to be
   re-expressed as `trajectory.get (k ⟨h⟩ : k < length)` depending on Lean 4 version
   compatibility. PR #62 + PR #63 use both forms; pick whichever matches the
   existing pattern.

## Lessons applied (Q3 v4 + Q4 v3 + META)

- **Q3 v4 + Q4 v3 (`: Type` sort):** `BoundedInputOrbitCertificate` is `: Type`-valued
  (data + proof fields). The `checkBoundedCertificate_sound` conclusion is
  `BoundedInputOrbitCertificate`, NOT `ReachesOne` directly. Lean 4 elaboration rejects
  `Type`-valued fields in `: Prop` structures.
- **Q4 v3 (Pattern 2.10 conditional companion theorem):** `checkBoundedCertificate_sound`
  takes `hcr` as an explicit hypothesis (no default, no `by sorry`) per PR #51 P1
  discipline. The "constructive availability" pattern stays hypothesis-bearing until the
  full per-leaf hypothesis dataset is supplied.
- **META § 3.2 (per-leaf availability pattern):** Lemma 6 is the constructive form; it
  takes the per-leaf `dataPerLeaf` as an explicit input, mirroring Q4 v3's `hCert`.
- **META § 3.3 (avoid universal acceptance):** the bounded companion theorem stays
  conditional on `hv + hc + hcr`. No `∀ t` universal claim.