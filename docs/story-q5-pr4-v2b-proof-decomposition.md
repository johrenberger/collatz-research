# Story Q5 PR #4 — v2b Proof Decomposition Plan

Companion to `docs/story-q5-external-certificate-inhabitation.md` (Q5 spec, PR #61).
Companion to `docs/story-q4-bounded-orbit-certificates.md` (Q4 v3 proof arc).

## Status — arc closed at v2b.9 (2026-11-08)

The v2b sub-arc is closed. v2b.9 landed as PR #99 (merged 2026-10-24, commit
`4309cab`), and the four open questions below are answered against the code
that shipped; the answers are in **Open questions — answered**.

Two things this plan states in the present tense were superseded by the Option C
redesign in §6 before that closure, and are corrected here:

- The `checkBoundedCertificate_sound` goal statement (below) and the Lemma 5
  assembly in §5 were **withdrawn** by the Codex P0 review of 2026-09-02.
  `checkBoundedCertificate_sound` has **no declaration in `Lean/`**. Its shipped
  successor is `checkBoundedCertificateTree_sound`
  (`Lean/CollatzResearch/BoundedInputCertificateTree.lean:117`), which
  delegates to `RoutingPartitionCertificate_sound`
  (`Lean/CollatzResearch/Q5RoutingPartition.lean:318`).
- The v2b.7 alias shipped under the name `per_leaf_available_bounded_of_check`
  (`Lean/CollatzResearch/BoundedInputCertificateTree.lean:368`), not
  `per_leaf_available_bounded_of_tree`; the module docstring at
  `BoundedInputCertificateTree.lean:352` records that rename and its reason.

**Closure scope.** The Q5 arc closes on the routing-partition path at the ADR
0009 reachability evidence tier: the reachability premise that the Option C
theorems carried as a hypothesis is **discharged by checked evidence rather
than assumed**, for claims whose terminal value is 1. It does **not** close the
legacy `checkBoundedCertificate` path, and it asserts neither global
convergence nor nontrivial-cycle exclusion.

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

### 6. constructive per-leaf availability theorem (OPTION C redesign, REVISED — 2026-09-06T15:56:40Z)

**Architectural disposition (per Justin calls message_id 23313 + 23323):** **Option C**
(hybrid: per-tree verifier with per-leaf certificate projection), **revised per
GPT-5.6 Terra reviewer round 3 (subagent `9464f91e-...`)** to use `RoutingPartitionCertificateData`
(PR #74, kernel-clean in main) as the underlying data structure instead of legacy
`BoundedInputCertificateData`. Supersedes the original v2b per-leaf design (Option A,
flagged as architecturally mismatched by reviewer round 2 Q9). Full disposition in
`.openclaw/followups/story-2-arch-disposition.md`; design details in
`.openclaw/followups/story-q5-option-c-spec.md`.

**Type:**

```lean
-- THIN WRAPPER over the kernel-clean RoutingPartitionCertificateData (PR #74):
structure BoundedInputCertificateTree (t : CoverageTree) where
  certData : RoutingPartitionCertificateData   -- single field; no perLeafData / no checkPerLeaf

-- Per-tree verifier (delegates to checkRoutingPartitionCertificate):
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool :=
  checkRoutingPartitionCertificate t tree.certData

-- Lemma 5 (per-tree reachability — DIRECTLY inherits RoutingPartitionCertificate_sound):
theorem checkBoundedCertificateTree_sound
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true) :
    ∀ (x : Nat), 0 < x → x ≤ tree.certData.wire.N → ReachesOne x :=
  RoutingPartitionCertificate_sound t tree.certData hcheck hcr

-- NEW intermediate extraction (per-leaf certificate from per-tree reachability + per-leaf routing):
theorem routing_partition_leaf_certificate
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N := by
  -- Construction uses `descend_orbit_complete` (PR #29) +
  --   `checkRoutingPartitionCertificate_accepts_slot` (PR #74) +
  --   `RoutingPartitionCertificate_sound` (PR #74).
  ...

-- Lemma 6 (per-leaf certificate projection — alias for routing_partition_leaf_certificate):
theorem per_leaf_available_bounded_of_tree
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : …)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N :=
  routing_partition_leaf_certificate t tree hcr hcheck l hl hver
```

**Strategy:** The thin wrapper means the per-tree reachability (Lemma 5) IS the
routing-partition reachability — no new soundness theorem, just a delegation.
The NEW intermediate extraction `routing_partition_leaf_certificate` bridges per-tree
reachability + per-leaf routing evidence (`descendOrbit t x 0 = some l`) to the
per-leaf `BoundedInputOrbitCertificate`. Lemma 6 is a direct alias for this
extraction (no separate forward needed).

Supersedes the v2a hypothesis-eliminator form `per_leaf_available_bounded_of_hCert`,
the v2b per-leaf `per_leaf_available_bounded_of_check` (Option A, architecturally
mismatched), and the intermediate Option C spec with legacy
`BoundedInputCertificateData` (revision 2026-09-06T15:40:25Z).

**Dependencies:** `RoutingPartitionCertificateData` (PR #74, kernel-clean) +
`RoutingPartitionCertificate_sound` (PR #74, kernel-clean) +
`checkRoutingPartitionCertificate_accepts_slot` (PR #74, per-slot acceptance) +
`descend_orbit_complete` (PR #29) + `orbit_predecessor_reaches_one` (PR #56).

**Risk:** Low. The thin wrapper over kernel-clean routing-partition data eliminates
the legacy per-leaf `checkBoundedCertificate_sound` direct path (which repeated the
fixed-leaf error per reviewer round 3). The intermediate extraction
`routing_partition_leaf_certificate` is the natural bridge, paralleling the
kernel-clean routing-partition closure pattern.

**Why revised Option C (per reviewer round 3):**
- **Q1:** Single-field `BoundedInputCertificateTree` wrapping
  `RoutingPartitionCertificateData` — no `checkPerLeaf` field (verifier recomputes,
  matches routing-partition pattern).
- **Q2:** `checkBoundedCertificateTree : Bool` — matches
  `checkRoutingPartitionCertificate` signature.
- **Q3:** Per-tree path with intermediate `routing_partition_leaf_certificate` —
  direct path via per-leaf `checkBoundedCertificate_sound` repeats the fixed-leaf
  error.
- **Q4:** Use existing `RoutingPartitionCertificateWire` — no new wire types needed.

## Sub-commit sequencing (OPTION C REVISED — 2026-09-06T15:56:40Z)

The revised sequencing is shorter because the per-tree reachability is inherited from
routing-partition (no new soundness theorem needed):

- **v2b.1** — Lemmas 1–2 + supporting definitions (kernel-clean in `Q5Integration.lean`)
- **v2b.2** — Lemma 3 + Lemma 4 (kernel-clean in `Q5Integration.lean` after the v2b.2 Codex P0 fix)
- **v2b.3** — `transitionOk_implies_step` bridge + `transitionOk_implies_step_forall` (**MERGED** via PR #81 commit `441f878` — kernel-clean)
- **v2b.4** — `BoundedInputCertificateTree` structure + `checkBoundedCertificateTree` delegation (THIN WRAPPER over `RoutingPartitionCertificateData` + `checkRoutingPartitionCertificate` — kernel-clean delegation; depends on v2b.1–3; **MERGED** via PR #85, commit `139ab69`)
- **v2b.5** — `checkBoundedCertificateTree_sound` (per-tree reachability; DIRECTLY inherits `RoutingPartitionCertificate_sound`; depends on v2b.4; **MERGED** via PR #86, commit `4a3d09e`)
- **v2b.6** — `routing_partition_leaf_certificate` (NEW intermediate extraction — bridges per-tree reachability + per-leaf routing to per-leaf `BoundedInputOrbitCertificate`; depends on v2b.5 + `descend_orbit_complete` (PR #29); **MERGED** via PR #91, commit `ffd54b6`)
- **v2b.7** — `per_leaf_available_bounded_of_check` (alias for v2b.6 — satisfies META § 3.2; depends on v2b.6; **MERGED** via PR #92, commit `8255f7a`. Shipped under the spec name, not the `per_leaf_available_bounded_of_tree` name used in the v2b.7 summary — see the naming note at `BoundedInputCertificateTree.lean:352`)
- **v2b.8** — Tests (per-tree + per-leaf regressions — mirrors PR #75 routing-partition test patterns; depends on v2b.7; **MERGED** via PR #93, commit `bfeb4a1` and PR #96, commit `0a048d9`)
- **v2b.9** — Concrete per-leaf discharge for v2b.6 + v2b.7 against the canonical two-leaf fixture (`twoLeaf_routing_partition_leaf_certificate` at `Q5Stage4Tests.lean:341`, `twoLeaf_per_leaf_available_bounded_of_check` at `Q5Stage4Tests.lean:358`; **MERGED** via PR #99, commit `4309cab`, 2026-10-24 — kernel-clean, no admitted declarations)

**Staged implementation (Option B per Justin message_id 23317) — all stages landed:**
- Stage 1 = spec doc update (this section + design doc) — **MERGED** via PR #84, commit `400b7ea`
- Stage 2 = v2b.4 implementation — **MERGED** via PR #85, commit `139ab69`
- Stage 3 = v2b.5 implementation — **MERGED** via PR #86, commit `4a3d09e`
- Stage 4 = v2b.6 + v2b.7 implementation — **MERGED** via PR #91, commit `ffd54b6` and PR #92, commit `8255f7a`
- Stage 5 = v2b.8 tests — **MERGED** via PR #93, commit `bfeb4a1` and PR #96, commit `0a048d9`; v2b.9 closure — **MERGED** via PR #99, commit `4309cab`

Each sub-commit triggers a Codex review round. PR `story-q5-per-tree-with-projection`
stays in DRAFT throughout the staged implementation.

Once GPT-5.6 Terra approves v2b.8 (Stage 5), retitle PR from "v2b Option C revised
staged implementation" to "v2 — bounded-input integration (closes Q5 4-PR split)" and
remove from draft. No Q5-end-to-end / Q5-complete claim is allowed before v2b.8.

*The v2b.8 gate is satisfied: v2b.8 landed via PR #96 and v2b.9 via PR #99. What
that gate unlocks is the scoped closure recorded in **Status — arc closed at
v2b.9** above: the routing-partition path closes at the ADR 0009
terminal-value-one tier. The legacy `checkBoundedCertificate` path still has no
soundness theorem, and no convergence or cycle-exclusion claim is unlocked.*

## Open questions — answered

Each question below is answered against the code that shipped, not against the
plan that asked it.

1. **Anchor alignment — resolved, and not by the bridging lemma this plan
   expected.** The `anchor : Nat` field the question presupposes does not
   exist: `CertWitness` (`Lean/CollatzResearch/BoundedInputCertificateData.lean:108`)
   carries only `l` and `trajectory`, and the canonical input is the type index
   `x`. The anchor obligation is discharged at two separate points.
   `anchorOk` (`Lean/CollatzResearch/Q5Integration.lean:353`) checks that the
   trajectory head equals `x`, and `trajectory_anchor_orbit_step`
   (`Lean/CollatzResearch/Q5Stage4Subproofs.lean:274`) proves
   `w.trajectory[k]! = accelerated_orbit x k` from that anchor check plus the
   per-step transition relation. The `descendOrbit` routing alignment is a
   separate obligation, discharged by `sameCoverageLeaf_eq` /
   `sameCoverageLeaf_congr_eq`
   (`Lean/CollatzResearch/Q5Stage4Subproofs.lean:134`) together with
   `registry_unique_of_pairwise_irrefl`
   (`Lean/CollatzResearch/Q5Stage4Subproofs.lean:191`), and consumed inside
   `routing_partition_leaf_certificate`
   (`Lean/CollatzResearch/BoundedInputCertificateTree.lean:179`). The v2a wall
   was an artifact of the single-leaf design; the routing-partition design
   routes per canonical slot instead.
2. **`claim` field placement — leaf-level, in the registry.** The placement
   that supports the per-leaf construction is one claim per registry entry:
   `LeafClaimWire` (`Lean/CollatzResearch/BoundedInputCertificateData.lean:306`)
   pairs a `leaf : CoverageLeaf` with a `claim : FiniteOrbitClaim`, and
   `RoutingPartitionCertificateWire.claimRegistry`
   (`Lean/CollatzResearch/BoundedInputCertificateData.lean:313`) carries the
   list of them. The per-leaf certificate takes `claim := entry_canon.claim`
   from the canonical registry entry for that leaf
   (`Lean/CollatzResearch/BoundedInputCertificateTree.lean:211`). The legacy
   data-level field on `BoundedInputCertificateWire`
   (`Lean/CollatzResearch/BoundedInputCertificateData.lean:119`) still exists,
   but it sits on the path this arc closed without.
3. **`wellFormed` field — confirmed absent.** `BoundedInputOrbitCertificate`
   (`Lean/CollatzResearch/Q5Integration.lean:175`) has exactly three fields —
   `claim`, `orbit_hits_claim`, `claim_reaches_one` — and no `wellFormed`
   field, matching `BoundedOrbitCertificate`
   (`Lean/CollatzResearch/CoverageTree.lean:695`). The v2a reading was right.
4. **Lean 4 indexing notation — `trajectory[k]!` was retained.** No
   re-expression to `trajectory.get (k ⟨h⟩)` was needed.
   `trajectory_index` (`Lean/CollatzResearch/Q5Integration.lean:570`) states
   `(w.trajectory)[k]! = accelerated_orbit x k`, and
   `trajectory_anchor_orbit_step`
   (`Lean/CollatzResearch/Q5Stage4Subproofs.lean:274`) uses
   `w.trajectory[k]!` in the same form.

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