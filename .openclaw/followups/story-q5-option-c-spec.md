# Story Q5 — Option C design spec: thin wrapper over `RoutingPartitionCertificateData`

**Date:** 2026-09-06T15:56:40Z (revised per reviewer round 3)
**Author:** OpenClaw agent (architectural disposition + spec update)
**Status:** DRAFT (Stage 1 of staged Option B implementation, per Justin message_id 23317; revised per message_id 23323)
**Branch:** `story-q5-per-tree-with-projection` (off post-PR-81 merge base `71b1e6e`)
**Tracking:** https://github.com/johrenberger/collatz-research/issues/82

## Revision history

- **2026-09-06T15:40:25Z** (initial Option C spec) — per-tree wrapper over legacy `BoundedInputCertificateData` (per-leaf payload).
- **2026-09-06T15:56:40Z** (this revision, per reviewer round 3) — **THIN WRAPPER over `RoutingPartitionCertificateData`** (PR #74, kernel-clean). Drops the legacy `BoundedInputCertificateData` + `checkBoundedCertificate` per-leaf payload from the architecture. The "bounded-input" nature comes from `RoutingPartitionCertificateData.wire.N` (the canonical input bound) — no new data structure needed.

## Why this revision

Reviewer round 3 (subagent `9464f91e-...`) found that my Option C hybrid (per-tree wrapper over legacy `BoundedInputCertificateData`) was on the right track but the **specific underlying data structure was wrong**:
- Legacy `BoundedInputCertificateData` is per-leaf (one `N`/`claim`/`rawWitnesses`) — doesn't naturally serialize as a single per-tree bundle.
- Routing-partition data (`RoutingPartitionCertificateData`, PR #74, kernel-clean) is per-tree (one `N` + `claimRegistry : List LeafClaimWire` + `routingWitness`) — already kernel-clean in main.
- Reusing the routing-partition data eliminates the need to reinvent the per-tree wrapper.

The reviewer also flagged that the direct projection path (per-leaf `checkBoundedCertificate_sound`) **repeats the fixed-leaf error** — its checker requires every witness to match the supplied fixed leaf, which doesn't compose with the per-tree verifier's `claimRegistry`. The fix is to use an intermediate extraction theorem `routing_partition_leaf_certificate` that constructs the per-leaf `BoundedInputOrbitCertificate` from per-tree reachability + per-leaf routing.

## Architecture diagram (revised)

```
                                  EXISTING KERNEL-CLEAN UPSTREAM (PR #74)
                                  ──────────────────────────────────────────
RoutingPartitionCertificateWire     (per-tree payload: N + claimRegistry + routingWitness)
= RoutingPartitionCertificateData  (PR #74, kernel-clean in main)

checkRoutingPartitionCertificate :   (per-tree verifier, no leaf parameter)
  CoverageTree → RoutingPartitionCertificateData → Bool

RoutingPartitionCertificate_sound :   (per-tree reachability)
  ∀ (x : Nat), 0 < x → x ≤ d.wire.N → ReachesOne x

                                  NEW Q5 v2b OPTION C — THIN WRAPPER
                                  ──────────────────────────────────────────
BoundedInputCertificateTree :   (THIN WRAPPER over RoutingPartitionCertificateData)
  - certData : RoutingPartitionCertificateData     ← use existing kernel-clean
  - per-tree RoutingPartitionCertificateData carries the N bound (wire.N)
                                                  ↓
checkBoundedCertificateTree :   (delegates to routing-partition verifier)
  BoundedInputCertificateTree → Bool
  := checkRoutingPartitionCertificate t tree.certData

                                  THEOREMS (NEW)
                                  ──────────────────────────────────────────
checkBoundedCertificateTree_sound :   (per-tree reachability — directly inherits RoutingPartitionCertificate_sound)
  ∀ (x : Nat), 0 < x → x ≤ tree.certData.wire.N → ReachesOne x

routing_partition_leaf_certificate :   (NEW intermediate extraction theorem — per-leaf certificate from per-tree reachability + per-leaf routing)
  ∀ (l : CoverageLeaf), l ∈ t.leaves, verified t l →
    BoundedInputOrbitCertificate t l tree.certData.wire.N

per_leaf_available_bounded_of_tree :   (per-leaf certificate projection — satisfies META § 3.2)
  ≡ routing_partition_leaf_certificate (after scaffolding)
```

## Type signatures (revised)

### `BoundedInputCertificateTree` (thin wrapper over `RoutingPartitionCertificateData`)

```lean
/-- Thin per-tree wrapper that exposes the kernel-clean
    `RoutingPartitionCertificateData` (PR #74) in the bounded-input
    context. The "bounded-input" nature comes from
    `certData.wire.N` (the canonical input bound).

    The verifier `checkBoundedCertificateTree` delegates to
    `checkRoutingPartitionCertificate` (no duplicate verifier logic).
    No `checkPerLeaf` field — verifier recomputes acceptance (matches
    routing-partition's recomputation pattern; no stored check proofs). -/
structure BoundedInputCertificateTree (t : CoverageTree) where
  certData : RoutingPartitionCertificateData
```

### `checkBoundedCertificateTree` (delegates to routing-partition)

```lean
/-- Per-tree verifier. Delegates to
    `checkRoutingPartitionCertificate` (PR #74 kernel-clean) — no
    duplicate logic, no new surface area. Returns `Bool` matching the
    routing-partition signature. -/
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool :=
  checkRoutingPartitionCertificate t tree.certData
```

### `checkBoundedCertificateTree_sound` (per-tree reachability, inherits `RoutingPartitionCertificate_sound`)

```lean
/-- **Lemma 5 (per-tree reachability, Option C).**
    If `checkBoundedCertificateTree t tree = true` and every entry in
    `tree.certData.wire.claimRegistry` is known to reach 1, then every
    canonical input `x ∈ {1, …, N}` reaches 1.

    The proof directly inherits `RoutingPartitionCertificate_sound`
    (PR #74 kernel-clean) — the thin wrapper means the per-tree
    reachability is exactly the routing-partition reachability. -/
theorem checkBoundedCertificateTree_sound
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true) :
    ∀ (x : Nat), 0 < x → x ≤ tree.certData.wire.N → ReachesOne x :=
  RoutingPartitionCertificate_sound t tree.certData hcheck hcr
```

### `routing_partition_leaf_certificate` (NEW intermediate extraction)

```lean
/-- **Intermediate extraction (per-leaf certificate from per-tree reachability).**
    Given the per-tree `checkBoundedCertificateTree_sound` reachability +
    a per-leaf routing evidence (`descendOrbit t x 0 = some l` for each
    `x` in `l`'s routing preimage) + the per-leaf claim hypothesis
    (from the claimRegistry), construct the per-leaf
    `BoundedInputOrbitCertificate t l N`.

    This is the bridge from per-tree reachability (Lemma 5) to
    per-leaf certificate (META § 3.2 — constructive per-leaf availability).

    Construction sketch:
    1. For each `x ∈ {1, …, N}` with `descendOrbit t x 0 = some l` and
       `hver : verified t l`, apply `checkRoutingPartitionCertificate_accepts_slot`
       (PR #74, per-slot acceptance) to get the routing evidence.
    2. Apply `RoutingPartitionCertificate_sound` reachability to get
       `ReachesOne x` (per-tree).
    3. For each `x` in `l`'s preimage, the leaf's claim entry in
       `claimRegistry` provides the `claim.Holds` evidence.
    4. Construct `BoundedInputOrbitCertificate` with:
       - `claim` = the leaf's claim (from `claimRegistry`)
       - `claim_reaches_one` = the per-leaf `hcr` hypothesis
       - `orbit_hits_claim` = assembled from steps 1-3.

    The construction mirrors `RoutingPartitionCertificate_sound` +
    `descend_orbit_complete` (PR #29). -/
theorem routing_partition_leaf_certificate
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N := by
  ...
```

### `per_leaf_available_bounded_of_tree` (per-leaf certificate projection, satisfies META § 3.2)

```lean
/-- **Lemma 6 (per-leaf certificate projection, Option C).**
    Given a per-tree `BoundedInputCertificateTree` + the per-tree
    structural hypotheses + per-leaf claim-reachability hypotheses,
    project to the per-leaf `BoundedInputOrbitCertificate t l N` for
    any verified leaf `l`.

    Direct alias for `routing_partition_leaf_certificate` — the
    intermediate extraction IS the per-leaf projection (no separate
    forward needed). Satisfies META § 3.2 (constructive per-leaf
    availability). -/
theorem per_leaf_available_bounded_of_tree
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hcr : ∀ (entry : LeafClaimWire),
      entry ∈ tree.certData.wire.claimRegistry →
      ∀ y, entry.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l tree.certData.wire.N :=
  routing_partition_leaf_certificate t tree hcr hcheck l hl hver
```

## Sub-commit sequencing (revised)

The revised sequencing is shorter because the per-tree reachability is inherited from routing-partition:

- **v2b.1** — Lemmas 1–2 + supporting definitions (kernel-clean in `Q5Integration.lean`)
- **v2b.2** — Lemma 3 + Lemma 4 (kernel-clean in `Q5Integration.lean` after the v2b.2 Codex P0 fix)
- **v2b.3** — `transitionOk_implies_step` bridge + `transitionOk_implies_step_forall` (**MERGED** via PR #81 commit `441f878` — kernel-clean)
- **v2b.4** — `BoundedInputCertificateTree` structure + `checkBoundedCertificateTree` delegation (THIN WRAPPER over `RoutingPartitionCertificateData` + `checkRoutingPartitionCertificate`)
- **v2b.5** — `checkBoundedCertificateTree_sound` (per-tree reachability, inherits `RoutingPartitionCertificate_sound`)
- **v2b.6** — `routing_partition_leaf_certificate` (intermediate extraction theorem — the NEW bridge from per-tree reachability to per-leaf certificate)
- **v2b.7** — `per_leaf_available_bounded_of_tree` (alias for v2b.6 — satisfies META § 3.2)
- **v2b.8** — Tests (per-tree + per-leaf regressions — mirrors PR #75 routing-partition test patterns)

**Staged implementation (Option B per Justin message_id 23317):**
- Stage 1 = spec doc update (this revision + new push on PR #84) — **CURRENT**
- Stage 2 = v2b.4 implementation (gated on Stage 1 approval)
- Stage 3 = v2b.5 implementation (gated on Stage 2 kernel-clean + GPT-5.6 Terra review)
- Stage 4 = v2b.6 + v2b.7 implementation (gated on Stage 3 kernel-clean + review)
- Stage 5 = v2b.8 tests (gated on Stage 4 kernel-clean + review)

## Architectural decision rationale (revised)

**Why thin wrapper over `RoutingPartitionCertificateData`:**
- Eliminates the need to invent a parallel bounded-input data structure (Q4 reviewer recommendation).
- Leverages the kernel-clean routing-partition closure (PR #74) for both verifier (`checkRoutingPartitionCertificate`) and soundness (`RoutingPartitionCertificate_sound`).
- Wire format compatible: no new wire types — `BoundedInputCertificateTree.certData` IS a `RoutingPartitionCertificateData` which has its existing wire (`RoutingPartitionCertificateWire`).
- The "bounded-input" nature is just the `N` field from `certData.wire.N` — no new machinery.

**Why per-tree path with intermediate extraction (NOT direct path):**
- Direct path via per-leaf `checkBoundedCertificate_sound` (the original v2b attempt) **repeats the fixed-leaf error** — its checker requires every witness to match the supplied fixed leaf, which doesn't compose with the per-tree verifier's `claimRegistry` (where each leaf's claim is a separate entry).
- Intermediate extraction `routing_partition_leaf_certificate` bridges per-tree reachability to per-leaf certificate cleanly via the routing-partition kernel-clean lemmas.

**Why no `checkPerLeaf` field (single-field wrapper):**
- Routing-partition pattern: verifier recomputes acceptance from wire + structural invariants, not from stored proofs.
- Storing `checkPerLeaf` would make the verifier a `decide` over already-supplied proofs (not real validation).
- Matches `RoutingPartitionCertificateData` shape (which stores `wire` + `routingWitness` but not pre-computed check results).

## Trust boundary

- Per `formal-math-codex-escalate`: all implementation gated on Justin's spec approval (this revision) + each subsequent stage's GPT-5.6 Terra review.
- No `sorry` / `admit` / `axiom` introduced.
- Stage 1 is docs-only (no Lean code changes) — fully reversible by closing the PR.
- The architectural decision (revised Option C) is logged in `.openclaw/followups/story-2-arch-disposition.md` + this file + Issue #82.

## Open questions for Justin's spec review (revised)

The 5 original questions are now resolved by the reviewer's recommendations:
- **Q1 (resolved):** Single-field `BoundedInputCertificateTree` wrapping `RoutingPartitionCertificateData` (no `checkPerLeaf`).
- **Q2 (resolved):** `checkBoundedCertificateTree : Bool` (delegates to routing-partition).
- **Q3 (resolved):** Per-tree path with intermediate `routing_partition_leaf_certificate` (no direct path).
- **Q4 (resolved):** Use existing `RoutingPartitionCertificateWire` (no new wire types).

**Remaining question (new):**
1. **`routing_partition_leaf_certificate` proof shape:** Does the construction from per-tree reachability + per-leaf routing directly parallel `RoutingPartitionCertificate_sound` + `descend_orbit_complete` (PR #29)? Or are there subtleties about per-leaf routing lookup against `claimRegistry` (e.g., how does the leaf `l` find its corresponding entry in `claimRegistry`)? Worth pre-staging a proof sketch before Stage 4 implementation.
