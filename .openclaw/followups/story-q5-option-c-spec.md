# Story Q5 — Option C design spec: per-tree verifier with per-leaf certificate projection

**Date:** 2026-09-06T15:40:25Z
**Author:** OpenClaw agent (architectural disposition + spec update)
**Status:** DRAFT (Stage 1 of staged Option B implementation, per Justin message_id 23317)
**Branch:** `story-q5-per-tree-with-projection` (off post-PR-81 merge base `71b1e6e`)
**Tracking:** https://github.com/johrenberger/collatz-research/issues/82

## Why this design

The original v2b design (`docs/story-q5-pr4-v2b-proof-decomposition.md` § 6) used **per-leaf data threading** via `dataPerLeaf : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData`. The GPT-5.6 Terra reviewer round 2 (subagent `0ee9bf18-...`, Q9 P0 stop signal) flagged this as the architectural gate requiring disposition.

The mismatch: `BoundedInputCertificateData` is per-leaf (one `N`/`claim`/`rawWitnesses`), but the kernel-clean routing-partition analog `RoutingPartitionCertificateData` (PR #74, in main) is per-tree (one `N` + `claimRegistry : List LeafClaimWire`). Option C synthesizes both: keep per-leaf data design, add a per-tree wrapper that threads the per-leaf function, verifier becomes per-tree, Lemma 5 returns per-tree reachability (like routing-partition), Lemma 6 projects to per-leaf certificate.

This is the architectural decision Justin authorized at message_id 23313 (Option C selected from `.openclaw/followups/story-2-arch-disposition.md`).

## Architecture diagram

```
                                  LEAF-LEVEL SEMANTIC PREDICATES
                                  ─────────────────────────────────
LeafClaim.interval claim    ─→   LeafReachesOne t l              (Q3 v4)
FiniteOrbitClaim            ─→   OrbitLeafReachesOne t l          (Q4 v3)

                                  PER-TREE CERTIFICATE (NEW Q5 v2b OPTION C)
                                  ──────────────────────────────────────────
BoundedInputCertificateWire     (per-leaf payload: N + rawWitnesses + claim)
   + length_ok
= BoundedInputCertificateData   (per-leaf checked payload)

BoundedInputCertificateTree :   (per-tree wrapper: t + perLeafData)
  - t : CoverageTree
  - perLeafData : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData
  - checkPerLeaf : ∀ l ∈ t.leaves, verified t l →
      checkBoundedCertificate t l (perLeafData l …) = true
                                  ↓
checkBoundedCertificateTree :   (per-tree verifier — no leaf parameter)
  CoverageTree → BoundedInputCertificateTree → Bool

                                  THEOREMS (NEW)
                                  ──────────────────────────────────────────
checkBoundedCertificateTree_sound :  (per-tree reachability, analog of RoutingPartitionCertificate_sound)
  ∀ (t : CoverageTree) (tree : BoundedInputCertificateTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l → ∀ y, (tree.perLeafData l …).wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true) :
    ∀ (x : Nat), 0 < x → x ≤ tree.perLeafData l … .wire.N → ReachesOne x

per_leaf_available_bounded_of_tree :  (per-leaf certificate projection)
  ∀ (t : CoverageTree) (tree : BoundedInputCertificateTree)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : …)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l (tree.perLeafData l hl hver).wire.N
```

## Type signatures

### `BoundedInputCertificateTree` (new per-tree wrapper, replaces per-leaf data threading)

```lean
/-- Per-tree wrapper that holds the per-leaf `BoundedInputCertificateData`
    for every verified leaf in the tree. The verifier
    (`checkBoundedCertificateTree`) walks all leaves at once.

    The per-leaf data is preserved (each leaf has its own
    `N`/`claim`/`rawWitnesses`), satisfying the wire-format
    requirement. The per-tree wrapper threads them through a
    single function value, enabling per-tree verifier calls.

    API-shape parallels `RoutingPartitionCertificateData` (PR #74,
    kernel-clean in main). The two coexist: routing-partition is the
    certificate registry pattern (per-tree list of claims); bounded-
    input is the per-leaf function pattern (per-leaf data + per-tree
    threading). -/
structure BoundedInputCertificateTree (t : CoverageTree) where
  perLeafData : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData
  checkPerLeaf : ∀ l ∈ t.leaves, verified t l →
    checkBoundedCertificate t l (perLeafData l ‹_› ‹_›) = true
```

### `checkBoundedCertificateTree` (per-tree verifier)

```lean
/-- Per-tree verifier. Walks every verified leaf in `t.leaves` and
    returns `true` iff every per-leaf `checkBoundedCertificate` call
    returned `true`. No leaf parameter — the verifier is at the tree
    level, matching the `RoutingPartitionCertificate_sound` analog. -/
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool :=
  List.all (t.leaves.filter (fun l => verified t l))
    (fun l => decide (tree.checkPerLeaf l (List.mem_filter.mp …).1
                                          (List.mem_filter.mp …).2))
```

### `checkBoundedCertificateTree_sound` (Lemma 5 Option C, per-tree reachability)

```lean
/-- **Lemma 5 (per-tree reachability, Option C analog of RoutingPartitionCertificate_sound).**
    If `checkBoundedCertificateTree t tree = true` and every per-leaf
    claim is known to reach one, then every canonical input
    `x ∈ {1, …, N}` (where `N = (tree.perLeafData l …).wire.N` for any
    verified leaf `l`) reaches 1.

    The proof parallels `RoutingPartitionCertificate_sound`: per-tree
    reachability is derived from per-leaf acceptances (via the per-leaf
    witness extraction) + the per-leaf `claim_reaches_one` hypotheses.

    Signature parallels `RoutingPartitionCertificate_sound` (per-tree
    reachability, NOT per-leaf certificate construction). -/
theorem checkBoundedCertificateTree_sound
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l →
      ∀ y, (tree.perLeafData l …).wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true)
    : ∀ (x : Nat), 0 < x →
        x ≤ (tree.perLeafData l …).wire.N →  -- for some l (all leaves share N)
        ReachesOne x := by
  ...
```

### `per_leaf_available_bounded_of_tree` (Lemma 6 Option C, per-leaf certificate projection)

```lean
/-- **Lemma 6 (per-leaf certificate projection, Option C).**
    Given a per-tree `BoundedInputCertificateTree` + the per-tree
    structural hypotheses + per-leaf `claim_reaches_one` hypotheses,
    project to the per-leaf `BoundedInputOrbitCertificate t l N`
    certificate for any verified leaf `l`.

    Construction:
    1. Apply `checkBoundedCertificate_sound` (the per-leaf Lemma 5)
       to `tree.perLeafData l hl hver` + the per-leaf
       `tree.checkPerLeaf l hl hver` evidence + the per-leaf
       `hcr l hl hver` hypothesis. This gives the per-leaf certificate
       directly.

    Alternatively, construct the per-leaf certificate from the
    per-tree `checkBoundedCertificateTree_sound` reachability + the
    per-leaf routing evidence — depends on the kernel-clean per-tree
    soundness closure (the cleaner path).

    API-shape parallels the original `per_leaf_available_bounded_of_check`
    but takes the per-tree wrapper as input (not the per-leaf function). -/
theorem per_leaf_available_bounded_of_tree
    (t : CoverageTree) (tree : BoundedInputCertificateTree t)
    (hv : ValidTree t) (hic : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, verified t l →
      ∀ y, (tree.perLeafData l …).wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificateTree t tree = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l) :
    BoundedInputOrbitCertificate t l (tree.perLeafData l hl hver).wire.N := by
  -- Direct path via per-leaf Lemma 5 + tree's per-leaf check:
  exact checkBoundedCertificate_sound t l (tree.perLeafData l hl hver)
    hv hic hver (hcr l hl hver) (tree.checkPerLeaf l hl hver)
```

## Sub-commit sequencing (updated from v2b)

The original v2b.1–v2b.6 sequencing had Lemmas 5+6 attempting per-leaf closure directly. Under Option C, the sequencing becomes:

- **v2b.1** — Lemmas 1–2 + supporting definitions (UNCHANGED — kernel-clean in Q5Integration.lean)
- **v2b.2** — Lemma 3 + Lemma 4 (UNCHANGED — kernel-clean in Q5Integration.lean)
- **v2b.3** — `transitionOk_implies_step` bridge + `transitionOk_implies_step_forall` (MERGED via PR #81 commit `441f878` — kernel-clean)
- **v2b.4** — `BoundedInputCertificateTree` structure + `checkBoundedCertificateTree` function (NEW per-tree wrapper + verifier)
- **v2b.5** — `checkBoundedCertificateTree_sound` (per-tree reachability, kernel-clean; analog of `RoutingPartitionCertificate_sound`)
- **v2b.6** — `per_leaf_available_bounded_of_tree` (per-leaf certificate projection; kernel-checked via `checkBoundedCertificate_sound` direct path)
- **v2b.7** — Tests (per-tree `check = true` regressions + soundness closure scenario + per-leaf projection regressions)

## Stage mapping (Option B staged implementation)

- **Stage 1 (this stage):** Spec doc update (this file + `docs/story-q5-pr4-v2b-proof-decomposition.md` § 6 update). DRAFT PR for review.
- **Stage 2:** v2b.4 implementation — `BoundedInputCertificateTree` structure + `checkBoundedCertificateTree` function. New file `Lean/CollatzResearch/BoundedInputCertificateTree.lean`.
- **Stage 3:** v2b.5 implementation — `checkBoundedCertificateTree_sound`. Append to `BoundedInputCertificateTree.lean` or new file.
- **Stage 4:** v2b.6 implementation — `per_leaf_available_bounded_of_tree`. Append.
- **Stage 5:** v2b.7 tests.

Each stage gated on prior stage being kernel-clean + GPT-5.6 Terra review approved.

## Architectural decision rationale (recap)

**Why per-tree verifier (not per-leaf):**
- Matches the kernel-clean routing-partition closure pattern (PR #74) — proven to compile.
- Wire format compatibility: `RoutingPartitionCertificateWire` already has `claimRegistry : List LeafClaimWire`; per-tree wrapper is the natural shape.
- API simplification: caller doesn't need to thread per-leaf data + check functions separately — one `BoundedInputCertificateTree` carries both.

**Why per-leaf certificate projection (not per-tree reachability only):**
- Satisfies META § 3.2 (constructive per-leaf availability) — required by `docs/story-q5-external-certificate-inhabitation.md` § 4.4.
- Downstream callers that need per-leaf `BoundedInputOrbitCertificate t l N` (for composition with `coverage_tree_soundness_orbit_cert_bounded`) get the per-leaf certificate directly.
- Spec continuity with the original v2b design's intent (just the threading pattern changes).

**Why not pure per-tree reachability (Option B from disposition doc):**
- Drops META § 3.2 (constructive per-leaf availability) — would require spec drift.

**Why not pure per-leaf (current attempt, Option A from disposition doc):**
- Reviewer round 2 Q9 P0 explicitly flagged this as the architectural mismatch requiring disposition.

## Trust boundary

- Per `formal-math-codex-escalate`: all implementation gated on Justin's spec approval (Stage 1) + each subsequent stage's GPT-5.6 Terra review.
- No `sorry` / `admit` / `axiom` introduced — explicit hypothesis preservation per PR #51 P1 discipline.
- Stage 1 is docs-only (no Lean code changes) — fully reversible by closing the PR.
- The architectural decision (Option C) is logged in `.openclaw/followups/story-2-arch-disposition.md` + this file + Issue #82.

## Open questions for Justin's spec review

1. **`BoundedInputCertificateTree` design:** Is the per-tree wrapper structure (with `perLeafData` + `checkPerLeaf` fields) the right shape? Alternative: `BoundedInputCertificateTree (t : CoverageTree) where perLeafData : (l : CoverageLeaf) → l ∈ t.leaves → verified t l → BoundedInputCertificateData` (single-field wrapper, no `checkPerLeaf` field; check is derived from `checkBoundedCertificate t l (perLeafData l …) = true` at use-sites).
2. **`checkBoundedCertificateTree` semantics:** Should it return `Bool` (single-bit all-leaves-checked) or `List Bool` (per-leaf check results)? The first is simpler; the second carries more diagnostic info.
3. **`per_leaf_available_bounded_of_tree` projection path:** Direct via per-leaf `checkBoundedCertificate_sound` (shown above) or via per-tree `checkBoundedCertificateTree_sound` + per-leaf routing? Direct is simpler; per-tree is more elegant but requires more lemmas.
4. **Wire format changes:** Does the wire format need to change from `BoundedInputCertificateWire` (per-leaf payload) to a per-tree wrapper? Or is the per-tree wrapper a Lean-only construct that doesn't affect the wire format?
5. **Tests:** Should v2b.7 include both per-tree regressions AND per-leaf projection regressions? Or only per-leaf (since per-tree is the upstream dependency)?
