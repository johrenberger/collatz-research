/-
Q5 v2b.4 — `BoundedInputCertificateTree`: thin per-tree wrapper
over `RoutingPartitionCertificateData`.

Story Q5 / Stage 2 of Option B staged implementation of Option C
(per-tree verifier with per-leaf certificate projection).

## Stage 2 scope

This module is the **v2b.4 thin wrapper** per
`docs/story-q5-pr4-v2b-proof-decomposition.md` § 6 + the design doc
at `.openclaw/followups/story-q5-option-c-spec.md`. It introduces:

1. `BoundedInputCertificateTree` — a single-field structure wrapping
   the kernel-clean `RoutingPartitionCertificateData` (PR #74). The
   "bounded-input" nature comes from `certData.wire.N` (the canonical
   input bound).
2. `checkBoundedCertificateTree` — a one-line delegation to
   `checkRoutingPartitionCertificate` (PR #74, kernel-clean).

## Why this design

Per GPT-5.6 Terra reviewer round 3 (Q1–Q4, subagent `9464f91e-...`):

- **Q1 (single-field wrapper):** `certData : RoutingPartitionCertificateData`.
  No `perLeafData`, no `checkPerLeaf` — the verifier recomputes
  acceptance (matches routing-partition's recomputation pattern; no
  stored check proofs).
- **Q2 (`Bool` return):** `checkBoundedCertificateTree : Bool` —
  delegates to `checkRoutingPartitionCertificate : Bool`.
- **Q4 (existing wire):** Use existing `RoutingPartitionCertificateWire`.
  No new wire types. The thin wrapper means no wire-format changes.

## Kernel-clean upstream

- `RoutingPartitionCertificateData` — `BoundedInputCertificateData.lean:281`
  (kernel-clean, PR #74).
- `checkRoutingPartitionCertificate` — `BoundedInputCertificateData.lean:362`
  (kernel-clean, PR #74).
- `RoutingPartitionCertificate_sound` — `Q5RoutingPartition.lean`
  (kernel-clean, PR #74 — directly inherited by Stage 3 v2b.5).

## Trust boundary

- **No unproven declarations introduced.**
- **Delegation is kernel-clean by construction** — delegates to
  existing kernel-clean code; the new code is a thin type-level
  adapter only.
- Per `formal-math-codex-escalate`: this is a bounded one-piece Stage 2
  implementation. Expected outcome: kernel-clean on first push.
- Per `collatz-pr-review-gate`: a GPT-5.6 Terra reviewer round will
  verify the design + delegation before Stage 3 proceeds.

## Tracking

- PR #84 (Stage 1 spec merge — closed): https://github.com/johrenberger/collatz-research/pull/84
- PR #74 (RoutingPartitionCertificate_sound, kernel-clean upstream)
- Issue #82 (Lemmas 5+6 follow-up)
- Design doc: `.openclaw/followups/story-q5-option-c-spec.md`
- Disposition doc: `.openclaw/followups/story-2-arch-disposition.md`
-/

import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-- Per-tree wrapper that exposes the kernel-clean
    `RoutingPartitionCertificateData` (PR #74) in the bounded-input
    context. The "bounded-input" nature comes from
    `certData.wire.N` (the canonical input bound).

    The verifier `checkBoundedCertificateTree` delegates to
    `checkRoutingPartitionCertificate` (no duplicate verifier logic,
    no new surface area).

    **Why single-field (per reviewer round 3 Q1):** No `checkPerLeaf`
    field — the verifier recomputes acceptance from the wire data +
    structural invariants, matching the routing-partition
    recomputation pattern. Storing `checkPerLeaf` would make the
    verifier a `decide` over already-supplied proofs (not real
    validation), which is not the design intent.

    See `.openclaw/followups/story-q5-option-c-spec.md` §
    "Type signatures" for the full design rationale. -/
structure BoundedInputCertificateTree (t : CoverageTree) where
  certData : RoutingPartitionCertificateData

/-- Per-tree verifier. Delegates to `checkRoutingPartitionCertificate`
    (PR #74, kernel-clean) — no duplicate logic, no new surface area.

    Returns `Bool` matching the routing-partition signature (per
    reviewer round 3 Q2). Per-leaf diagnostics are available
    separately via `checkRoutingPartitionCertificate_accepts_slot`
    (PR #74) if needed; not exposed here. -/
def checkBoundedCertificateTree (t : CoverageTree)
    (tree : BoundedInputCertificateTree t) : Bool :=
  checkRoutingPartitionCertificate t tree.certData

end CollatzResearch
