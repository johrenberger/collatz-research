# Independent Codex PR review gate

This protocol makes independent Codex review a required quality gate for every
implementation PR. It preserves the maintainer's sole authority to merge.

## Scope and evidence

The gate applies after a PR has a committed, pushed head and the PR evidence
records its validation state. The controller records, in the PR template:

- the full reviewed head SHA;
- review round and review URL;
- verdict (`approved`, `changes requested`, or `escalated`); and
- each P0/P1 finding with its evidence-backed disposition.

A review only approves the exact recorded SHA. A subsequent push invalidates
the approval and begins a new round.

## States

```text
IMPLEMENTING
  -> AWAITING_CODEX_REVIEW
  -> CODEX_CHANGES_REQUESTED -> REMEDIATING -> AWAITING_CODEX_REVIEW
  -> CODEX_APPROVED -> HUMAN_MERGE_READY -> MERGED
                         \
                          -> ESCALATED
```

`HUMAN_MERGE_READY` requires a current-head Codex approval, required CI green
at that same SHA, and no unresolved P0/P1 finding. It is not merge authority.

## Controller procedure

1. Open or update the PR as a draft and record validation evidence for its
   exact head SHA.
2. Request independent Codex review and set the PR state to
   `AWAITING_CODEX_REVIEW`. The request must identify the story, acceptance
   criteria, trust-boundary changes, known limitations, validation evidence,
   and the head SHA.
3. Fetch submitted reviews and inline threads. Ignore a review of any SHA
   other than the current head for merge-gate purposes.
4. Classify findings:
   - **P0:** block merge; stop the current approach and perform structural
     reassessment before any edit.
   - **P1:** block merge; form a falsifiable remediation hypothesis, make the
     bounded change, and validate it.
   - **P2:** resolve when inexpensive; otherwise only a maintainer may defer
     it, with a linked follow-up issue and a scope rationale.
   - **architecture or mathematical decision:** stop edits and request a
     maintainer decision; do not turn the review into a speculative repair
     loop.
5. Post evidence-backed responses, resolve only addressed review threads, and
   push the remediation. This creates a new head and therefore a new review
   round.
6. Repeat until `CODEX_APPROVED`, then request human merge authorization.

## Bounded remediation

Allow at most three remediation-review rounds for one PR. Do not repeat a
rejected strategy. On the third unresolved round, a P0, or a requested
architecture/mathematical decision, create the project diagnostic and escalate
with the reviewed SHAs, review URLs, findings, hypotheses, validation output,
and last-green commit.

## Automation boundary

OpenClaw can collect GitHub reviews, classify them, maintain the PR evidence,
and perform bounded remediation. The Codex invocation must be performed by an
authorized review integration that posts a review to the PR.

Until that integration is configured, a maintainer triggers Codex manually and
the controller begins at review collection. Do not represent this fallback as
automatic review. Once configured, the integration must trigger on PR creation
and after every remediation push, and it must post a review tied to the head
SHA. The integration identity and trigger mechanism belong in deployment
configuration, not repository source or chat transcripts.

## Review checklist

Codex reviews the exact diff and head SHA for:

- story scope, acceptance criteria, and claim language;
- Lean theorem premises, proof debt, and no new unapproved admissions;
- trust-boundary, parser/checker, and external-producer assumptions;
- BDD coverage and relevant Python/Lean targets;
- CI evidence at the reviewed SHA; and
- completeness of PR evidence and follow-up handling.
