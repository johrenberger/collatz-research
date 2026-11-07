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
2. Create an internal review handoff and set the PR state to
   `AWAITING_CODEX_REVIEW`. Its idempotency key is
   `codex-pr-review:<repository>:<pr-number>:<head-sha>:<round>` and its
   payload identifies the story, acceptance criteria, trust-boundary changes,
   known limitations, validation evidence, and head SHA.
3. Start an isolated Codex reviewer session from that handoff. It may read the
   PR, diff, CI evidence, and review threads, and may post a review; it must
   not edit source, push, resolve a thread, or merge. Run `one reviewer per
   head SHA`: never start a second reviewer for a SHA that is already under
   review, and never start reviewers in parallel for the same PR. Each
   additional reviewer re-reads the repository and the diff from scratch, and
   that fan-out is the dominant token cost of this gate.
4. Fetch submitted reviews and inline threads. Ignore a review of any SHA
   other than the current head for merge-gate purposes.
5. Classify findings:
   - **P0:** block merge; stop the current approach and perform structural
     reassessment before any edit.
   - **P1:** block merge; form a falsifiable remediation hypothesis, make the
     bounded change, and validate it.
   - **P2:** resolve when inexpensive; otherwise only a maintainer may defer
     it, with a linked follow-up issue and a scope rationale.
   - **architecture or mathematical decision:** stop edits and request a
     maintainer decision; do not turn the review into a speculative repair
     loop.
6. Post evidence-backed responses, resolve only addressed review threads, and
   push the remediation. This creates a new head and therefore a new review
   round.
7. Repeat until `CODEX_APPROVED`, then request human merge authorization.

## Bounded remediation

Allow at most three remediation-review rounds for one PR. Do not repeat a
rejected strategy. On the third unresolved round, a P0, or a requested
architecture/mathematical decision, create the project diagnostic and escalate
with the reviewed SHAs, review URLs, findings, hypotheses, validation output,
and last-green commit.

Each round after the first resumes the same reviewer session rather than
opening a fresh one, and presents it the new head SHA together with its own
prior findings. A fresh reviewer re-reads the repository and the diff from
scratch, so resuming the existing session is what keeps the review rounds
affordable: the round count is not the cost driver, reviewer reuse is. Start a
fresh reviewer only when the previous session cannot be resumed, or when a P0
calls for a genuinely independent second opinion.

## Internal reviewer handoff

The implementation session emits the review handoff immediately after a
successful PR create or update operation. The lifecycle receipt is the source
of truth: a provider abort may not create a duplicate reviewer task.

While it waits, the implementation session waits by event, not by polling.
Each poll is a fresh model turn that re-transmits the whole conversation
context, so a poll loop over a known command costs a full context re-send per
iteration. Probe once; if there is no decision-relevant result, register the
completion event and yield. When a blocking wait is unavoidable, issue one
call that owns its result so the wait completes in a single turn.

The implementation session's operational context is a per-packet working
budget, not a session-lifetime accumulation. At each PR milestone — PR
opened, review round landed, or PR merged — persist the delivery checkpoint
and end that packet's working loop, starting the next packet in a fresh
session restored from the checkpoint. A session that spans several packets
re-sends the accumulated history on every turn, and the resulting
context-limit failure lands on whichever packet happened to be running.

The isolated reviewer returns a durable receipt containing the PR number,
reviewed full SHA, review round, model identity, verdict, finding summary, and
GitHub review URL. The implementation session treats this receipt—not a chat
claim—as the transition from `AWAITING_CODEX_REVIEW` to either
`CODEX_CHANGES_REQUESTED` or `CODEX_APPROVED`.

GitHub posts through the maintainer's connected identity, so the review body
must begin with `Generated by independent OpenClaw Codex review` and include
the model and reviewed SHA. Model identity does not change GitHub authorship.
This arrangement uses no public webhook or inbound gateway exposure.

## Review checklist

Codex reviews the exact diff and head SHA for:

- story scope, acceptance criteria, and claim language;
- Lean theorem premises, proof debt, and no new unapproved admissions;
- trust-boundary, parser/checker, and external-producer assumptions;
- BDD coverage and relevant Python/Lean targets;
- CI evidence at the reviewed SHA; and
- completeness of PR evidence and follow-up handling.
