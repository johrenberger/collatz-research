---
name: formal-math-pr-review
description: "Run the bounded independent-review and remediation gate for a collatz-research feature PR."
---

# Formal Math PR Review

Use only after a feature PR has a pushed head. Read
`formal-math-working-state` and `formal-math-bounds` first. Keep all review
context typed: PR number, exact head SHA, validation status, finding severity,
and disposition. Raw diffs, thread dumps, and reviewer prose belong in the
review artifact, not the controller prompt.

## One review round

1. Verify/open the PR and record its exact head SHA, story, acceptance
   criteria, trust-boundary changes, validation evidence, and limitations.
2. Fetch PR comments, CI status, and the last diff in parallel when they are
   independent.
3. Dispatch one isolated read-only `code_review` leaf. Its budget is at most
   12,000 tokens and 600 seconds; its return is a typed verdict and findings.
4. Record the round in `pr_review_round`, checkpoint the working state, and
   compare the reviewed SHA to the current SHA. A review of another SHA is not
   gate evidence.

The reviewer may inspect and comment but must not edit, push, resolve threads,
or merge. Use a model route different from the implementation session when one
is available. If the requested route is unavailable, stop at `HUMAN_GATE`;
never substitute an unbounded continuation.

## Findings and transitions

- **Approve with no P0/P1:** require green CI for that same SHA, all P2s
  resolved or maintainer-deferred with a linked follow-up, and a valid
  termination check; then transition to `HUMAN_MERGE_READY`.
- **P0, architecture/mathematical decision, dispatch failure, or budget
  violation:** transition to `HUMAN_GATE` without autonomous repair.
- **P1:** write a falsifiable repair hypothesis, make one bounded change,
  validate it, push it, and start a new round for the new SHA.
- **P2:** fix when inexpensive; otherwise only a maintainer may defer it.

At most two review rounds are permitted. Any unresolved third round is
`HUMAN_GATE`, with the reviewed SHAs, typed findings, hypotheses, validation
records, and last-green commit.

## Validation scope

For P1 remediation run the narrowest meaningful gate first; require the full
CI gate before `HUMAN_MERGE_READY`. A P2-only documentation disposition does
not require a re-review if no code is pushed. Do not report a PR ready when CI
is unknown, a current-head review is absent, or a P0/P1 remains.
