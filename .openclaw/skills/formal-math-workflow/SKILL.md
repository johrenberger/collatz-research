---
name: formal-math-workflow
description: "Route bounded Lean/Python work packets on collatz-research through discovery, validation, finite budgets, and independent review."
---

# Formal Math Engineering Controller

Use for a bounded Lean proof, Python certificate tool, or Lean/Python bridge
work packet in `johrenberger/collatz-research`. Do not use it for ordinary
documentation or repository-administration work.

## Load only what the current state needs

At every state entry, read `formal-math-working-state` for the story. Then
read the named companion skill for that state; do not preload every companion
or its schemas.

| State | Required companion |
|---|---|
| DISCOVERY | `formal-math-discovery` |
| PLAN | `formal-math-plan`, then `formal-math-bounds` |
| BASELINE | `formal-math-baseline` |
| IMPLEMENT | `formal-math-implement` |
| VALIDATE | `formal-math-validate` |
| validation failure | `formal-math-classify-failure`, then `formal-math-budget-check` |
| restore or escalation | `formal-math-restore-green`, `formal-math-diagnostic`, or `formal-math-codex-escalate` |
| DELIVER | no additional companion; use the delivery transition below |
| PR_REVIEW | `formal-math-pr-review` |

Every primitive is dispatched through `formal-math-effect-dispatch` with one
effect label: `deterministic`, `code_review`, or `op_LLM`. Pass typed results
between states; do not paste raw build logs, diffs, review prose, or whole
source files into the controller context.

## State machine

```
DISCOVERY → PLAN → BASELINE → IMPLEMENT → VALIDATE
                                      │ pass
                                      ├→ CHECKPOINT → next packet or DELIVER → PR_REVIEW
                                      │ fail
                                      └→ CLASSIFY_FAILURE → BUDGET_CHECK
                                              ├→ bounded repair → IMPLEMENT
                                              ├→ reassess / diagnostic / independent review
                                              └→ HUMAN_GATE
PR_REVIEW → HUMAN_MERGE_READY | REVIEW_AGAIN | HUMAN_GATE
```

`VALIDATE` may never return directly to `IMPLEMENT`: classify the failure,
record a falsifiable hypothesis, and let the budget check select the next
transition. A failed strategy may be attempted at most twice. At RCS ≥ 12,
stop editing for structural reassessment; at RCS ≥ 24 or after three distinct
proof strategies, create a diagnostic and request independent review. At RCS
≥ 32, hard-stop unless a reviewer supplies a materially new strategy.

## Finite work only

`formal-math-bounds` is authoritative. A story must have finite token and
wall-clock limits before its first dispatch. Defaults are 40,000 aggregate
tokens, 30 minutes active work, two PR-review rounds, and eight repair cycles.
A larger budget requires explicit human approval in the plan. Refuse a leaf
that exceeds its remaining composite budget, record `bound_violation`, and
route to replan or `HUMAN_GATE`.

## Engineering invariants

- Before editing, confirm branch/status, reread the exact target, and check
  for concurrent modification.
- Preserve unrelated work and checkpoint valid progress before escalation.
- Classify Lean failures causally; do not rotate tactics or retry validation
  without a new hypothesis.
- Python can explore or generate evidence but never substitutes for Lean
  proof. New `sorry`/`admit` is prohibited unless explicitly approved.
- Any FFI, native, external-process, or trust-boundary change requires an
  architecture decision before implementation.
- Keep a packet within its accepted files and claim. A new mathematical or
  architectural decision is a human gate, not an autonomous scope expansion.

## Waiting

Dispatch a long-running deterministic command once and use its completion
event or watch handle. One status probe is allowed. If it has no
decision-relevant result, persist the handle, give one concise update, and
yield; do not repoll, reread the same log, or generate another reasoning turn
until completion/failure arrives.

## Resume events

When waiting for a local validation command, register a one-shot `on-exit`
automation that sends the controller a self-contained completion event and
delete it after delivery. When waiting for GitHub CI or a submitted review,
persist `WAIT_CI` or `WAIT_REVIEW` in `working_state` with the repository, PR
number, exact head SHA, and observed status; register a condition watcher that
fires only when that exact SHA's CI or review status changes. The watcher must
include the story id and observed transition in its event, so the controller
can read the checkpoint and resume without conversation history.

Never wake the controller on a fixed cadence merely to poll. A watcher must
deduplicate observations in its persisted trigger state, make no repository
writes, and fire on actionable completion, failure, or head-SHA drift only.
On resume, verify the stored SHA still matches the PR before continuing; a
different SHA returns to `PR_REVIEW` for a new round.

## Completion

A packet completes only after its narrow validation passes and valid progress
is checkpointed. A feature additionally requires clean/committed work,
required Lean/Python gates, no unapproved proof debt, an unchanged or approved
trust boundary, and `PR_REVIEW` approval of the current SHA.

## Delivery transition

After all required validation is green, transition directly to `DELIVER` unless
the accepted plan explicitly says the packet is local-only. `DELIVER` must:

1. recheck the scoped diff and clean unrelated work;
2. create a feature branch from the approved base, commit only the packet, and
   push it;
3. open a draft PR with the exact head SHA, scope, validation evidence,
   limitations, and trust-boundary status; then
4. enter `PR_REVIEW` automatically.

These publication steps are standing delivery authorization for an accepted,
validated packet; do not ask again between validation and PR creation. Never
merge, enable auto-merge, or override review/CI requirements: `HUMAN_MERGE_READY`
is a handoff, never merge authority.
