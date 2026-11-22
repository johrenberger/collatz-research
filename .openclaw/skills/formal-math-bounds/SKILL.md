---
name: formal-math-bounds
description: "FAOP +B (composite bounds) and +V (verified termination). Owns the story_budget table, the per-leaf and composite bound checks, and the termination certificate. The dispatcher routes every dispatch through this skill before and after running."
---

# Formal Math Engineering — Bounds (+B and +V)

> Companion skill invoked by `formal-math-effect-dispatch` for every dispatch and by the controller at PLAN and at STORY_COMPLETE. Implements FAOP `+B` (declared per-leaf time and cost bounds composed into a story-level cap) and `+V` (verified termination via bounded loops and acyclic call graph).

This skill is the gate. It refuses to dispatch a leaf whose declared `c_max` would push the story over budget. It also owns the termination certificate that says "this story cannot run forever."

## +B — Per-Leaf and Composite Bounds (FAOP Proposition 4)

### Per-Leaf Bound (declared in dispatch_request)

Every action leaf carries:

```yaml
c_max:
  tokens: positive int             # max tokens for this single invocation
  wallclock_seconds: positive int  # max wall-clock for this single invocation
```

The dispatcher enforces per-leaf `c_max` by refusing to launch a leaf whose expected runtime exceeds its `c_max` and by killing the leaf on overrun. Stage 1 already does this for the leaves declared in `formal-math-validate` and `formal-math-pr-review`.

### Story Budget (declared once at PLAN)

A story's `story_budget` row is the cap. It is the *sum* of all leaves the story will run, not the per-leaf cap. Default values:

```yaml
story_budget_defaults:
  max_tokens: 40000             # aggregate cap; raise only with explicit human approval
  max_wallclock_seconds: 1800   # 30 minutes aggregate active work
  max_rounds: 2                 # one review plus at most one remediation re-review
  max_cycles: 8                 # repair cycles; replan or escalate instead of churning
```

A planner may choose tighter bounds in the `plan` work packet. It may raise a
default only with explicit human approval recorded in that plan. The skill
refuses an override that omits a finite token or wall-clock limit or
contradicts the controller's thresholds.

### Composite Bound Formula (FAOP Proposition 4)

For a story with `n` leaves, the composite bound is:

```
composite_tokens      = Σ tokens_actual(i) for dispatched leaves i in this story
composite_wallclock   = Σ wallclock_actual(i) for dispatched leaves i in this story
tokens_remaining      = story_budget.max_tokens      − composite_tokens      (if cap is set)
wallclock_remaining   = story_budget.max_wallclock   − composite_wallclock   (if cap is set)
rounds_used           = count(pr_review_round rows for this story)
cycles_used           = count(repair cycles = current_strategy_attempt_count flips for this story)
```

The dispatcher computes these on every dispatch by querying `dispatch_log` and `pr_review_round` for the story.

### Pre-Dispatch Check (the +B gate)

Before launching a leaf, the dispatcher runs:

```text
1. read story_budget for this story
2. read the leaf's declared c_max
3. compute composite_tokens, composite_wallclock, rounds_used, cycles_used
4. for each bound, check:
     if remaining < declared:    refuse with bound_violation reason
5. if any check fails:
     emit dispatch_log row with ok=0, failure_signature="bound_violation", data={...}
     refuse the dispatch; controller transitions to BUDGET_CHECK → HUMAN_GATE
6. if all checks pass: dispatch
```

The refusal path **never** silently drops the leaf. It is recorded as a `dispatch_log` row so the human sees the exact bound that was hit.

### Worst-Case Planning (FAOP +O)

For a story that has not started, the planner can compute a worst-case composite bound bottom-up:

```
worst_case(leaf)              = leaf.c_max
worst_case(seq(f, g))         = worst_case(f) + worst_case(g)
worst_case(if(p, f, g))       = max(worst_case(f), worst_case(g))
worst_case(loop_n_max(f, p))  = n_max × worst_case(f)
worst_case(call(F'))          = worst_case(F')           # by FNF-3 acyclicity, F' is finite
```

If the bottom-up worst case exceeds the story budget at PLAN time, the planner must reduce scope (smaller work packet) or raise the budget. **A plan that exceeds budget at PLAN time is rejected** — the planner is forced to either bound the work or bound the budget.

## +V — Verified Termination

The controller's state machine has three kinds of loops. Each is bounded and the bound is enforced:

| Loop | Bound | Where enforced |
|---|---|---|
| PR_REVIEW cycle | `max_rounds = 2` (declared in `story_budget`, default 2) | `formal-math-pr-review` increments `pr_review_round`; `HUMAN_GATE` if exceeded |
| Repair cycle (IMPLEMENT → VALIDATE → CLASSIFY_FAILURE → BUDGET_CHECK → IMPLEMENT) | `max_cycles = 8` | `formal-math-budget-check` refuses further IMPLEMENT transitions above threshold |
| Acyclic call graph | implicit | the controller's state diagram is a DAG; FNF-3 forbids recursive `call(id)` |

### Termination Certificate

At DELIVER entry and at PR_REVIEW exit, the controller asks this skill to verify:

```text
verify_termination(story_id) -> TerminationCertificate:
   rounds_used = count(pr_review_round rows for this story)
   cycles_used = current_strategy_attempt_count flips for this story
   rcs = working_state.current_rcs for this story
   bounded = (
       rounds_used <= story_budget.max_rounds
       AND cycles_used <= story_budget.max_cycles
       AND rcs < 32
       AND dispatch_log shows no cycle of states that bypasses BUDGET_CHECK
   )
   return TerminationCertificate{ bounded, rounds_used, cycles_used, rcs, reason? }
```

The certificate is appended to the diagnostic artifact and to the PR review round row.

### The Acyclicity Argument (FNF-3)

`call(id)` in the controller resolves to a registered state, not to a recursive re-entry. The state machine is a DAG:

```
STORY_READY → DISCOVERY → PLAN → BASELINE → IMPLEMENT ⇄ VALIDATE ⇄ CLASSIFY_FAILURE → BUDGET_CHECK
                                                                                       ├→ IMPLEMENT
                                                                                       ├→ SAVE_DIAGNOSTIC → RESTORE_GREEN → CODEX_REVIEW → IMPLEMENT
                                                                                       └→ HUMAN_GATE (terminal)
                                                                                       …
                                                                            STORY_COMPLETE → DELIVER → PR_REVIEW
                                                                                                  ├→ HUMAN_MERGE_READY (terminal)
                                                                                                  ├→ HUMAN_GATE (terminal)
                                                                                                  └→ REVIEW_AGAIN (loop, bounded by max_rounds)
```

The `IMPLEMENT ⇄ VALIDATE ⇄ CLASSIFY_FAILURE` cycle is bounded by `max_cycles` and the RCS thresholds. Every other path is acyclic. So the state machine itself terminates under the budget.

## API

```text
declare_story_budget(story_id, budget: StoryBudget) -> StoryBudget
   -> UPSERT into story_budget
   -> called by PLAN with work-packet-level overrides

get_story_budget(story_id) -> StoryBudget | None
   -> SELECT from story_budget

composite_bound(story_id) -> CompositeBound
   -> SELECT SUM(tokens_used), SUM(wallclock_used) FROM dispatch_log WHERE story_id = ?
   -> SELECT COUNT(*) FROM pr_review_round WHERE story_id = ?
   -> SELECT current_strategy_attempt_count from working_state
   -> returns { tokens_used, wallclock_used, tokens_remaining, wallclock_remaining, rounds_used, cycles_used }

check_dispatch_fits_budget(story_id, leaf_c_max) -> BoundCheck
   -> composite_bound(story_id) + the leaf's declared c_max
   -> returns { ok: bool, reason?: "tokens_exceeded" | "wallclock_exceeded" | "rounds_exceeded" | "cycles_exceeded", would_exceed_by?: int }

record_dispatch_usage(story_id, dispatch_log_row)
   -> no separate write; dispatch_log already records tokens_used
   -> this function is for the caller's benefit (returns the new composite_bound)

worst_case_bound(plan) -> WorstCase
   -> bottom-up fold over the plan tree per FAOP Proposition 4
   -> called by PLAN before declaring a plan acceptable

verify_termination(story_id) -> TerminationCertificate
   -> described above
```

## Persistent Schema (in `formal-math-effect-dispatch/SCHEMA.sql`)

```sql
CREATE TABLE story_budget (
    story_id              TEXT PRIMARY KEY,
    max_tokens            INTEGER,           -- null = no cap
    max_wallclock_seconds INTEGER,           -- null = no cap
    max_rounds            INTEGER NOT NULL DEFAULT 3,
    max_cycles            INTEGER NOT NULL DEFAULT 32,
    declared_at           TEXT NOT NULL,
    updated_at            TEXT NOT NULL,
    notes                 TEXT
);
```

## Refusal Path (the +B enforcement)

When a leaf is refused, the dispatcher MUST:

1. emit a `dispatch_log` row with `ok = 0`, `failure_signature.fingerprint = "bound_violation"`, `data.bound = "tokens|wallclock|rounds|cycles"`, `data.budget_remaining = int`, `data.leaf_c_max = int`
2. return a `dispatch_result` with `ok = false` and the same fields in `data`
3. signal the controller: the next state is `BUDGET_CHECK` (not `IMPLEMENT`)

A bound violation is not a `LOCAL` failure and is not a `STRUCTURAL` failure. It is a **budget failure** that triggers:

- `BUDGET_CHECK` reads the bound violation, classifies as `BOUND_EXHAUSTED` (a new sub-class under budget pressure)
- if the budget was set by the user, escalate to `HUMAN_GATE` with the exact bound
- if the budget was set by a default and the leaf's `c_max` was set by the skill, the planner must shrink the work packet

## Co-Signed Invariant (controller invariant #19)

> **#19 Every dispatch runs the +B composite bound check before launch and the +V termination check at STORY_COMPLETE. A leaf whose declared `c_max` would push the story over `story_budget` is refused with a typed `bound_violation` row in `dispatch_log`; the controller transitions to `BUDGET_CHECK → HUMAN_GATE` (or to a plan revision if the budget was a default). The state machine's termination is asserted at every PR_REVIEW exit via `verify_termination`.**
