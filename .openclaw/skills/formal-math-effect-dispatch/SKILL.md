---
name: formal-math-effect-dispatch
description: "FAOP-style effect-labeled dispatcher: routes every controller step by effect_label (deterministic | code_review | op_LLM) so only op_LLM steps consume model reasoning context."
---

# Formal Math Engineering — Effect Dispatch (FAOP-style)

> Companion skill invoked by every other companion skill before performing work. Implements FNF-1 (every step declares exactly one mutating effect) and FNF-4 (scope confinement per step) for the formal-math-engineering controller.

The contract below describes the intended EFFECT_DISPATCH behavior. Repository audit found no executable formal-math dispatcher, state store, or composite-budget checker; these statements are requirements, not verified runtime guarantees. The separate `scripts/agent_lifecycle.py` enforces per-turn model/tool/time limits and review handoffs, not formal story budgets or strategy history. Do not claim enforcement until executable code and recovery tests exist.

When implemented, EFFECT_DISPATCH must be the only path through which the formal-math controller runs side effects. It must enforce that:

1. Every primitive action is declared with exactly one `effect_label` from the closed set below.
2. Routing is determined by `effect_label`, not by where the call sits in the agent's reasoning context.
3. Steps labeled `deterministic` or `code_review` **never** consume model reasoning context; their return is a typed record, not a transcript.
4. Steps labeled `op_LLM` are the only ones that may run in the model's reasoning context.

This is Stage 1 of the FAOP-style adoption. LLM bypass (Benefit #7 in Table 5 of arXiv 2610.22061) is achieved by routing non-`op_LLM` leaves out of the model context entirely.

## Closed Effect Vocabulary

Three labels only. Adding a fourth requires an ADR-equivalent change to this skill.

| `effect_label` | What runs | Returns | May use model reasoning context? |
|---|---|---|---|
| `deterministic` | orchestrator `exec` / `read` / `apply_patch` directly on the host. No spawned subagent, no model call. | a typed record (see "Return Schema" below) | **no** |
| `code_review` | spawned isolated subagent with `toolsAllow` restricted to read/inspection. **Never** edit, push, or merge. | a typed record (addressed/unresolved/suggested_changes) | **no** in the parent context; one-shot in the subagent |
| `op_LLM` | runs in model reasoning context (orchestrator or another same-model subagent with full tool access scoped to the leaf). | a typed record | **yes** |

## Required Pre-Dispatch Declaration

Before invoking the dispatcher, the calling skill must declare:

```yaml
dispatch_request:
  effect_label: deterministic | code_review | op_LLM
  primitive: "<one-line description of the work>"
  inputs:                                       # typed
    schema: { ... }                             # fields this primitive reads
  outputs:                                      # typed
    schema: { ... }                             # fields this primitive produces
  trust_boundary_change: bool
  estimated_cost:
    tokens: int
    wallclock_seconds: int
  c_max: { tokens: int, wallclock_seconds: int } # declared budget for this leaf (per FAOP +B)
  scope:
    tools_allow: [...]                          # mandatory for code_review and op_LLM
    tools_deny:  [...]
```

The runtime contract **requires refusal** when a leaf exceeds `c_max` or a trust-boundary change lacks its architecture-decision artifact. A future implementation must also check the composite `story_budget` and return typed bound details. None of these checks is executable in this repository yet.

## Routing Rules

```text
effect_label = "deterministic"
   -> run on host directly via orchestrator's exec / read / apply_patch
   -> capture stdout / file content / exit code into a typed record
   -> no spawned session, no model call

effect_label = "code_review"
   -> sessions_spawn(
        runtime: "subagent",
        model:   "<cheapest viable model>"      # never the same model as the orchestrator
        agentId: "default"
        context: "isolated"
        toolsAllow: <scope.tools_allow>
        toolsDeny:  <scope.tools_deny>
        runTimeoutSeconds: dispatch_request.c_max.wallclock_seconds
        taskName: "<primitive>"
        task: "<typed instructions; one-shot; no follow-ups>"
      )
   -> wait for the typed return record
   -> parent context sees only the record

effect_label = "op_LLM"
   -> run inside the current reasoning context
   -> MUST declare tools_allow / tools_deny even when running locally
   -> record tokens used; refuse to dispatch if previous-cycle c_max already exceeded
```

### Why a different model for `code_review`

The existing controller's invariant #9 ("Codex review is independent, not continuation bias") generalises: any code-review effect must not be performed by the same model that performed the implementation. The current `collatz-pr-review-gate` skill already specifies `openai/gpt-5.6-terra` as the reviewer. The dispatcher respects that. If the reviewer model is unset, the dispatcher fails closed and surfaces a `model_resolution_required` typed record.

## Return Schema (Mandatory Typed Record)

Every dispatch — regardless of `effect_label` — produces **exactly one** typed record of this shape. No transcripts, no diff dumps, no free-form prose:

```yaml
dispatch_result:
  effect_label: deterministic | code_review | op_LLM
  primitive: "<echo of input primitive>"
  parent_state: string | null         # controller state (e.g. PR_REVIEW, IMPLEMENT)
  sub_state: string | null            # the sub-state inside parent (e.g. DISPATCH_REVIEW, RE_VALIDATE)
  ok: bool
  started_at: <iso8601>
  finished_at: <iso8601>
  tokens_used: int | null                     # null for deterministic
  exit_code: int | null
  failure_signature:
    tool: string | null
    category: string | null
    symbol: string | null
    target: string | null
    normalized_message: string | null
  data:
    # shape depends on the primitive; see per-skill declarations
    ...
```

The `parent_state` and `sub_state` fields are required for any dispatch originating from a state that has internal sub-states (currently: `PR_REVIEW`, and `CODEX_REVIEW` once the in-packet reviewer is migrated). They MUST be null only for primitives invoked outside a stateful context (e.g., a one-shot `make ci` during baseline). Grep the log for `parent_state=PR_REVIEW` to filter all PR_REVIEW activity.

The **parent reasoning context** of the controller only ever sees `dispatch_result`. It never sees raw stdout, raw diff text, raw Lean goal output, or chat transcripts from subagents. This is what closes the "context loss" regression: deterministic and code_review outputs are reduced to typed records before they enter the prompt.

## Cost Discipline (FAOP +B lightweight)

Per-leaf declared `c_max` is the single most important number in Stage 1. The target dispatcher must enforce:

```text
1. If estimated_cost.tokens > c_max.tokens                    -> refuse, return ok:false, signature:"budget_exceeded"
2. If previous_cycle of the same primitive exceeded c_max    -> block; transition to BUDGET_CHECK in the controller
3. If running total tokens for the work packet exceed 0.5 * story_budget_for_packet
                                                               -> block; transition to BUDGET_CHECK
```

These map to FAOP Proposition 4 (composite bound) without requiring a SkillBase-style compiler.

## Scope Confinement (FAOP FNF-4)

`code_review` and `op_LLM` MUST declare `tools_allow`. The dispatcher passes `toolsAllow` to the spawned subagent (or refuses the dispatch if running locally without an enforceable tool list). Forbidden tool patterns default-deny:

```text
deterministic:
   tools_allow = implicit (host capabilities)
   scope free — but must not edit_lean / edit_python / push without re-classifying to op_LLM

code_review:
   tools_allow MUST be a subset of {read, browser, exec:[gh, ripgrep], exec:[ls, cat, jq]}
   MUST NOT include: apply_patch, exec:[git commit], exec:[git push], exec:[lean], exec:[make], exec:[lake]

op_LLM:
   tools_allow MUST be declared explicitly per leaf
   trust_boundary_change=true must show an ADR artifact id in working_state
```

## What This Skill Does Not Yet Do (Stage 2+ scope)

- **No typed working state schema yet.** Stage 2 of the FAOP adoption introduces `working_state.schema` and persists it across context resets. Stage 1 only persists `dispatch_result` rows to the runtime state.
- **No auto-parallelization (Law L3).** Independent `deterministic` and `code_review` dispatches remain sequential for now. Stage 5 introduces `par(...)` fan-out via `sessions_spawn` ×N with `context:"fork"`.
- **No +V termination cap enforcement.** Per-leaf `c_max` is declared and enforced, but no provable wall-clock bound yet.
- **No SkillBase-style FAOP compiler.** Dispatch happens at runtime by pattern-matching `effect_label`. The static guarantees FAOP obtains at compile-time we obtain at deploy-time by skill author discipline + runtime refusal.

## Calling Convention (How Other Skills Use This)

Every companion skill that wants to perform an action does:

```text
1. Construct dispatch_request
2. Call dispatch(effect_label, ...)
3. Receive dispatch_result; do NOT inspect intermediate output
4. Branch on ok / failure_signature; transition to next state per controller
```

Example from `formal-math-validate`:

```yaml
# Pseudo-call (illustrates the contract; OpenClaw doesn't have a literal dispatch() tool)
dispatch_result = EFFECT_DISPATCH.dispatch(
    effect_label="deterministic",
    primitive="make_ci",
    inputs={work_packet_id:"WP-06B-D"},
    outputs={exit_code:int, summary:str, regression_set:list[str]},
    estimated_cost={tokens:0, wallclock_seconds:180},
    c_max={tokens:0, wallclock_seconds:240},
)
if not dispatch_result.ok:
    transition_to("CLASSIFY_FAILURE", failure=dispatch_result.failure_signature)
```

## Persistent Runtime State

Append-only `dispatch_log` keyed by `(story_id, work_packet_id, cycle_index)`:

```text
sqlite> CREATE TABLE dispatch_log (
    story_id TEXT,
    work_packet_id TEXT,
    cycle_index INTEGER,
    effect_label TEXT,
    primitive TEXT,
    ok INTEGER,
    tokens_used INTEGER,
    started_at TEXT,
    finished_at TEXT,
    failure_signature TEXT,
    data_json TEXT,
    PRIMARY KEY (story_id, work_packet_id, cycle_index, primitive)
);
```

This makes Stage 1 measurable. **Stage 3** adds the `story_budget` table and the `working_state` table that the bounds skill reads on every dispatch. The full schema lives in `SCHEMA.sql` next to this skill.

## Transition

This skill does not itself transition states. It is invoked from any state that performs an action, and its result drives the controller's normal transitions.

## Required Co-Signed Invariant (added to controller invariant #16)

> **#16 Every primitive action in the controller runs through EFFECT_DISPATCH with a declared effect_label. No action runs directly in the orchestrator's reasoning context without an explicit op_LLM declaration.**
