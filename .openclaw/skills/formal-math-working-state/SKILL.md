---
name: formal-math-working-state
description: "Typed working state for the formal-math-engineering controller. The single source of truth for what the agent has in its head; read on every state entry, written (χ-checkpoint) on every state exit and on every hypothesis change."
---

# Formal Math Engineering — Working State (FAOP χ + FNF-2)

> Companion skill invoked by the controller and by every other companion skill. Owns the typed `working_state` schema and the read / write / checkpoint / restore API. Implements the FAOP `χ` (checkpoint) primitive and the FNF-2 typed-data-flow discipline applied to the agent's working memory.

This is the load-bearing skill for the "context loss" regression. **The agent's working memory is data persisted in SQLite, not prose accumulated in the prompt.** When the model's context is compacted or a new session resumes, the agent reads its working state from the store and continues — without re-deriving assumptions from conversation history.

## Why This Exists (the Failure Mode It Prevents)

The previous failure mode: the agent accumulated its working memory as a side-effect of conversation. When the model's context was cleared or compacted, the agent lost `current_hypothesis`, `last_validation`, `strategy_history`, the in-flight `pr_review_round`, and every other piece of "what am I doing right now." Re-deriving these from a transcript was expensive (token cost) and unreliable (drift between what was true at compaction time and what the agent thinks is true after).

After this skill, none of that state lives in the prompt. The agent reads from the store.

## The Typed Schema

`working_state` is a finite map from typed field names to typed values, exactly as in FAOP Section 2.1. One row per `story_id` in the `working_state` table. Derived data (rejected hypotheses, strategy history, full failure history) is **not** stored here — it is queried from `dispatch_log`, `pr_review_round`, and other append-only tables on read.

```yaml
working_state:
  # identity
  story_id: str                       # PRIMARY KEY
  work_packet_id: str | null          # null before PLAN, then set

  # control
  current_state: str                  # one of the controller states
  current_sub_state: str | null       # sub-state within parent (e.g. DISPATCH_REVIEW)
  state_entered_at: iso8601
  state_updated_at: iso8601
  checkpoint_count: int               # number of explicit χ calls for this story

  # git
  branch: str
  base_commit: str | null             # first commit of branch (set at PLAN)
  last_green_commit: str | null       # updated by BASELINE / RESTORE_GREEN
  current_head_sha: str               # updated at every χ that follows a git mutation

  # repair
  current_hypothesis: RepairHypothesis | null     # the active repair attempt
  current_strategy_id: str | null
  current_strategy_attempt_count: int

  # validation
  last_validation: ValidationResult | null
  last_validation_exit_code: int | null

  # budget
  current_rcs: float                  # Repair Cost Score (per formal-math-budget-check)

  # proof debt
  proof_debt_baseline: int            # sorry/admit count at BASELINE
  proof_debt_current: int             # current count

  # trust
  trust_boundary_baseline: TrustBoundary
  trust_boundary_current: TrustBoundary

  # review (PR_REVIEW state)
  review_feedback: ReviewFeedback | null
```

### Typed Sub-Schemas (the FNF-2 part)

```yaml
RepairHypothesis:
  failure: str
  proposed_root_cause: str
  evidence: list[str]
  proposed_change: list[PatchTarget]
  files_affected: list[str]
  expected_result: str
  falsification_condition: str
  strategy_id: str
  status: "open" | "failed" | "rejected" | "closed"
  attempted_at: iso8601 | null
  result_signature: str | null        # normalized failure_signature.fingerprint after attempt

ValidationResult:
  tool: str                           # "lean" | "pytest" | "make" | "lake" | "other"
  target: str                         # what was validated
  category: str
  symbol: str | null
  normalized_message: str
  ok: bool
  exit_code: int
  raw_output_path: str | null         # path to full output if needed for diagnostic

TrustBoundary:
  pure_lean: bool
  external_process: bool
  ffi: bool
  native_code: bool
  generated_certificate: bool
  cryptographic_library_dependency: bool

ReviewFeedback:
  round: int
  pr_url: str
  head_sha: str
  findings: list[Finding]
  disposition: list[Disposition]
  ok: bool

Finding:
  finding_id: str
  priority: "P0" | "P1" | "P2"
  file: str | null
  line: int | null
  description: str
  suggested_change: str | null

Disposition:
  finding_id: str
  action: "remediated" | "deferred" | "rejected" | "escalated"
  hypothesis_id: str | null
  commit: str | null
  followup_url: str | null
```

The FNF-2 guarantee: a step that reads `working_state.current_hypothesis` is statically guaranteed to find it present (or null with a declared `current_hypothesis | null` type). A step that reads an undeclared field is rejected at the API level.

## The Read / Write / Checkpoint / Restore API

This is the only path through which the agent's working memory is mutated. The controller and every companion skill call these.

```text
write_working_state(story_id, partial: dict)
   -> merges partial into the current row, bumps state_updated_at
   -> does NOT checkpoint (does not increment checkpoint_count)

read_working_state(story_id) -> WorkingState
   -> SELECT one row
   -> enriches with derived data from dispatch_log / pr_review_round
   -> returns typed structure

checkpoint(story_id)
   -> write_working_state + state_entered_at reset + checkpoint_count += 1
   -> emits a "working_state_checkpoint" dispatch_log row (effect_label: deterministic)
   -> this is the χ call

restore_after_compaction(story_id) -> WorkingState
   -> read_working_state + emit "context_recovered" dispatch_log row
   -> returns a "Recovery Manifest" the agent uses to resume
```

### χ-Semantics: When to Checkpoint

A checkpoint (`χ`) is required at:

| Trigger | Who calls it |
|---|---|
| every controller state transition | the controller, on exit from one state and entry to the next |
| every `op_LLM` write of `current_hypothesis` | `formal-math-classify-failure` |
| every successful patch | `formal-math-implement`, after a passing `make ci` |
| every `make ci` result | `formal-math-validate` |
| before any `code_review` dispatch | `formal-math-pr-review` (so the reviewer reads a consistent snapshot) |
| before `HUMAN_GATE` / `HUMAN_MERGE_READY` exit | the controller |
| every K mutations (K = 10) | any companion skill, opportunistic |

A checkpoint is **idempotent** — calling it twice with no intervening writes produces the same row and increments `checkpoint_count` by one. This is by design: a context-compaction-aware runtime that has just restored state will checkpoint to record "I am here now" and the next compaction will see the new `state_entered_at`.

### Recovery After Context Compaction

The agent's first action when it detects a context break (or when it is asked to resume a story) is:

```text
1. read_working_state(story_id)
2. cross-check current_state against controller's allowed states
3. emit a "context_recovered" dispatch_log row (effect_label: deterministic)
4. resume from current_state
```

The "Recovery Manifest" returned by `restore_after_compaction` includes:

```yaml
recovery_manifest:
  story_id: str
  work_packet_id: str | null
  current_state: str
  current_sub_state: str | null
  last_checkpoint_at: iso8601
  last_dispatch_signature: str | null
  current_hypothesis_summary: str | null
  last_validation_summary: str | null
  review_feedback_summary: str | null
  outstanding_p0_or_p1_count: int
  recommended_action: str
```

`outstanding_p0_or_p1_count` is computed by joining `pr_review_round` for the current story. `recommended_action` is one of `continue_implement | re_validate | re_dispatch_review | escalate_to_human_gate`.

## Reading vs. Re-Deriving (the Anti-Pattern This Skill Prevents)

**The agent must NOT do any of:**

- Re-read the conversation transcript to figure out what hypothesis is active. The hypothesis is in `working_state.current_hypothesis`. Read it.
- Re-run `make ci` to know the last validation result. The result is in `working_state.last_validation`. Read it.
- Re-derive "which PR review round are we on" from the message history. The round is in `pr_review_state` (queried by the read API). Read it.
- Keep a "scratch" copy of the current state in the prompt. The store is the source of truth; the prompt is a cache.

**The agent MAY do any of:**

- Reason about what the typed state implies. Reasoning is `op_LLM`; it does not require re-fetching.
- Update the typed state via `write_working_state`. That is the only way to change it.
- Query derived data (full failure history, full PR review history) from append-only tables. The read API does this for you.

## The Persistent API (SQLite)

The dispatcher / runner implements the API as four functions over the `working_state` table defined in `formal-math-effect-dispatch/SCHEMA.sql`:

```sql
-- Schema (defined in SCHEMA.sql)
CREATE TABLE working_state (
    story_id                        TEXT PRIMARY KEY,
    work_packet_id                  TEXT,
    current_state                   TEXT,
    current_sub_state               TEXT,
    state_entered_at                TEXT,
    state_updated_at                TEXT,
    checkpoint_count                INTEGER NOT NULL DEFAULT 0,
    branch                          TEXT,
    base_commit                     TEXT,
    last_green_commit               TEXT,
    current_head_sha                TEXT,
    current_hypothesis_json         TEXT,
    current_strategy_id             TEXT,
    current_strategy_attempt_count  INTEGER NOT NULL DEFAULT 0,
    last_validation_json            TEXT,
    last_validation_exit_code       INTEGER,
    current_rcs                     REAL NOT NULL DEFAULT 0,
    proof_debt_baseline             INTEGER NOT NULL DEFAULT 0,
    proof_debt_current              INTEGER NOT NULL DEFAULT 0,
    trust_boundary_baseline_json    TEXT,
    trust_boundary_current_json     TEXT,
    review_feedback_json            TEXT
);
```

A minimal Python reference implementation:

```python
def read_working_state(story_id):
    row = cur.execute(
        "SELECT * FROM working_state WHERE story_id = ?", (story_id,)
    ).fetchone()
    if row is None:
        return None
    state = dict(zip([c[0] for c in cur.description], row))
    # enrich with derived data
    state["rejected_hypotheses"] = derive_rejected_hypotheses(story_id)
    state["strategy_history"] = derive_strategy_history(story_id)
    state["failure_history"] = derive_failure_history(story_id)
    state["pr_review_round"] = derive_pr_review_round(story_id)
    return state

def checkpoint(story_id):
    write_working_state(story_id, {})
    cur.execute(
        "UPDATE working_state SET state_entered_at = ?, checkpoint_count = checkpoint_count + 1 "
        "WHERE story_id = ?", (iso_now(), story_id)
    )
    con.commit()
    emit_dispatch_log_row(story_id=story_id, effect_label="deterministic",
                          primitive="working_state_checkpoint", ok=1,
                          data={"story_id": story_id, "checkpoint_count": ...})
```

## What This Skill Does Not Do (Stage 3+ scope)

- **No static type checker at compile time.** The FNF-2 guarantee is enforced at runtime by the API refusing undeclared field reads. A full FAOP-style SkillBase compiler is Stage 6.
- **No automatic inference of `current_hypothesis` from prior state.** The companion skill that mutates the hypothesis writes it explicitly.
- **No merge logic across concurrent stories.** Stories are independent; cross-story merge is out of scope.

## Transition

This skill does not itself transition states. It is invoked from any state that needs to read, write, or checkpoint the working state.

## Co-Signed Invariant (controller invariant #18)

> **#18 The agent's working memory is the `working_state` row in `/data/.openclaw/state/openclaw.sqlite`, not the conversation transcript. Every state entry reads `working_state`; every state exit checkpoints (χ). The agent must not re-derive its current hypothesis, last validation, or PR review round from prose; these are typed and persisted.**
