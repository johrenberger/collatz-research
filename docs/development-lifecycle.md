# Development lifecycle: reliable agent execution

This process exists to make OpenClaw/MiniMax work resumable, reviewable, and
safe under aborted turns. It supersedes informal guard rules that rely on chat
context or a short SHA alone.

## Non-negotiable invariants

1. **Exactly once for external effects.** A Git commit, push, PR comment,
   checkpoint write, or message has a durable operation receipt before it is
   attempted and an idempotency key after it is attempted.
2. **A turn is not the unit of progress.** A packet has durable steps and can
   restart at the next receipt after any provider abort. There is no attempt to
   resume model sampling mid-turn.
3. **Chat is not state.** The external state ledger and Git are authoritative;
   runtime context is a compact rendering of one packet only.
4. **Red tests are historical evidence, not mergeable output.** A test-first
   commit must be visible in the implementation PR history, but the PR's final
   head must build all added test targets and pass its required CI checks.
5. **Formal status is evidence-led.** A green build with `sorry` is compilation
   evidence, not a completed theorem.

## Workspace and commands

The canonical deployment has one Git checkout and an external mutable state
directory. Do not put lifecycle state in the checkout, where it can pollute Git
status or disappear when the checkout is replaced:

```text
REPO_PATH/                         # canonical Git checkout
├── scripts/agent_lifecycle.py
└── integrations/openclaw-lifecycle-plugin/

STATE_DIR/                         # persistent, writable, outside Git
└── turn-ledger.json
```

All new lifecycle commands take `REPO_PATH` and `STATE_DIR` explicitly. A
packet starts with a full Git SHA and a clean-worktree check:

```bash
python "$REPO_PATH/scripts/agent_lifecycle.py" \
  --repo-path "$REPO_PATH" --state-dir "$STATE_DIR" begin \
  --packet-id 07c-4-orbit-routing --turn-id "$RUNTIME_TURN_ID" \
  --payload-json '{"objective":"implement routing theorem"}' \
  --max-model-attempts 3 --max-tool-calls 20 --max-seconds 900
```

If `begin` returns `already_started`, the controller must call `resume` and
continue from the returned operation receipts; it must not repeat a send or
edit. Before a mutation, create an intent:

```bash
python "$REPO_PATH/scripts/agent_lifecycle.py" \
  --repo-path "$REPO_PATH" --state-dir "$STATE_DIR" \
  begin-operation --turn-id "$RUNTIME_TURN_ID" --step-id post-review \
  --operation-kind github-comment --target pull/23 \
  --input-json '{"body_digest":"..."}'
```

Only `execute_once` authorizes the mutation. A returned `duplicate` requires a
read-after-write check against the target; an unfinished `intent` after an
abort is an uncertainty state, never permission to repeat the mutation.

## Context and abort recovery

The controller must inject no more than one compact packet: objective, full
SHA, branch, paths, acceptance commands, budget, one relevant checkpoint, and
the next unfinished step. It must not inject full guard files, all checkpoints,
merged history, or prior chat transcript.

On `assistant turn failed before producing content`:

1. classify the error and validate the provider-visible transcript;
2. archive/reset a corrupt transcript automatically before a retry;
3. retain the packet and operation receipts;
4. start a fresh assistant session with only the compact packet;
5. block with diagnostics if authentication/configuration fails or retries are
   exhausted.

The MiniMax M3 API-key path is `minimax/MiniMax-M3` through the native
Anthropic-messages adapter with reasoning enabled. Do not route it through an
OpenAI-completions compatibility adapter or inherit `thinking: false`.

## OpenClaw runtime enforcement

Install `integrations/openclaw-lifecycle-plugin` from the canonical checkout
into the OpenClaw host. It is
the controller wrapper for every admitted agent turn: `before_agent_run`
creates/reuses the durable turn and consumes a model attempt before submission;
`before_tool_call` consumes the tool budget and writes an operation intent;
`after_tool_call` stores the result; and `agent_end` records the terminal
outcome. It defaults to **observe** mode: controller failures are logged but do
not interrupt chat. Switch to **enforce** only after the host smoke test and a
read-only tool test pass; then a missing ledger, exhausted budget, or duplicate
external operation fails closed.

The plugin requires `hooks.allowConversationAccess: true` because it uses
`before_agent_run` and `agent_end`, but it does **not** inject conversation
context. See `integrations/openclaw-lifecycle-plugin/README.md` for the exact
configuration and post-install validation. For embedded harnesses that miss
`agent_end`, the durable record intentionally remains resumable; do not infer
success from an absent event.

## Explicit budgets

Budgets are controller inputs, not hidden model limits. Every packet declares:

- maximum model attempts;
- maximum tool calls;
- maximum elapsed time;
- an escalation target.

The lifecycle script persists model/tool consumption and enforces elapsed time
when a controller action occurs. It writes `budget_blocked` with the current
evidence. A budget event never marks work passed.

## Safe Git recovery

Never discard uncommitted agent edits with `git checkout -- .`. Use isolated
worktrees and portable binary patches:

```bash
repo/scripts/packet_patch.sh worktree "$PROJECT_ROOT" 07c-4 agent/07c-4
repo/scripts/packet_patch.sh snapshot "$PROJECT_ROOT" 07c-4
repo/scripts/packet_patch.sh apply "$PROJECT_ROOT" state/patches/07c-4-*.patch
```

`apply` refuses a dirty target worktree and uses `git apply --3way --index`.
If a patch conflicts, preserve it and escalate with the conflict list; do not
overwrite source or reconstruct a large file by blind replacement.

## Lean proof work

Proof work uses an explicit experiment packet: theorem signature, smallest
reproducer, candidate induction principle, and expected elaboration shape.
The stop rule is based on **repeated root cause**, not raw error count:

- stop after two failures with the same motive/eliminator mismatch;
- continue through one local placement/import/syntax failure after fixing it;
- switch to the documented fallback (`CoverageNode.rec` with explicit motive,
  or a custom induction principle) after a repeated proof-shape failure.

Do not merge an admitted proof or an excluded failing Lean test as a
preparatory proof story. The red test commit is retained in PR history; the
final target is green and explicitly invoked by CI.

### Related discipline documents (added 2026-08-19)

- **`docs/lean-api-discipline.md`** — the API-surface **stop-guessing** rule.
  When CI failures come from guessing wrong lemmas / wrong signatures /
  implicit-vs-explicit arguments, this rule applies. Threshold: stop after
  **2 CI failures** on the same surface, take one of the four exit paths
  (playbook / nearby-proven / read source / Codex review). After 3 CI
  failures, the next attempt **must** begin with one of those paths.
  Distinct from the proof-shape stop rule above — see the failure-mode
  classification table in `lean-api-discipline.md` for how to tell them
  apart.
- **`LEAN_PATTERNS.md`** (repo root, PR #40) — vetted Lean patterns P01–P13
  with worked examples. The *positive* companion to `lean-api-discipline.md`.

## CI status without `checks:read`

Use Actions runs by commit SHA as a polling fallback:

```bash
python repo/scripts/ci_status.py --repo johrenberger/collatz-research \
  --sha "$FULL_SHA" --watch
```

This is sufficient for observation when `gh pr checks` is forbidden. For
branch-protection-grade status, install a GitHub App with `Checks: read` and
`Actions: read`; do not infer required checks from a prior green workflow.

## Independent Codex PR review gate

Every implementation PR must complete the review gate in
[`codex-pr-review-gate.md`](codex-pr-review-gate.md) before maintainer merge
authorization. The controller records the reviewed full SHA, review round,
verdict, finding disposition, and review URLs as durable PR evidence.

A push invalidates a prior approval: the controller waits for an independent
review of the new head rather than treating a review of an earlier commit as
approval for the changed code. P0 and P1 findings block merge; P2 findings are
either resolved or explicitly deferred by a maintainer with a follow-up issue.
After three remediation-review rounds, or when a review requests an
architecture or mathematical decision, the controller stops source edits and
escalates with the review record and diagnostics. Codex review never grants
merge authority; a maintainer does.
