# Agent runtime contract

This contract governs OpenClaw/MiniMax execution around this repository. It is
versioned because a worker's local state is not proof of work and must never
override Git, CI, or Lean evidence.

## Workspace boundary

The external project workspace has this layout:

```text
projects/collatz-research/
├── state/                         # mutable execution cache
├── scripts/
└── repo/                          # Git checkout; sole source-edit root
```

At packet open, resolve and record all three values:

```sh
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(git -C "$PROJECT_ROOT/repo" rev-parse --show-toplevel)"
HEAD_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
test "$REPO_ROOT" = "$PROJECT_ROOT/repo"
git -C "$REPO_ROOT" diff --quiet
```

Do not run repository commands from `PROJECT_ROOT`; do not edit source outside
`REPO_ROOT`. A missing, stale, or dirty checkout makes a checkpoint unusable.

## Authority and trust

- Git commits, tracked documentation, GitHub Actions logs, and Lean output are
  durable evidence.
- `state/checkpoints.json` and `state/merged.json` are convenience caches,
  never source-of-truth proof.
- Chat messages are progress deltas only. They cannot replace a checkpoint or
  validation log.
- Python, MiniMax, OpenClaw, and generated certificates are untrusted
  producers. Lean establishes formal results only when the relevant target
  builds without a new admission.

## Checkpoint schema and reuse

`checkpoints.json` must be schema-versioned. A `passed` entry is reusable only
when every identity field matches exactly:

```json
{
  "schema_version": 2,
  "packet_id": "07c-3:orbit-routing-tests",
  "repo_head": "<full 40-character SHA>",
  "branch": "<branch name>",
  "worktree_clean": true,
  "command": ["lake", "build", "CollatzResearch.CoverageTreeOrbitTests"],
  "toolchain_digest": "<sha256 of lean-toolchain + lake-manifest.json>",
  "python_lock_digest": "<sha256 of uv.lock, when applicable>",
  "status": "passed",
  "finished_at": "<UTC ISO-8601>",
  "evidence": {"exit_code": 0, "log_path": "..."}
}
```

Short SHAs, command slugs, and packet IDs are display labels only; none may be
used as a cache key. Treat an entry as **stale** and rerun when the full SHA,
branch, worktree cleanliness, exact argv, dependency digest, toolchain digest,
or required artifact digest differs.

Never reuse a passed checkpoint when CI for that SHA is pending, failed, or
cancelled. Never treat a failed checkpoint as completion.

## Failure recovery

For every failed command, persist `failed` with the exact argv, exit code,
timestamp, and a bounded error excerpt. Before retrying, the worker must state
one changed input: source, command, environment, dependency state, or external
CI state. Retrying identical inputs is prohibited.

After two distinct unsuccessful repairs, stop mutation and create a concise
escalation packet containing the failing command, full SHA, relevant log path,
attempts, and the smallest suspected cause. This prevents token-loop failure
without suppressing legitimate debugging.

### No-content assistant-turn failure

`assistant turn failed before producing content` is a controller/provider
failure, not a MiniMax decision, tool result, or packet outcome. It must never
mark a packet `passed`, `failed`, or `blocked`, consume a repair attempt, or
terminate the workflow by itself.

On this error the controller must write a transport diagnostic containing UTC
time, provider/model, request or trace ID, HTTP status/error payload when
available, packet ID, full repository SHA, tool-call count, and serialized
turn-packet byte size. Do not write prompts, secrets, or certificate contents
to this diagnostic.

Retry the same turn at most twice with exponential delays of 2 and 8 seconds.
If both retries fail, create a `transport_blocked` record and restart the
assistant session with a compact packet. A new session may make one final
attempt; then escalate to the operator with the diagnostic. Transport retries
are distinct from source-repair attempts.

The compact packet contains only the objective, repository-relative paths,
full SHA, acceptance commands, prior error summary, and the relevant
checkpoint record. Never inject all of `GUARDS.md`, `checkpoints.json`,
`merged.json`, CI logs, or chat history into every turn. The controller reads
and validates those files locally, then supplies a bounded summary (target:
under 12 KiB / roughly 3,000 tokens). The assistant requests one named source
or log excerpt at a time when more evidence is necessary.

If no-content failures correlate with a packet size, a particular tool schema,
or an oversized tool result, split the packet before another model attempt.
The controller must preserve the original packet ID and evidence so the split
does not duplicate Git mutations, PR comments, or validation records.

## Packet discipline

1. Read guards, current Git status, current full SHA, and relevant checkpoints.
2. State the single packet objective and its acceptance commands.
3. Add BDD tests first when behavior changes. Record their expected failure
   before implementation; do not weaken them to make an implementation pass.
4. Make one coherent change set, then run the acceptance commands.
5. Record evidence atomically only after the command exits.
6. Send one progress update per packet. The update may summarize several local
   commands; the single-send rule must not prevent validation or recovery.

The token guard may stop speculative exploration, but it must not mark a
packet passed. It instead writes `blocked` with the outstanding evidence.

## Repository CI baseline

- Pull requests: Python CI and Lean CI are required when their path filters
  match.
- Lean CI explicitly builds the changed target in addition to package setup.
- Nightly and reproducibility workflows use hosted Ubuntu runners; no workflow
  may require `/data/.elan` or another machine-local path.
- CI results are evaluated at the reviewed full head SHA, not by workflow name
  or a prior green run.

## Reviewer gate

Codex review verifies the exact head SHA, BDD test-first evidence, scoped
diff, targeted Lean build, Python tests, CI state, theorem-status wording, and
the absence of newly admitted proof obligations in a completed-proof story.
