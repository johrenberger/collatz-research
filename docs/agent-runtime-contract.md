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
The detailed PR protocol is [`codex-pr-review-gate.md`](codex-pr-review-gate.md).

A review approval is valid only for its recorded full head SHA. Any push starts
a new review round. P0/P1 findings block merge; P2 findings require either a
fix or maintainer-approved deferral with a follow-up. After three remediation
rounds, or on an architecture/mathematical decision, stop editing and escalate
with the complete review record. Codex is independent review, never automatic
merge authority.

The implementation session sends an internal handoff after a successful PR
create or update receipt. Its idempotency key includes repository, PR number,
full head SHA, and review round. The isolated Codex reviewer returns a durable
review receipt and posts using the connected maintainer GitHub identity; the
review body records the reviewer model and SHA so identity and provenance stay
separate.
