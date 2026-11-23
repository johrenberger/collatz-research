---
name: formal-math-restore-green
description: "Recover a failed experiment to the last safe checkpoint while preserving unrelated valid user work."
---

# Formal Math Engineering — RESTORE_GREEN State

> Agent-driven. Use when the `formal-math-engineering` profile is active and the controller has determined that the current experiment should be rolled back to a known-good state.

RESTORE_GREEN recovers the current failed experiment to the last safe checkpoint. Preserves unrelated user work.

> **Effect labels for git operations:**
>
> | step | label |
> |---|---|
> | `git checkout <sha> -- <files>` | `deterministic` (revert path known up-front) |
> | `git revert <sha>` | `deterministic` |
> | `git stash` / `git stash pop` | `deterministic` |
> | `git reset --hard` / `git clean -fd` | **`op_LLM` with `trust_boundary_change=true` and an explicit ADR/human approval artifact id in `working_state`** |
>
> All routing goes through `formal-math-effect-dispatch`. The dispatcher refuses destructive resets absent the required approval artifact.

## Required Steps

```text
1. capture diff (current state vs. last-green)
2. save diagnostic artifact
3. preserve useful commits already known to be valid
4. restore the current failed experiment to the last safe checkpoint when appropriate
5. do NOT destroy unrelated valid work
```

## Safe Git Operations

Use safe Git operations. **Never** perform destructive reset operations across unrelated user work.

```text
- `git checkout <last-green-commit> -- <failed-files>`  (selective revert; preserves unrelated)
- `git revert <failed-commit>`  (creates a new commit undoing the failure; safest)
- `git stash` / `git stash pop`  (preserves both states)
```

**Do NOT use** `git reset --hard` or `git clean -fd` without first committing the last-known-good state to a safe branch.

## Preserving Unrelated Work

The repository may have parallel work packets, branches, or uncommitted changes that are NOT part of the failed experiment. RESTORE_GREEN must:

1. Identify which files are part of the failed experiment.
2. Only revert those files.
3. Leave all other files untouched.

## Trust-Boundary Preservation

If the failed experiment touched any trust-boundary (FFI, native code, external verifier, generated certificate), RESTORE_GREEN must also:

1. Verify the trust boundary is restored to its baseline state.
2. Update or revert any related ADRs.
3. Do NOT introduce a new trust-boundary state without explicit approval.

## Transitions

RESTORE_GREEN changes source state, not experiment history. Preserve append-only dispatch/failure records, cumulative RCS, the story budget, and per-strategy attempt history. Context recovery and rollback must not reset them.

After RESTORE_GREEN completes:
- If restoration succeeded and the failure was resolved → transition to `VALIDATE` (re-run validation) or `STORY_COMPLETE?` if the story is done.
- If restoration succeeded but a decision is still needed → transition to `HUMAN_GATE` (escalate).
- If restoration failed (e.g., merge conflict, unrelated work tangled) → transition to `SAVE_DIAGNOSTIC` then `HUMAN_GATE`.

## Working State Contract (Stage 2)

| action | field | type |
|---|---|---|
| write | `current_state` | `"RESTORE_GREEN"` |
| write | `current_sub_state` | `selective_revert \| git_revert \| stash \| hard_reset_adr` |
| write | `last_green_commit` | str (set to the restored commit) |
| write | `current_head_sha` | str |
| write | `state_updated_at` | iso8601 |
| write | `current_hypothesis_json` | `null` (cleared on rollback) |
| preserve | `current_strategy_id`, `current_strategy_attempt_count` | Keep the current attempt identity/count until a new strategy is explicitly selected.
| preserve | `current_rcs` | Restore source files only; never refund cumulative repair cost. Recompute from append-only history if the cache is stale. |
| checkpoint (χ) on exit | — | — |
| read | `last_green_commit`, `branch` | str |
