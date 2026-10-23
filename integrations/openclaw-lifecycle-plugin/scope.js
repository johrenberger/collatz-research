/**
 * Workspace scoping for the durable lifecycle ledger.
 *
 * This module is registered globally but governs exactly one project, so every
 * hook must first confirm that the turn belongs to the configured repository.
 * It deliberately imports nothing from the OpenClaw SDK so the trust boundary
 * stays directly testable.
 */
import { realpathSync } from "node:fs";

/** Resolve a path to its canonical form, or undefined when it cannot be read. */
export function canonicalPath(value) {
  if (typeof value !== "string" || value === "") return undefined;
  try {
    return realpathSync(value);
  } catch {
    return undefined;
  }
}

/**
 * Report whether this turn's workspace is the governed repository.
 *
 * Paths are compared after symlink resolution and must be equal, so a prefix
 * sibling such as `<repo>-sandbox` never inherits the ledger's budgets. A turn
 * that reports no workspace is treated as out of scope rather than trusted.
 *
 * @param context hook context; only `workspaceDir` is consulted
 * @param config plugin config; only `repoPath` is consulted
 * @param onMissingWorkspace called once per process when no workspace is present
 */
export function inScope(context, config, onMissingWorkspace) {
  const workspaceDir = context?.workspaceDir;
  if (typeof workspaceDir !== "string" || workspaceDir === "") {
    onMissingWorkspace?.();
    return false;
  }
  const repo = canonicalPath(config?.repoPath);
  const workspace = canonicalPath(workspaceDir);
  return repo !== undefined && workspace !== undefined && repo === workspace;
}
