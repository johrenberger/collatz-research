/**
 * OpenClaw runtime adapter for the repository's durable lifecycle ledger.
 *
 * This module deliberately stores no workflow state in OpenClaw memory.  The
 * Python ledger is authoritative across Gateway restarts and provider aborts.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { definePluginEntry } from "openclaw/plugin-sdk/plugin-entry";

const turnIds = new Map();
const operationKeys = new Map();

function digest(value) {
  return createHash("sha256").update(value).digest("hex").slice(0, 24);
}

function valueOr(value, fallback) {
  return value === undefined || value === null || value === "" ? fallback : value;
}

function pluginConfig(event, context) {
  const config = event?.context?.pluginConfig ?? context?.pluginConfig;
  if (!config || typeof config !== "object") {
    throw new Error("plugin configuration was not provided by the OpenClaw hook event");
  }
  return config;
}

function identifiers(event, context, config) {
  const session = valueOr(context?.sessionKey, context?.sessionId ?? "unknown-session");
  const run = valueOr(event?.runId, context?.runId ?? `prompt-${digest(String(event?.prompt ?? ""))}`);
  const packet = `${valueOr(config.packetPrefix, "openclaw")}:${session}`;
  return { packet, run: String(run) };
}

function lifecycle(config, args) {
  const repoPath = config.repoPath;
  const stateDir = config.stateDir;
  const script = join(repoPath ?? "", "scripts", "agent_lifecycle.py");
  if (!repoPath || !stateDir || !existsSync(script)) {
    throw new Error("collatz-lifecycle: repoPath, stateDir, and scripts/agent_lifecycle.py are required");
  }
  const result = spawnSync(valueOr(config.pythonCommand, "python3"), [
    script,
    "--repo-path",
    repoPath,
    "--state-dir",
    stateDir,
    ...args,
  ], { encoding: "utf8", timeout: 10_000 });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(result.stderr.trim() || "lifecycle command failed");
  return JSON.parse(result.stdout);
}

function block(reason) {
  return { block: true, blockReason: `collatz-lifecycle: ${reason}` };
}

function enforce(config) {
  return config?.enforcementMode === "enforce";
}

function report(scope, error) {
  console.warn(`[collatz-lifecycle] ${scope}: ${error instanceof Error ? error.message : String(error)}`);
}

export default definePluginEntry({
  id: "collatz-lifecycle",
  name: "Collatz lifecycle controller",
  description: "Enforces durable receipts and bounded agent execution.",
  register(api) {
    api.on("before_agent_run", async (event, context) => {
      let config;
      try {
        config = pluginConfig(event, context);
        const { packet, run } = identifiers(event, context, config);
        const payload = JSON.stringify({
          source: "openclaw",
          session: context.sessionKey ?? null,
          prompt_digest: digest(String(event.prompt ?? "")),
        });
        const started = lifecycle(config, [
          "begin", "--packet-id", packet, "--turn-id", run, "--payload-json", payload,
          "--max-model-attempts", String(valueOr(config.maxModelAttempts, 3)),
          "--max-tool-calls", String(valueOr(config.maxToolCalls, 20)),
          "--max-seconds", String(valueOr(config.maxSeconds, 900)),
        ]);
        if (!["started", "already_started"].includes(started.decision)) {
          return { outcome: "block", reason: "lifecycle-start", message: "Lifecycle start was rejected." };
        }
        const budget = lifecycle(config, ["consume", "--turn-id", run, "--kind", "model"]);
        if (budget.decision === "blocked") {
          return { outcome: "block", reason: "model-budget", message: "Packet model budget is exhausted." };
        }
        turnIds.set(run, { packet, run });
        return { outcome: "pass" };
      } catch (error) {
        report("before_agent_run", error);
        if (!enforce(config)) return { outcome: "pass" };
        return { outcome: "block", reason: "lifecycle-error", message: "Lifecycle controller unavailable; run blocked." };
      }
    }, { priority: 100, timeoutMs: 10_000 });

    api.on("before_tool_call", async (event, context) => {
      let config;
      try {
        config = pluginConfig(event, context);
        const { run } = identifiers(event, context, config);
        const budget = lifecycle(config, ["consume", "--turn-id", run, "--kind", "tool"]);
        if (budget.decision === "blocked") return block("tool budget is exhausted");
        const target = String(event.toolName ?? "unknown-tool");
        if (!new Set(config.receiptToolNames ?? []).has(target)) return undefined;
        const intent = lifecycle(config, [
          "begin-operation", "--turn-id", run, "--step-id", String(event.toolCallId ?? target),
          "--operation-kind", "openclaw-tool", "--target", target,
          "--input-json", JSON.stringify(event.params ?? {}),
        ]);
        if (intent.decision === "duplicate") return block("duplicate tool operation requires receipt review");
        operationKeys.set(String(event.toolCallId ?? `${run}:${target}`), { run, key: intent.operation_key });
        return undefined;
      } catch (error) {
        report("before_tool_call", error);
        if (!enforce(config)) return undefined;
        return block("ledger unavailable or turn was not admitted");
      }
    }, { priority: 100, timeoutMs: 10_000 });

    api.on("after_tool_call", async (event, context) => {
      let receiptKey;
      try {
        const config = pluginConfig(event, context);
        const { run } = identifiers(event, context, config);
        receiptKey = String(event.toolCallId ?? `${run}:${event.toolName ?? "unknown-tool"}`);
        const stored = operationKeys.get(receiptKey);
        if (!stored) return;
        lifecycle(config, [
          "finish-operation", "--turn-id", stored.run, "--operation-key", stored.key,
          "--status", event.isError ? "failed" : "succeeded",
          "--result-json", JSON.stringify({ is_error: Boolean(event.isError) }),
        ]);
      } finally {
        if (receiptKey) operationKeys.delete(receiptKey);
      }
    }, { priority: 100, timeoutMs: 10_000 });

    api.on("agent_end", async (event, context) => {
      let run;
      try {
        const config = pluginConfig(event, context);
        ({ run } = identifiers(event, context, config));
        if (!turnIds.has(run)) return;
        lifecycle(config, [
          "finish", "--turn-id", run,
          "--status", event.isError ? "transport_blocked" : "passed",
          "--evidence-json", JSON.stringify({ source: "openclaw-agent-end", is_error: Boolean(event.isError) }),
        ]);
      } finally {
        if (run) turnIds.delete(run);
      }
    }, { priority: 100, timeoutMs: 10_000 });
  },
});
