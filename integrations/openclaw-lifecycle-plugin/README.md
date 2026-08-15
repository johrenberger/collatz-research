# Collatz OpenClaw lifecycle plugin

This is a native OpenClaw plugin for the canonical repository checkout. It is
the runtime controller for `scripts/agent_lifecycle.py`:

- `before_agent_run` opens or resumes a durable turn and consumes one model
  attempt before MiniMax receives the prompt;
- `before_tool_call` consumes the tool budget and records an operation intent;
- `after_tool_call` records the operation result; and
- `agent_end` records a terminal outcome when the host emits it.

The plugin never places the ledger or guard files into prompt context. OpenClaw
run IDs are turn IDs; the packet ID is a stable `<packetPrefix>:<sessionKey>`.
A retransmitted turn therefore returns `already_started` rather than repeating
the controller's setup, while a repeated tool call is blocked pending receipt
review.

## Install locally

The plugin is intentionally source-loadable for the project workspace:

```bash
openclaw plugins install ./integrations/openclaw-lifecycle-plugin --link
openclaw plugins enable collatz-lifecycle
```

Set the following in the OpenClaw configuration. `repoPath` is the canonical
Git checkout and `stateDir` is a writable persistent directory outside it.

```json
{
  "plugins": {
    "entries": {
      "collatz-lifecycle": {
        "enabled": true,
        "hooks": { "allowConversationAccess": true },
        "config": {
          "repoPath": "/absolute/path/projects/collatz-research",
          "stateDir": "/absolute/path/openclaw-state/collatz-research",
          "pythonCommand": "python3",
          "packetPrefix": "collatz",
          "maxModelAttempts": 3,
          "maxToolCalls": 20,
          "maxSeconds": 900,
          "enforcementMode": "observe",
          "receiptToolNames": []
        }
      }
    }
  }
}
```

Start in `observe` mode. It preserves chat availability while logging controller
failures. Switch to `enforce` only after the host smoke tests below pass.
Add only known mutation-capable tool names to `receiptToolNames`; ordinary
read-only tool calls deliberately receive budgets but no external-effect receipt.

On Windows, use an absolute Windows `repoPath` and set `pythonCommand` to
the interpreter executable OpenClaw can invoke (for example `py` only when its
argument handling is known to work; an explicit `python.exe` is safer).

Validate after installation:

```bash
openclaw plugins inspect collatz-lifecycle --runtime --json
openclaw plugins doctor
```

`agent_end` is an observation hook. If an embedded non-Codex harness does not
emit it, the retained turn remains resumable and `resume` is the safe recovery
path; the plugin never guesses completion after an aborted provider call.

The plugin obtains its resolved configuration from the typed hook event context.
After changing a plugin configuration value, restart Gateway before testing a
chat turn; source inspection alone does not prove that the active Gateway has
loaded the change.
