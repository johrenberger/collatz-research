# MiniMax controller recovery integration

This is the implementation companion to `agent-runtime-contract.md`. It
applies to the external OpenClaw project workspace; it is not a claim that the
repository itself controls MiniMax transport.

**Critical rule:** do not blindly retry a no-content turn in the same session.
OpenClaw can persist an orphan or empty assistant message after an aborted turn.
That makes subsequent provider requests structurally invalid and turns retries
into a permanent failure loop.

## Error classification

Classify an attempt as `transport_no_content` when the controller reports
`assistant turn failed before producing content`, an empty assistant response,
or an upstream request failure before a tool call or text response exists.

This classification is distinct from:

- `tool_failure`: a tool returned an error after a model response;
- `task_failure`: the assistant produced a result that fails validation;
- `source_failure`: a command ran and exited nonzero.

Only the latter three may affect source-repair attempts or packet completion.

Classify the provider failure before retrying:

| Class | Examples | Required action |
| --- | --- | --- |
| `session_corrupt` | empty assistant content, orphan error assistant turn, sentinel text, provider 400 schema/message-array error | quarantine the transcript and start a new session; do not replay the old transcript |
| `auth_or_config` | 401, 403, invalid API key, unsupported provider content type | stop the packet as `transport_blocked`; re-authenticate or correct routing before retrying |
| `transient_transport` | timeout, connection reset, 429, 5xx before model output | retry with jitter only after confirming the session is valid and no run is active |
| `tool_failure` | a tool returned an error after a model tool call | retain the session; use normal task recovery |

## MiniMax M3 provider preflight

For the native MiniMax integration, use exactly one matching model reference:

- API key: `minimax/MiniMax-M3`;
- Coding Plan OAuth: `minimax-portal/MiniMax-M3`.

### API-key baseline

For this project, use the API-key provider path. Keep the key in the gateway
secret environment, never in `openclaw.json`, checkpoints, diagnostics, or
repository files:

```json5
{
  env: { MINIMAX_API_KEY: "${MINIMAX_API_KEY}" },
  agents: {
    defaults: {
      model: { primary: "minimax/MiniMax-M3" },
      // Do not set thinking: false for MiniMax M3.
    }
  },
  models: {
    mode: "merge",
    providers: {
      minimax: {
        baseUrl: "https://api.minimax.io/anthropic",
        apiKey: "${MINIMAX_API_KEY}",
        api: "anthropic-messages",
        models: [{ id: "MiniMax-M3", reasoning: true, input: ["text"] }]
      }
    }
  }
}
```

For the China endpoint, replace only the base URL with
`https://api.minimaxi.com/anthropic`; preserve the `minimax` provider ID and
the `anthropic-messages` API type. Do not configure both global and China
endpoints under the same provider ID.

MiniMax M3 is an Anthropic-messages reasoning model. Its adaptive thinking
path must remain enabled: do not inherit a generic `thinking: false` setting
intended for MiniMax M2.x, and do not route M3 through an OpenAI-completions
compatibility adapter. A disabled M3 thinking path can yield no visible model
content and look identical to a transport failure.

At gateway startup and before the first packet after a configuration/model
change, run a read-only preflight and persist only its redacted result:

```text
openclaw --version
openclaw models list --provider minimax
# or, for OAuth:
openclaw models list --provider minimax-portal
```

The controller must verify that the selected provider exposes the exact,
case-sensitive M3 model reference and that the effective model configuration
has reasoning enabled. If this check fails, create `transport_blocked` with
class `auth_or_config`; do not send a work packet, silently fall back to a
different provider, or modify credentials.

## Reference controller algorithm

```python
MAX_TRANSIENT_RETRIES = 2
RETRY_DELAYS_SECONDS = (2, 8)  # add bounded random jitter
MAX_COMPACT_PACKET_BYTES = 12 * 1024

def run_packet(packet):
    packet = hydrate_and_validate(packet)  # full SHA, clean repo, exact argv
    turn = build_compact_turn(packet, MAX_COMPACT_PACKET_BYTES)
    lease = acquire_packet_lease(packet.id)  # one live runner / fencing token

    for attempt in range(MAX_TRANSIENT_RETRIES + 1):
        result = provider.run(turn)
        if result.has_assistant_content:
            return dispatch_assistant_result(packet, result, lease)

        diagnostic = redact({
            "kind": "transport_no_content",
            "packet_id": packet.id,
            "repo_head": packet.full_sha,
            "provider": result.provider,
            "model": result.model,
            "request_id": result.request_id,
            "http_status": result.http_status,
            "tool_call_count": result.tool_call_count,
            "turn_bytes": byte_len(turn),
            "error": result.error_summary,
        })
        append_transport_diagnostic(diagnostic)

        failure_class = classify(result, current_session())
        if failure_class == "session_corrupt":
            archive_session(current_session(), suffix=".jsonl.reset.<utc>")
            turn = build_minimal_resume_turn(packet, diagnostic)
            result = provider.run_in_new_session(turn)
            if result.has_assistant_content:
                return dispatch_assistant_result(packet, result, lease)
            write_packet_status(packet, "transport_blocked", diagnostic)
            notify_operator(packet, diagnostic)
            return

        if failure_class == "auth_or_config":
            write_packet_status(packet, "transport_blocked", diagnostic)
            notify_operator(packet, diagnostic)
            return

        if failure_class == "transient_transport" and attempt < MAX_TRANSIENT_RETRIES:
            assert_session_replayable(current_session())
            assert_lease_current(lease)
            sleep(RETRY_DELAYS_SECONDS[attempt])
            continue

    write_packet_status(packet, "transport_blocked", diagnostic)
    notify_operator(packet, diagnostic)
```

## Compact turn construction

The controller reads `GUARDS.md`, checkpoints, Git status, and CI records
itself. It sends the model only:

```json
{
  "packet_id": "07c-3:orbit-routing-tests",
  "repo_head": "full 40-character SHA",
  "objective": "one sentence",
  "paths": ["repo/Lean/...", "repo/tests/..."],
  "acceptance_commands": ["lake build ...", "uv run pytest ..."],
  "relevant_checkpoint": {"status": "stale", "reason": "head changed"},
  "prior_error": "one redacted line"
}
```

Never concatenate full state JSON, unbounded chat history, complete GitHub
logs, or large tool outputs. A model request for additional evidence must name
one file, command, or bounded log excerpt.

## Transcript preflight and quarantine

Before every provider call, validate the provider-visible transcript:

1. Remove OpenClaw runtime/control messages and prior no-content sentinel
   entries from the replay view.
2. Reject empty assistant content and assistant error entries without a
   preceding user turn.
3. Require a valid user-originated message after transcript normalization.
4. If validation fails, atomically rename—not delete—the session transcript to
   `<session>.jsonl.reset.<UTC timestamp>`, create a fresh session, and resume
   from the compact packet.

The archived transcript is diagnostic evidence. Never automatically append to
or replay it. **Archive and reset are automatic:** no operator confirmation is
required on a detected corruption. Record the original session ID, archive
path, reset timestamp, packet ID, and failure class in the transport
diagnostic. Do not automatically delete archives; apply a separately reviewed
retention policy. The reset must occur before a retry, not after repeated 400s.

## Exactly-once external effects

A fresh session can reissue a model tool call. Every mutating operation must
therefore use an idempotency key of:

```text
packet_id + full_repo_sha + operation_kind + canonical_target + input_digest
```

The controller acquires a lease with a fencing token before a provider run and
checks the token immediately before a mutation. Git commits, pushes, GitHub
review comments, checkpoint writes, and external messages must record this key
and return the prior result on duplicate delivery. Read-only commands need no
idempotency record.

## State transitions

```text
open ── transient transport / valid session ──> open
open ── corrupt transcript ──> session_reset ──> open (one fresh-session attempt)
open ── auth/config failure ──> transport_blocked
open ── command failed ──> repair_required
open ── acceptance commands pass ──> passed
open ── transient retries exhausted ──> transport_blocked
```

`transport_no_content` must not create `passed` or consume the two-attempt
source-repair budget. A corruption, auth, or exhausted transient-retry outcome
becomes `transport_blocked` with diagnostics; it is not a source failure.

## Controller BDD acceptance tests

| Given | When | Then |
| --- | --- | --- |
| provider returns no assistant content once | controller runs a valid packet | retry after 2 seconds; packet remains `open`; no repair counter changes |
| transcript contains an empty/orphan assistant entry | controller performs preflight | archive transcript, create a new session, and send only compact resume state |
| transcript corruption is detected | controller resets automatically | atomic archive exists, diagnostic identifies it, and no operator prompt delays the fresh-session attempt |
| provider returns schema 400 after no content | controller classifies failure | quarantine session before any retry; no old transcript is replayed |
| provider returns 401 or 403 | controller classifies failure | record `transport_blocked`; do not consume retries or change provider silently |
| M3 inherits `thinking: false` or resolves to the wrong provider ID | controller runs startup preflight | block before the packet; diagnostic names the effective model/provider without exposing credentials |
| timeout occurs with a valid transcript | controller retries | retry with bounded jitter while the packet lease is current |
| restarted session repeats a mutation request | controller dispatches it | return prior result by idempotency key; no duplicate commit, comment, or message |
| checkpoint cache is 200 KiB | turn is built | model packet is ≤12 KiB and contains only the relevant record |
| tool returns an error after an assistant tool call | controller handles result | classify as `tool_failure`, not `transport_no_content` |
| same full SHA and exact command passed | a clean packet opens | reuse checkpoint only if toolchain/dependency digests and CI state also match |

Run these tests with a fake provider before enabling the integration. Capture
request IDs and serialized-packet sizes in test assertions, but redact prompt
content and secrets from persisted diagnostics.
