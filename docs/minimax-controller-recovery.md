# MiniMax controller recovery integration

This is the implementation companion to `agent-runtime-contract.md`. It
applies to the external OpenClaw project workspace; it is not a claim that the
repository itself controls MiniMax transport.

## Error classification

Classify an attempt as `transport_no_content` when the controller reports
`assistant turn failed before producing content`, an empty assistant response,
or an upstream request failure before a tool call or text response exists.

This classification is distinct from:

- `tool_failure`: a tool returned an error after a model response;
- `task_failure`: the assistant produced a result that fails validation;
- `source_failure`: a command ran and exited nonzero.

Only the latter three may affect source-repair attempts or packet completion.

## Reference controller algorithm

```python
MAX_TRANSPORT_RETRIES = 2
RETRY_DELAYS_SECONDS = (2, 8)
MAX_COMPACT_PACKET_BYTES = 12 * 1024

def run_packet(packet):
    packet = hydrate_and_validate(packet)  # full SHA, clean repo, exact argv
    turn = build_compact_turn(packet, MAX_COMPACT_PACKET_BYTES)

    for attempt in range(MAX_TRANSPORT_RETRIES + 1):
        result = provider.run(turn)
        if result.has_assistant_content:
            return dispatch_assistant_result(packet, result)

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

        if attempt < MAX_TRANSPORT_RETRIES:
            sleep(RETRY_DELAYS_SECONDS[attempt])
            continue

    # No checkpoint transition and no source-repair counter increment here.
    restart_session()
    compact = build_minimal_resume_turn(packet, diagnostic)
    result = provider.run(compact)
    if result.has_assistant_content:
        return dispatch_assistant_result(packet, result)

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

## State transitions

```text
open ── transport_no_content ──> open
open ── command failed ────────> repair_required
open ── acceptance commands pass -> passed
open ── retry budget exhausted -> transport_blocked
```

`transport_no_content` must not create `passed`, `failed`, or `blocked` state
and must not increment the two-attempt source-repair budget.

## Controller BDD acceptance tests

| Given | When | Then |
| --- | --- | --- |
| provider returns no assistant content once | controller runs a valid packet | retry after 2 seconds; packet remains `open`; no repair counter changes |
| provider returns no content three times | controller runs a valid packet | session restarts with compact packet; one final attempt is made |
| restarted session also returns no content | final attempt completes | record `transport_blocked` and notify operator; no Git mutation occurs |
| checkpoint cache is 200 KiB | turn is built | model packet is ≤12 KiB and contains only the relevant record |
| tool returns an error after an assistant tool call | controller handles result | classify as `tool_failure`, not `transport_no_content` |
| same full SHA and exact command passed | a clean packet opens | reuse checkpoint only if toolchain/dependency digests and CI state also match |

Run these tests with a fake provider before enabling the integration. Capture
request IDs and serialized-packet sizes in test assertions, but redact prompt
content and secrets from persisted diagnostics.
