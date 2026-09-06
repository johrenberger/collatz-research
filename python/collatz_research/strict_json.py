"""Strict JSON decoding for certificate trust boundaries.

This module is the single source of truth for strict JSON decoding in
the project. Every certificate-facing parser **MUST** use these helpers
rather than the permissive stdlib `json.loads`.

Strictness guarantees:

- **Duplicate object keys are rejected.** The stdlib `json.loads` (and
  `json.JSONDecoder` without `object_pairs_hook`) silently retains the
  last occurrence, so two distinct certificate byte streams would parse
  to the same record and digest — fatal for canonical, proof-bearing
  certificates. The custom decoder hook below raises `ValueError` on any
  duplicate (recursively, at every object nesting level).
- **UTF-8 decoding is strict.** Invalid bytes raise `UnicodeDecodeError`
  (caller maps to the parse-error boundary).
- **Decoder failures map to `ValueError`** with a stable message
  (`"duplicate JSON object key: <key>"`, `"Invalid \\escape"`,
  `"Unterminated string"`, etc.). The caller is responsible for mapping
  this to the project's parse-error boundary
  (``StrictParseError(..., ERR_MALFORMED_JSON, ...)``).

See `tests/test_strict_json.py` for the direct test surface and
`tests/test_parser.py` for the higher-level adversarial tests.
"""

from __future__ import annotations

import json
from typing import Any


def _no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """`object_pairs_hook` callback that rejects any duplicate object key.

    Runs at every object-literal nesting level because `json.JSONDecoder`
    dispatches `object_pairs_hook` recursively.
    """
    seen: set[str] = set()
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in seen:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        seen.add(key)
        result[key] = value
    return result


def _reject_non_standard_numeric(c: object) -> None:
    """`parse_constant` callback that rejects non-standard JSON numeric constants.

    Python's `json.JSONDecoder` accepts `NaN`, `Infinity`, and `-Infinity`
    by default. These are NOT in the JSON spec (RFC 8259) and conflict with
    the strict-JSON contract at certificate trust boundaries. The
    helper raises a `ValueError` instead; the caller (`parse_jsonl_strict`)
    maps it to `StrictParseError(..., ERR_MALFORMED_JSON, ...)`.

    `parse_constant` is only invoked for these non-standard tokens (the
    standard literals `true`/`false`/`null` and numbers are handled
    separately by the decoder), so raising unconditionally is correct.
    """
    raise ValueError(f"non-standard JSON numeric constant not allowed: {c!r}")


_decoder = json.JSONDecoder(
    object_pairs_hook=_no_duplicate_keys,
    parse_constant=_reject_non_standard_numeric,
)


def decode_strict_json(data: bytes | str) -> Any:
    """Decode JSON from bytes (strict UTF-8) or text, rejecting duplicate object keys
    and non-standard numeric constants (`NaN`, `Infinity`, `-Infinity`).

    Args:
        data: JSON bytes (strict UTF-8) or text.

    Returns:
        The decoded Python value.

    Raises:
        `UnicodeDecodeError`: if `data` is bytes and contains invalid UTF-8.
        `ValueError`: on duplicate object keys, non-standard numeric
            constants (`NaN` / `Infinity` / `-Infinity`), malformed JSON,
            or any other decoder failure. The message is stable across runs
            for a given failure mode, so callers can use it for diagnostics.
    """
    if isinstance(data, bytes):
        text = data.decode("utf-8", errors="strict")
    else:
        text = data
    return _decoder.decode(text)
