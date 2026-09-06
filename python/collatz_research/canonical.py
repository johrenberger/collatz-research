"""Canonical byte-stable serialization, SHA-256 digest, and JSONL helpers.

The canonical form is:
- UTF-8 encoded
- Keys in sorted order
- No extra whitespace (no spaces after colons or commas)
- One record per line (for JSONL)
- Trailing newline after each record

This guarantees that:
- Two semantically-equal certificates produce identical canonical bytes.
- Hashing the canonical bytes yields a stable digest.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any

# Proof-bearing fields (in sorted order). Used for digest computation.
PROOF_BEARING_FIELDS: tuple[str, ...] = ("schema_version", "start", "steps", "target")


def canonical_jsonb(obj: dict[str, Any]) -> bytes:
    """Return the canonical UTF-8 bytes of `obj` (sorted keys, no whitespace, no trailing newline).

    Raises TypeError if any field is not JSON-serializable.
    """
    s = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return s.encode("utf-8")


def canonical_jsonb_with_newline(obj: dict[str, Any]) -> bytes:
    """Canonical bytes with a single trailing LF (one-record file convention)."""
    return canonical_jsonb(obj) + b"\n"


def compute_digest(cert: dict[str, Any]) -> str:
    """Compute the SHA-256 digest over the proof-bearing fields of `cert`.

    The fields are serialized in the canonical form (sorted keys, no
    whitespace) and SHA-256 is applied to the resulting UTF-8 bytes.
    The digest is returned as a lowercase hex string of 64 characters.
    """
    proof_bearing = {k: cert[k] for k in PROOF_BEARING_FIELDS}
    canonical = canonical_jsonb(proof_bearing)
    return hashlib.sha256(canonical).hexdigest()


def write_jsonl(records: list[dict[str, Any]]) -> bytes:
    """Serialize a list of records as JSONL (UTF-8, canonical, LF-terminated)."""
    return b"".join(canonical_jsonb_with_newline(r) for r in records)


def parse_jsonl_bytes(data: bytes) -> list[dict[str, Any]]:
    """Parse JSONL bytes into a list of records. Raises json.JSONDecodeError on malformed lines."""
    records = []
    for line in data.split(b"\n"):
        if not line.strip():
            continue
        records.append(json.loads(line.decode("utf-8")))
    return records
