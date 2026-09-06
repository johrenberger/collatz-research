"""Tests for canonical serialization, SHA-256 digest, and JSONL helpers."""

from __future__ import annotations

import json

from collatz_research.canonical import (
    PROOF_BEARING_FIELDS,
    canonical_jsonb,
    canonical_jsonb_with_newline,
    compute_digest,
    parse_jsonl_bytes,
    write_jsonl,
)

# --- Canonical JSON ---


def test_canonical_jsonb_sorts_keys() -> None:
    obj = {"b": 2, "a": 1, "c": 3}
    assert canonical_jsonb(obj) == b'{"a":1,"b":2,"c":3}'


def test_canonical_jsonb_no_whitespace() -> None:
    obj = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    assert canonical_jsonb(obj) == b'{"schema_version":"1.0","start":1,"steps":1,"target":1}'


def test_canonical_jsonb_utf8() -> None:
    obj = {"name": "café"}
    assert canonical_jsonb(obj) == b'{"name":"caf\xc3\xa9"}'


def test_canonical_jsonb_with_newline_appends_lf() -> None:
    obj = {"a": 1}
    assert canonical_jsonb_with_newline(obj) == b'{"a":1}\n'


def test_canonical_jsonb_deterministic() -> None:
    obj = {"b": 2, "a": 1}
    assert canonical_jsonb(obj) == canonical_jsonb(obj)


def test_canonical_jsonb_rejects_unserializable() -> None:
    import pytest

    with pytest.raises(TypeError):
        canonical_jsonb({"x": {1, 2, 3}})  # set is not JSON-serializable


# --- SHA-256 digest ---


def test_compute_digest_deterministic() -> None:
    cert = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    assert compute_digest(cert) == compute_digest(cert)


def test_compute_digest_64_lowercase_hex() -> None:
    cert = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    digest = compute_digest(cert)
    assert len(digest) == 64
    assert all(c in "0123456789abcdef" for c in digest)


def test_compute_digest_uses_only_proof_bearing_fields() -> None:
    cert = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    extras = {"non_proof_field": "value", "another": 42}
    assert compute_digest(cert) == compute_digest(cert | extras)


def test_compute_digest_changes_with_field_value() -> None:
    cert1 = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    cert2 = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 2}
    assert compute_digest(cert1) != compute_digest(cert2)


def test_compute_digest_changes_with_schema_version() -> None:
    cert1 = {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1}
    cert2 = {"schema_version": "1.1", "start": 1, "steps": 1, "target": 1}
    assert compute_digest(cert1) != compute_digest(cert2)


def test_proof_bearing_fields_sorted() -> None:
    assert list(PROOF_BEARING_FIELDS) == sorted(PROOF_BEARING_FIELDS)


def test_proof_bearing_fields_count() -> None:
    assert len(PROOF_BEARING_FIELDS) == 4


# --- JSONL ---


def test_write_jsonl_empty_list() -> None:
    assert write_jsonl([]) == b""


def test_write_jsonl_single_record() -> None:
    records = [{"a": 1}]
    assert write_jsonl(records) == b'{"a":1}\n'


def test_write_jsonl_multiple_records() -> None:
    records = [{"a": 1}, {"b": 2}]
    assert write_jsonl(records) == b'{"a":1}\n{"b":2}\n'


def test_parse_jsonl_bytes_empty() -> None:
    assert parse_jsonl_bytes(b"") == []


def test_parse_jsonl_bytes_single_record() -> None:
    assert parse_jsonl_bytes(b'{"a":1}\n') == [{"a": 1}]


def test_parse_jsonl_bytes_multiple_records() -> None:
    assert parse_jsonl_bytes(b'{"a":1}\n{"b":2}\n') == [{"a": 1}, {"b": 2}]


def test_parse_jsonl_bytes_skip_empty_lines() -> None:
    assert parse_jsonl_bytes(b'{"a":1}\n\n{"b":2}\n') == [{"a": 1}, {"b": 2}]


def test_parse_jsonl_bytes_malformed_raises() -> None:
    import pytest

    with pytest.raises(json.JSONDecodeError):
        parse_jsonl_bytes(b'{"a":1}\nnot valid json\n')


def test_jsonl_roundtrip() -> None:
    records = [{"a": 1}, {"b": 2}, {"c": 3}]
    assert parse_jsonl_bytes(write_jsonl(records)) == records


def test_jsonl_roundtrip_certificates() -> None:
    records = [
        {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1},
        {"schema_version": "1.0", "start": 27, "steps": 8, "target": 91},
    ]
    assert parse_jsonl_bytes(write_jsonl(records)) == records
