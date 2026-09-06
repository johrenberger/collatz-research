"""Tests for the strict parser with adversarial fixtures."""

from __future__ import annotations

import pytest
from collatz_research.parser import (
    ERR_INVALID_VALUE,
    ERR_MALFORMED_JSON,
    ERR_MISSING_FIELD,
    ERR_UNKNOWN_FIELD,
    ERR_UNKNOWN_SCHEMA,
    KNOWN_SCHEMA_VERSIONS,
    StrictParseError,
    parse_jsonl_strict,
    strict_parse_record,
)

# --- Valid records ---


def test_valid_minimal_certificate() -> None:
    cert = {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1}
    assert strict_parse_record(cert) == cert


def test_valid_trajectory_certificate() -> None:
    cert = {"schema_version": "1.0", "start": 27, "steps": 8, "target": 91}
    assert strict_parse_record(cert) == cert


def test_valid_zero_steps() -> None:
    cert = {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1}
    assert strict_parse_record(cert) == cert


def test_valid_large_values() -> None:
    cert = {"schema_version": "1.0", "start": 10**18, "steps": 1000, "target": 1}
    assert strict_parse_record(cert) == cert


def test_valid_field_order_independent() -> None:
    """Field order in the dict does not matter for parsing."""
    a = {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1}
    b = {"target": 1, "steps": 0, "start": 1, "schema_version": "1.0"}
    assert strict_parse_record(a) == strict_parse_record(b)


# --- MALFORMED_JSON ---


def test_non_dict_raises_malformed_json() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record([1, 2, 3], line_no=1)
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 1


def test_string_raises_malformed_json() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record("not a dict", line_no=5)
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 5


def test_none_raises_malformed_json() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record(None, line_no=3)
    assert exc_info.value.category == ERR_MALFORMED_JSON


def test_int_raises_malformed_json() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record(42, line_no=7)
    assert exc_info.value.category == ERR_MALFORMED_JSON


# --- UNKNOWN_SCHEMA ---


def test_unknown_schema_version_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "2.0", "start": 1, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_UNKNOWN_SCHEMA


def test_empty_schema_version_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "", "start": 1, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_UNKNOWN_SCHEMA


def test_known_schema_versions_is_frozenset_with_1_0() -> None:
    assert isinstance(KNOWN_SCHEMA_VERSIONS, frozenset)
    assert "1.0" in KNOWN_SCHEMA_VERSIONS


# --- MISSING_FIELD ---


def test_missing_schema_version_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"start": 1, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_MISSING_FIELD


def test_missing_start_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_MISSING_FIELD


def test_missing_steps_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": 1, "target": 1})
    assert exc_info.value.category == ERR_MISSING_FIELD


def test_missing_target_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": 1, "steps": 0})
    assert exc_info.value.category == ERR_MISSING_FIELD


def test_missing_multiple_fields_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0"})
    assert exc_info.value.category == ERR_MISSING_FIELD


# --- UNKNOWN_FIELD ---


def test_extra_field_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record(
            {
                "schema_version": "1.0",
                "start": 1,
                "steps": 0,
                "target": 1,
                "extra": "value",
            }
        )
    assert exc_info.value.category == ERR_UNKNOWN_FIELD


def test_digest_field_raises() -> None:
    """A digest field (not in v1.0 schema) raises UNKNOWN_FIELD."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record(
            {
                "schema_version": "1.0",
                "start": 1,
                "steps": 0,
                "target": 1,
                "digest": "abc123",
            }
        )
    assert exc_info.value.category == ERR_UNKNOWN_FIELD


def test_empty_dict_raises_missing_field() -> None:
    """An empty dict raises MISSING_FIELD (schema_version missing)."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({})
    assert exc_info.value.category == ERR_MISSING_FIELD


# --- INVALID_VALUE ---


def test_negative_start_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": -1, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_zero_start_raises() -> None:
    """Zero start raises INVALID_VALUE (minimum is 1)."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": 0, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_negative_steps_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": 1, "steps": -1, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_zero_target_raises() -> None:
    """Zero target raises INVALID_VALUE (minimum is 1)."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": 1, "steps": 0, "target": 0})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_non_int_start_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": "1", "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_bool_rejected_as_int() -> None:
    """Boolean values are rejected (not counted as int)."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "1.0", "start": True, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


def test_non_string_schema_version_raises() -> None:
    """Non-string schema_version raises INVALID_VALUE."""
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": 1.0, "start": 1, "steps": 0, "target": 1})
    assert exc_info.value.category == ERR_INVALID_VALUE


# --- Line number propagation ---


def test_line_no_default_is_1() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record({"schema_version": "2.0", "start": 1, "steps": 0, "target": 1})
    assert exc_info.value.line_no == 1


def test_line_no_custom_propagated() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        strict_parse_record(
            {"schema_version": "2.0", "start": 1, "steps": 0, "target": 1},
            line_no=42,
        )
    assert exc_info.value.line_no == 42


# --- JSONL strict ---


def test_parse_jsonl_strict_valid_records() -> None:
    data = (
        b'{"schema_version":"1.0","start":1,"steps":1,"target":1}'
        b"\n"
        b'{"schema_version":"1.0","start":27,"steps":8,"target":91}'
        b"\n"
    )
    assert parse_jsonl_strict(data) == [
        {"schema_version": "1.0", "start": 1, "steps": 1, "target": 1},
        {"schema_version": "1.0", "start": 27, "steps": 8, "target": 91},
    ]


def test_parse_jsonl_strict_empty() -> None:
    assert parse_jsonl_strict(b"") == []


def test_parse_jsonl_strict_skip_empty_lines() -> None:
    data = (
        b'{"schema_version":"1.0","start":1,"steps":0,"target":1}'
        b"\n\n"
        b'{"schema_version":"1.0","start":2,"steps":1,"target":1}'
        b"\n"
    )
    assert parse_jsonl_strict(data) == [
        {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1},
        {"schema_version": "1.0", "start": 2, "steps": 1, "target": 1},
    ]


def test_parse_jsonl_strict_malformed_json_raises() -> None:
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(
            b'{"schema_version":"1.0","start":1,"steps":0,"target":1}\nnot valid json\n'
        )
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 2


def test_parse_jsonl_strict_nan_constant_raises_malformed_json() -> None:
    """A `NaN` token at the parser boundary is `MALFORMED_JSON` (P2 review feedback)."""
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(b'{"k":NaN}\n')
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 1
    assert "non-standard JSON numeric constant" in str(exc_info.value)


def test_parse_jsonl_strict_invalid_record_raises() -> None:
    """An invalid record (e.g., missing field) raises with the right line number."""
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(
            b'{"schema_version":"1.0","start":1,"steps":0,"target":1}\n{"schema_version":"1.0","start":1,"steps":0}\n'
        )
    assert exc_info.value.category == ERR_MISSING_FIELD
    assert exc_info.value.line_no == 2


def test_parse_jsonl_strict_rejects_duplicate_keys() -> None:
    """Adversarial: duplicate object keys raise MALFORMED_JSON.

    `json.loads` silently accepts duplicate keys (last wins), so two
    distinct certificate byte streams would parse to the same record
    and digest. For canonical certificates, we reject duplicates.
    """
    # Two `start` keys in the same object — ambiguous certificate.
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(b'{"schema_version":"1.0","start":1,"start":2,"steps":0,"target":1}\n')
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 1


def test_parse_jsonl_strict_rejects_duplicate_keys_in_second_line() -> None:
    """Adversarial: duplicate keys on a non-first line yield the right line number."""
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(
            b'{"schema_version":"1.0","start":1,"steps":0,"target":1}\n{"schema_version":"1.0","start":1,"start":3,"steps":1,"target":1}\n'
        )
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 2


def test_parse_jsonl_strict_rejects_nested_duplicate_keys() -> None:
    """Adversarial: duplicate keys in a nested object are also rejected."""
    # The nested object has duplicate `x` keys; the whole record must fail.
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(
            b'{"schema_version":"1.0","start":1,"steps":0,"target":1,"meta":{"x":1,"x":2}}\n'
        )
    assert exc_info.value.category == ERR_MALFORMED_JSON
    assert exc_info.value.line_no == 1


def test_parse_jsonl_strict_rejects_three_duplicate_keys_in_one_object() -> None:
    """Adversarial: three-way duplicate keys (not just two) are rejected."""
    with pytest.raises(StrictParseError) as exc_info:
        parse_jsonl_strict(
            b'{"schema_version":"1.0","start":1,"steps":0,"target":1,"steps":99,"steps":100}\n'
        )
    assert exc_info.value.category == ERR_MALFORMED_JSON
