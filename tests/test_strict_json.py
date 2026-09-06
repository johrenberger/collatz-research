"""Direct tests for the strict JSON helper.

The helper is the single source of truth for JSON-layer strictness at
certificate trust boundaries. These tests cover the helper's contract
independently of the higher-level parser.
"""

from __future__ import annotations

import pytest
from collatz_research.strict_json import decode_strict_json

# --- Basic decode (round-trip with the stdlib for the non-strict cases) ---


def test_decodes_object() -> None:
    assert decode_strict_json(b'{"a":1,"b":2}') == {"a": 1, "b": 2}


def test_decodes_from_text() -> None:
    assert decode_strict_json('{"a":1}') == {"a": 1}


def test_decodes_array() -> None:
    assert decode_strict_json(b"[1,2,3]") == [1, 2, 3]


def test_decodes_nested() -> None:
    obj = decode_strict_json(b'{"a":{"b":{"c":1}}}')
    assert obj == {"a": {"b": {"c": 1}}}


def test_decodes_unicode_escape() -> None:
    assert decode_strict_json(b'{"k":"\\u00e9"}') == {"k": "é"}


# --- Duplicate-key rejection (the core strictness guarantee) ---


def test_same_line_duplicate_raises() -> None:
    """Two `start` keys on the same object raises."""
    with pytest.raises(ValueError, match="duplicate JSON object key: 'start'"):
        decode_strict_json(b'{"schema_version":"1.0","start":1,"start":2}')


def test_three_way_duplicate_raises() -> None:
    """Three-way duplicate also raises (not just two)."""
    with pytest.raises(ValueError, match="duplicate JSON object key: 'steps'"):
        decode_strict_json(
            b'{"schema_version":"1.0","start":1,"steps":0,"steps":99,"steps":100,"target":1}'
        )


def test_nested_duplicate_raises() -> None:
    """Duplicates in a nested object are also caught (recursively)."""
    with pytest.raises(ValueError, match="duplicate JSON object key: 'x'"):
        decode_strict_json(b'{"meta":{"x":1,"x":2}}')


def test_no_duplicate_when_keys_distinct() -> None:
    """Distinct keys pass through even at deep nesting."""
    obj = decode_strict_json(b'{"a":{"b":{"c":1,"d":2}},"e":3}')
    assert obj == {"a": {"b": {"c": 1, "d": 2}}, "e": 3}


# --- UTF-8 strictness ---


def test_valid_utf8_decodes() -> None:
    assert decode_strict_json('{"k":"café"}'.encode()) == {"k": "café"}


def test_invalid_utf8_bytes_raise() -> None:
    """Bytes that aren't valid UTF-8 raise UnicodeDecodeError."""
    # 0xFF is not a valid UTF-8 start byte.
    with pytest.raises(UnicodeDecodeError):
        decode_strict_json(b'{"k":"\xff"}')


# --- Malformed JSON ---


def test_unterminated_string_raises() -> None:
    with pytest.raises(ValueError):
        decode_strict_json(b'{"k":"unterminated}')


def test_garbage_raises() -> None:
    with pytest.raises(ValueError):
        decode_strict_json(b"not json at all")


def test_empty_object_is_valid() -> None:
    """An empty object is valid JSON; no duplicate keys to flag."""
    assert decode_strict_json(b"{}") == {}


def test_empty_array_is_valid() -> None:
    assert decode_strict_json(b"[]") == []


# --- Non-object payloads (regression: object_pairs_hook fires only on objects) ---


def test_array_of_objects_with_duplicate_key_inside_raises() -> None:
    """Arrays are decoded; duplicate keys WITHIN each array element are caught."""
    # The second array element has `x` twice (internal duplicate);
    # the first element has only one `x` (no internal duplicate).
    with pytest.raises(ValueError, match="duplicate JSON object key: 'x'"):
        decode_strict_json(b'[{"x":1},{"x":2,"x":3}]')


def test_null_is_valid() -> None:
    assert decode_strict_json(b"null") is None


def test_number_is_valid() -> None:
    assert decode_strict_json(b"42") == 42


def test_string_is_valid() -> None:
    assert decode_strict_json(b'"hello"') == "hello"


# --- Non-standard numeric constant rejection (P2 review feedback) ---


def test_nan_constant_raises() -> None:
    """`NaN` is not in RFC 8259; the strict helper rejects it."""
    with pytest.raises(ValueError, match="non-standard JSON numeric constant not allowed: 'NaN'"):
        decode_strict_json(b"NaN")


def test_infinity_constant_raises() -> None:
    """`Infinity` is not in RFC 8259; the strict helper rejects it."""
    with pytest.raises(
        ValueError, match="non-standard JSON numeric constant not allowed: 'Infinity'"
    ):
        decode_strict_json(b"Infinity")


def test_negative_infinity_constant_raises() -> None:
    """`-Infinity` is not in RFC 8259; the strict helper rejects it."""
    with pytest.raises(
        ValueError, match="non-standard JSON numeric constant not allowed: '-Infinity'"
    ):
        decode_strict_json(b"-Infinity")


def test_nan_in_object_value_raises() -> None:
    """`NaN` inside an object value is rejected with a clear message."""
    with pytest.raises(ValueError, match="non-standard JSON numeric constant not allowed: 'NaN'"):
        decode_strict_json(b'{"k": NaN}')


def test_infinity_in_array_value_raises() -> None:
    """`Infinity` inside an array value is rejected with a clear message."""
    with pytest.raises(
        ValueError, match="non-standard JSON numeric constant not allowed: 'Infinity'"
    ):
        decode_strict_json(b"[1, Infinity, 3]")
