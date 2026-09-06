"""Strict parser for certificates with stable error categories.

Errors fall into stable categories so that downstream tooling can
distinguish user errors (unknown schema, missing field) from
malformed-input errors (broken JSON, bad encoding). All categories are
uppercase strings to match the project's conventions.

**Important:** JSON-layer strictness (duplicate-key rejection, strict
UTF-8 decoding, decoder-failure mapping) lives in `strict_json.py`. Do
**not** use the stdlib `json.loads` directly at any certificate trust
boundary; route through `strict_json.decode_strict_json` instead.
"""

from __future__ import annotations

from typing import Any

from .strict_json import decode_strict_json

# Error categories (stable, uppercase).
ERR_MALFORMED_JSON = "MALFORMED_JSON"
ERR_UNKNOWN_SCHEMA = "UNKNOWN_SCHEMA"
ERR_UNKNOWN_FIELD = "UNKNOWN_FIELD"
ERR_MISSING_FIELD = "MISSING_FIELD"
ERR_INVALID_VALUE = "INVALID_VALUE"

# Known schema versions.
KNOWN_SCHEMA_VERSIONS: frozenset[str] = frozenset({"1.0"})

# Known fields per schema version. Schema v1.0: schema_version, start, steps, target.
KNOWN_FIELDS_V1: frozenset[str] = frozenset({"schema_version", "start", "steps", "target"})

# Field constraints (value ranges).
FIELD_CONSTRAINTS_V1: dict[str, dict[str, int]] = {
    "start": {"min": 1},
    "steps": {"min": 0},
    "target": {"min": 1},
}


class StrictParseError(Exception):
    """Raised when a certificate fails to parse in a strict way."""

    def __init__(self, line_no: int, category: str, message: str):
        self.line_no = line_no
        self.category = category
        self.message = message
        super().__init__(f"line {line_no}: {category}: {message}")


def known_fields_for_version(schema_version: str) -> frozenset[str] | None:
    if schema_version == "1.0":
        return KNOWN_FIELDS_V1
    return None


def field_constraints_for_version(schema_version: str) -> dict[str, dict[str, int]] | None:
    if schema_version == "1.0":
        return FIELD_CONSTRAINTS_V1
    return None


def strict_parse_record(obj: dict[str, Any], line_no: int = 1) -> dict[str, Any]:
    """Strict-parse a single certificate record.

    Raises StrictParseError with a stable category. Returns the record
    unchanged on success (no transformation).

    Pre-condition: the caller must have already produced `obj` via
    `strict_json.decode_strict_json` (or an equivalent that rejects
    duplicate object keys and decoder failures). This function does
    NOT re-decode; it only validates the already-parsed dict against
    the schema.
    """
    if not isinstance(obj, dict):
        raise StrictParseError(
            line_no,
            ERR_MALFORMED_JSON,
            f"expected dict, got {type(obj).__name__}",
        )

    schema_version = obj.get("schema_version")
    if schema_version is None:
        raise StrictParseError(line_no, ERR_MISSING_FIELD, "schema_version missing")
    if not isinstance(schema_version, str):
        raise StrictParseError(
            line_no,
            ERR_INVALID_VALUE,
            f"schema_version must be string, got {type(schema_version).__name__}",
        )
    if schema_version not in KNOWN_SCHEMA_VERSIONS:
        raise StrictParseError(
            line_no,
            ERR_UNKNOWN_SCHEMA,
            f"schema_version {schema_version!r} not in known versions",
        )

    known_fields = known_fields_for_version(schema_version)
    if known_fields is None:
        raise StrictParseError(
            line_no,
            ERR_UNKNOWN_SCHEMA,
            f"no field set registered for schema_version {schema_version!r}",
        )

    unknown = set(obj.keys()) - known_fields
    if unknown:
        raise StrictParseError(
            line_no,
            ERR_UNKNOWN_FIELD,
            f"unknown fields: {sorted(unknown)}",
        )

    missing = known_fields - set(obj.keys())
    if missing:
        raise StrictParseError(
            line_no,
            ERR_MISSING_FIELD,
            f"missing required fields: {sorted(missing)}",
        )

    constraints = field_constraints_for_version(schema_version)
    if constraints is None:
        raise StrictParseError(
            line_no,
            ERR_UNKNOWN_SCHEMA,
            f"no constraints registered for schema_version {schema_version!r}",
        )

    for field, constraint in constraints.items():
        value = obj[field]
        # Reject booleans (which are technically int in Python).
        if isinstance(value, bool) or not isinstance(value, int):
            raise StrictParseError(
                line_no,
                ERR_INVALID_VALUE,
                f"field {field!r} = {value!r} must be int, got {type(value).__name__}",
            )
        if "min" in constraint and value < constraint["min"]:
            raise StrictParseError(
                line_no,
                ERR_INVALID_VALUE,
                f"field {field!r} = {value} violates minimum {constraint['min']}",
            )

    return obj


def parse_jsonl_strict(data: bytes) -> list[dict[str, Any]]:
    """Parse JSONL bytes with strict per-record validation.

    Each non-empty line is decoded via `strict_json.decode_strict_json`
    (which rejects duplicate object keys, strict UTF-8, and decoder
    failures as `ValueError` / `UnicodeDecodeError`) and then validated
    by `strict_parse_record` against the schema. Malformed JSON raises
    `StrictParseError` with category `MALFORMED_JSON` and the offending
    line number.
    """
    records: list[dict[str, Any]] = []
    for line_no, line in enumerate(data.split(b"\n"), start=1):
        if not line.strip():
            continue
        try:
            obj = decode_strict_json(line)
        except (ValueError, UnicodeDecodeError) as e:
            raise StrictParseError(line_no, ERR_MALFORMED_JSON, str(e)) from e
        strict_parse_record(obj, line_no=line_no)
        records.append(obj)
    return records
