"""Tests for the semantic local-descent certificate checker."""

from __future__ import annotations

import pytest
from collatz_research.canonical import compute_digest, write_jsonl
from collatz_research.certificates import build_descent_certificate
from collatz_research.checker import (
    ERR_DIGEST_MISMATCH,
    ERR_NOT_DESCENT,
    ERR_RECORD_COUNT,
    ERR_TRAJECTORY_MISMATCH,
    ERR_TRAJECTORY_UNDEFINED,
    CertificateCheckError,
    check_certificate,
)
from collatz_research.parser import ERR_UNKNOWN_FIELD, ERR_UNKNOWN_SCHEMA, StrictParseError


def _write_cert(tmp_path, record: dict) -> object:
    path = tmp_path / "certificate.jsonl"
    path.write_bytes(write_jsonl([record]))
    return path


def test_check_certificate_accepts_strict_local_descent(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1}
    checked = check_certificate(_write_cert(tmp_path, record))
    assert checked.start == 5
    assert checked.steps == 1
    assert checked.target == 1
    assert checked.trajectory == (5, 1)
    assert checked.digest == compute_digest(record)


def test_check_certificate_verifies_expected_digest_string(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1}
    checked = check_certificate(
        _write_cert(tmp_path, record), expected_digest=compute_digest(record)
    )
    assert checked.digest == compute_digest(record)


def test_check_certificate_verifies_expected_digest_file(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1}
    digest_path = tmp_path / "certificate.sha256"
    digest_path.write_text(compute_digest(record) + "\n", encoding="utf-8")
    checked = check_certificate(_write_cert(tmp_path, record), expected_digest=digest_path)
    assert checked.digest == compute_digest(record)


def test_check_certificate_rejects_digest_mismatch(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1}
    with pytest.raises(CertificateCheckError) as exc_info:
        check_certificate(_write_cert(tmp_path, record), expected_digest="0" * 64)
    assert exc_info.value.category == ERR_DIGEST_MISMATCH


@pytest.mark.parametrize(
    "mutated, category, error_type",
    [
        (
            {"schema_version": "2.0", "start": 5, "steps": 1, "target": 1},
            ERR_UNKNOWN_SCHEMA,
            StrictParseError,
        ),
        (
            {"schema_version": "1.0", "start": 7, "steps": 1, "target": 1},
            ERR_TRAJECTORY_MISMATCH,
            CertificateCheckError,
        ),
        (
            {"schema_version": "1.0", "start": 5, "steps": 0, "target": 1},
            ERR_TRAJECTORY_MISMATCH,
            CertificateCheckError,
        ),
        (
            {"schema_version": "1.0", "start": 5, "steps": 1, "target": 5},
            ERR_TRAJECTORY_MISMATCH,
            CertificateCheckError,
        ),
    ],
)
def test_check_certificate_rejects_field_mutations(tmp_path, mutated, category, error_type) -> None:
    with pytest.raises(error_type) as exc_info:
        check_certificate(_write_cert(tmp_path, mutated))
    assert exc_info.value.category == category


def test_check_certificate_rejects_non_descent(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 1, "steps": 0, "target": 1}
    with pytest.raises(CertificateCheckError) as exc_info:
        check_certificate(_write_cert(tmp_path, record))
    assert exc_info.value.category == ERR_NOT_DESCENT


def test_check_certificate_rejects_undefined_accelerated_trajectory(tmp_path) -> None:
    record = {"schema_version": "1.0", "start": 2, "steps": 1, "target": 1}
    with pytest.raises(CertificateCheckError) as exc_info:
        check_certificate(_write_cert(tmp_path, record))
    assert exc_info.value.category == ERR_TRAJECTORY_UNDEFINED


def test_check_certificate_rejects_multiple_records(tmp_path) -> None:
    path = tmp_path / "certificates.jsonl"
    path.write_bytes(
        write_jsonl(
            [
                {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1},
                {"schema_version": "1.0", "start": 5, "steps": 1, "target": 1},
            ]
        )
    )
    with pytest.raises(CertificateCheckError) as exc_info:
        check_certificate(path)
    assert exc_info.value.category == ERR_RECORD_COUNT


def test_check_certificate_rejects_embedded_digest_field(tmp_path) -> None:
    record = {
        "schema_version": "1.0",
        "start": 5,
        "steps": 1,
        "target": 1,
        "digest": "0" * 64,
    }
    with pytest.raises(StrictParseError) as exc_info:
        check_certificate(_write_cert(tmp_path, record))
    assert exc_info.value.category == ERR_UNKNOWN_FIELD


def test_generator_checker_integration(tmp_path) -> None:
    cert = build_descent_certificate(5, 1)
    checked = check_certificate(_write_cert(tmp_path, cert.as_dict()))
    assert checked.target == cert.target
    assert checked.digest == compute_digest(cert.as_dict())
