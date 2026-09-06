"""Semantic checker for local descent certificates."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .canonical import compute_digest
from .parser import parse_jsonl_strict
from .trajectory import iterate

ERR_DIGEST_MISMATCH = "DIGEST_MISMATCH"
ERR_NOT_DESCENT = "NOT_DESCENT"
ERR_RECORD_COUNT = "RECORD_COUNT"
ERR_TRAJECTORY_MISMATCH = "TRAJECTORY_MISMATCH"
ERR_TRAJECTORY_UNDEFINED = "TRAJECTORY_UNDEFINED"


class CertificateCheckError(Exception):
    """Raised when a parsed certificate fails semantic checking."""

    def __init__(self, category: str, message: str):
        self.category = category
        self.message = message
        super().__init__(f"{category}: {message}")


@dataclass(frozen=True, slots=True)
class CheckedCertificate:
    """Accepted finite certificate plus its canonical proof-bearing digest."""

    schema_version: str
    start: int
    steps: int
    target: int
    digest: str
    trajectory: tuple[int, ...]


def _coerce_digest(expected_digest: str | Path | None) -> str | None:
    if expected_digest is None:
        return None
    if isinstance(expected_digest, Path):
        return expected_digest.read_text(encoding="utf-8").strip()
    return expected_digest.strip()


def check_certificate(
    cert_path: str | Path,
    *,
    expected_digest: str | Path | None = None,
) -> CheckedCertificate:
    """Parse and semantically check a one-record local descent certificate.

    The certificate file is JSONL, but Story 06's local-descent checker accepts
    exactly one record. The digest is recomputed over the canonical
    proof-bearing fields. If `expected_digest` is supplied as a string or a
    path to a text file, it must match the recomputed digest.
    """
    path = Path(cert_path)
    records = parse_jsonl_strict(path.read_bytes())
    if len(records) != 1:
        raise CertificateCheckError(
            ERR_RECORD_COUNT,
            f"expected exactly one certificate record, got {len(records)}",
        )

    record: dict[str, Any] = records[0]
    digest = compute_digest(record)
    expected = _coerce_digest(expected_digest)
    if expected is not None and digest != expected:
        raise CertificateCheckError(
            ERR_DIGEST_MISMATCH,
            f"expected digest {expected}, got {digest}",
        )

    start = record["start"]
    steps = record["steps"]
    target = record["target"]
    try:
        trajectory = tuple(iterate(start, steps))
    except ValueError as e:
        raise CertificateCheckError(ERR_TRAJECTORY_UNDEFINED, str(e)) from e

    actual_target = trajectory[-1]
    if actual_target != target:
        raise CertificateCheckError(
            ERR_TRAJECTORY_MISMATCH,
            f"trajectory({start}, {steps}) ended at {actual_target}, not {target}",
        )
    if not target < start:
        raise CertificateCheckError(
            ERR_NOT_DESCENT,
            f"target {target} is not strictly below start {start}",
        )

    return CheckedCertificate(
        schema_version=record["schema_version"],
        start=start,
        steps=steps,
        target=target,
        digest=digest,
        trajectory=trajectory,
    )
