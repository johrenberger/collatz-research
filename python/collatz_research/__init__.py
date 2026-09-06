"""Untrusted tools for exploring accelerated Collatz dynamics."""

from .accelerated import accelerated_step, two_adic_valuation
from .affine import AffineMap, BranchWord
from .canonical import (
    PROOF_BEARING_FIELDS,
    canonical_jsonb,
    canonical_jsonb_with_newline,
    compute_digest,
    parse_jsonl_bytes,
    write_jsonl,
)
from .certificates import DescentCertificate, build_descent_certificate
from .checker import (
    ERR_DIGEST_MISMATCH,
    ERR_NOT_DESCENT,
    ERR_RECORD_COUNT,
    ERR_TRAJECTORY_MISMATCH,
    ERR_TRAJECTORY_UNDEFINED,
    CertificateCheckError,
    CheckedCertificate,
    check_certificate,
)
from .parser import (
    ERR_INVALID_VALUE,
    ERR_MALFORMED_JSON,
    ERR_MISSING_FIELD,
    ERR_UNKNOWN_FIELD,
    ERR_UNKNOWN_SCHEMA,
    KNOWN_FIELDS_V1,
    KNOWN_SCHEMA_VERSIONS,
    StrictParseError,
    parse_jsonl_strict,
    strict_parse_record,
)
from .partitions import (
    ERR_INCOMPLETE,
    ERR_INVALID_RESIDUE,
    ERR_NON_DISJOINT,
    PartitionError,
    is_partition,
)
from .standard import is_even, is_odd, is_positive, standard_step, standard_trajectory
from .strict_json import decode_strict_json

__all__ = [
    "accelerated_step",
    "AffineMap",
    "BranchWord",
    "build_descent_certificate",
    "canonical_jsonb",
    "canonical_jsonb_with_newline",
    "CertificateCheckError",
    "check_certificate",
    "CheckedCertificate",
    "compute_digest",
    "decode_strict_json",
    "DescentCertificate",
    "ERR_DIGEST_MISMATCH",
    "ERR_INCOMPLETE",
    "ERR_INVALID_RESIDUE",
    "ERR_INVALID_VALUE",
    "ERR_MALFORMED_JSON",
    "ERR_MISSING_FIELD",
    "ERR_NON_DISJOINT",
    "ERR_NOT_DESCENT",
    "ERR_RECORD_COUNT",
    "ERR_TRAJECTORY_MISMATCH",
    "ERR_TRAJECTORY_UNDEFINED",
    "ERR_UNKNOWN_FIELD",
    "ERR_UNKNOWN_SCHEMA",
    "is_even",
    "is_odd",
    "is_partition",
    "is_positive",
    "KNOWN_FIELDS_V1",
    "KNOWN_SCHEMA_VERSIONS",
    "parse_jsonl_bytes",
    "parse_jsonl_strict",
    "PartitionError",
    "PROOF_BEARING_FIELDS",
    "standard_step",
    "standard_trajectory",
    "StrictParseError",
    "strict_parse_record",
    "two_adic_valuation",
    "write_jsonl",
]
