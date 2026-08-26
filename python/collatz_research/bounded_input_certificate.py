"""Untrusted bounded-input certificate producer (Q5 PR #3).

Emits `BoundedInputCertificateWire` (per Q5 v5 wire model + PR #62 v5
Lean record) as deterministic JSON bytes for the wire format
`schemas/bounded-input-certificate-v1.json`. The Lean parser
(`BoundedInputCertificateParser.lean`, Q5 PR #3) parses + verifies the
emitted bytes; the producer itself is UNTRUSTED — only the Lean
verifier + soundness theorem enter the trusted computing base.

Trust boundary (per Q5 v5 spec § 4.3.1a):
  Python serialized evidence → (Q5 PR #3 JSON parser) →
  Lean wire → Lean checked → Bool verifier → soundness theorem
  (Q5 PR #4) → BoundedInputOrbitCertificate →
  coverage_tree_soundness_orbit_cert_bounded.

Design choices (per Justin's approval of the 3 Q5 PR #3 decisions):
1. Parser return type: `Except String BoundedInputCertificateWire`
   (informative — surfaces rejection reason in tests).
2. Producer scope: `singleLeafTree` (matches PR #62 test fixture).
   `depthTwoTree` deferred to PR #4 (integration).
3. JSON parser implementation: hand-rolled Lean parser for the fixed
   schema. Producer-side Python uses stdlib `json.dumps` for determinism
   (sorted keys, no whitespace, ASCII-only).
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import ClassVar

from .tree import CoverageLeaf


# Wire format schema version. Immutable.
SCHEMA_VERSION: str = "1.0"


# ===== Claim types =====


@dataclass(frozen=True)
class FiniteOrbitClaimWire:
    """Wire model of `FiniteOrbitClaim` (PR #57 + PR #62 v5).

    Three constructors: `.empty | .singleton n | .bounded K`.
    `.interval` is structurally excluded (matches the Lean inductive).
    """

    type: str  # "empty" | "singleton" | "bounded"
    n: int | None = None
    K: int | None = None

    TYPE_EMPTY: ClassVar[str] = "empty"
    TYPE_SINGLETON: ClassVar[str] = "singleton"
    TYPE_BOUNDED: ClassVar[str] = "bounded"

    @classmethod
    def empty(cls) -> "FiniteOrbitClaimWire":
        return cls(type=cls.TYPE_EMPTY)

    @classmethod
    def singleton(cls, n: int) -> "FiniteOrbitClaimWire":
        if n < 1:
            raise ValueError(f"singleton claim requires n >= 1, got {n}")
        return cls(type=cls.TYPE_SINGLETON, n=n)

    @classmethod
    def bounded(cls, K: int) -> "FiniteOrbitClaimWire":
        if K < 1:
            raise ValueError(f"bounded claim requires K >= 1, got {K}")
        return cls(type=cls.TYPE_BOUNDED, K=K)

    def holds(self, y: int) -> bool:
        """Mirror `FiniteOrbitClaim.Holds` from `CoverageTree.lean`."""
        if self.type == self.TYPE_EMPTY:
            return False
        if self.type == self.TYPE_SINGLETON:
            assert self.n is not None
            return y == self.n
        if self.type == self.TYPE_BOUNDED:
            assert self.K is not None
            return y <= self.K
        raise ValueError(f"unsupported claim type: {self.type!r}")

    def to_dict(self) -> dict:
        if self.type == self.TYPE_EMPTY:
            return {"type": "empty"}
        if self.type == self.TYPE_SINGLETON:
            return {"type": "singleton", "n": self.n}
        if self.type == self.TYPE_BOUNDED:
            return {"type": "bounded", "K": self.K}
        raise ValueError(f"unsupported claim type: {self.type!r}")


# ===== Witness + wire bundle =====


@dataclass(frozen=True)
class CertWitnessWire:
    """Wire model of `CertWitnessWire` (PR #62 v5): leaf + trajectory."""

    leaf: CoverageLeaf
    trajectory: list[int]

    def to_dict(self) -> dict:
        return {
            "l": {
                "leafId": self.leaf.leaf_id,
                "leafProperty": self.leaf.leaf_property,
            },
            "trajectory": list(self.trajectory),
        }


@dataclass(frozen=True)
class BoundedInputCertificateWire:
    """Wire model of `BoundedInputCertificateWire` (PR #62 v5).

    Three fields: `N` (bound on input domain) + `rawWitnesses` (per-input
    trajectory evidence) + `claim` (FiniteOrbitClaim). Canonical-input
    identity: witness at list index `i` corresponds to input `i + 1`.
    """

    N: int
    rawWitnesses: list[CertWitnessWire]
    claim: FiniteOrbitClaimWire

    def to_dict(self) -> dict:
        return {
            "schemaVersion": SCHEMA_VERSION,
            "claim": self.claim.to_dict(),
            "N": self.N,
            "rawWitnesses": [w.to_dict() for w in self.rawWitnesses],
        }

    def to_json_bytes(self, *, indent: int | None = None) -> bytes:
        """Deterministic JSON emit.

        Default: no whitespace, ASCII-only, insertion-order keys (which
        matches the field declaration order in `to_dict`). With
        `indent=2`: pretty-printed for debugging.

        Determinism is required by the Q5 v5 spec § 4.1 — the Lean
        verifier trusts the bytes emitted by this function (modulo
        structural validation); the producer must not produce
        non-deterministic output.
        """
        if indent is None:
            text = json.dumps(
                self.to_dict(),
                separators=(",", ":"),
                ensure_ascii=True,
                sort_keys=False,
            )
        else:
            text = json.dumps(
                self.to_dict(),
                indent=indent,
                ensure_ascii=True,
                sort_keys=False,
            )
        return text.encode("ascii")


# ===== Trajectory generation =====


def _two_adic_valuation(n: int) -> int:
    """Mirror Lean's `twoAdicValuation (n : Nat) : Nat := n.factorization 2`.

    For non-negative `n`: returns `v_2(n)` (the largest power of 2
    dividing `n`). `v_2(0) = 0` (matches `Nat.factorization`).
    """
    if n < 0:
        raise ValueError("two_adic_valuation requires non-negative integer")
    if n == 0:
        return 0
    exponent = 0
    while n % 2 == 0:
        n //= 2
        exponent += 1
    return exponent


def _accelerated_step_all(n: int) -> int:
    """Mirror Lean's `acceleratedStep (n : Nat) : Nat := (3n + 1) / 2^v_2(3n + 1)`.

    Differs from `accelerated.accelerated_step` (which is restricted to
    positive odd). This version handles ALL positive `n` (including
    even), matching the Lean def exactly. The Python
    `accelerated.accelerated_step` is kept for backwards compat with the
    existing test suite that uses positive-odd inputs only.
    """
    if n <= 0:
        raise ValueError(f"accelerated_step requires positive integer, got {n}")
    succ = 3 * n + 1
    return succ >> _two_adic_valuation(succ)


def build_trajectory(
    start: int,
    claim: FiniteOrbitClaimWire,
    *,
    max_steps: int = 1000,
) -> list[int]:
    """Build the trajectory `[start, acceleratedStep(start), ..., last]`.

    Walks the orbit under `acceleratedStep` (mirrors `accelerated_orbit`)
    until reaching a value `y` with `claim.holds(y)`. Returns the full
    trajectory including `start` and the terminal `y`.

    For `.empty` claims: never terminates within `max_steps` (raises
    RuntimeError). This matches the Lean semantics — `.empty` claims
    cannot be witnessed.

    Raises ValueError on `start <= 0` (canonical-input identity is
    `i + 1` for `i : Fin N`; `0` is not in the domain).
    """
    if start <= 0:
        raise ValueError(f"start must be positive, got {start}")
    trajectory: list[int] = [start]
    current = start
    for _ in range(max_steps):
        if claim.holds(current):
            return trajectory
        current = _accelerated_step_all(current)
        trajectory.append(current)
    raise RuntimeError(
        f"trajectory did not satisfy claim within {max_steps} steps: "
        f"start={start}, claim={claim}"
    )


def build_bounded_input_certificate(
    leaf: CoverageLeaf,
    claim: FiniteOrbitClaimWire,
    N: int,
    *,
    max_steps: int = 1000,
) -> BoundedInputCertificateWire:
    """Build a `BoundedInputCertificateWire` for the given `leaf` + `claim` + `N`.

    For each `x ∈ [1..N]`, builds the trajectory that reaches a
    claim-satisfying terminal value under `acceleratedStep`. Witness at
    list index `i` carries canonical input `i + 1` (type-level identity
    preserved via list position — matches the Lean `certWitness` def
    that reconstructs `CertWitness (i.val + 1)`).

    The `leaf` parameter is stamped onto each witness (all witnesses
    must carry the same leaf — enforced by the Lean checker via
    `w.l = l`). Tree-shape verification is deferred to PR #4
    (integration); this producer only emits the raw data.
    """
    if N <= 0:
        raise ValueError(f"N must be positive, got {N}")
    raw_witnesses: list[CertWitnessWire] = []
    for x in range(1, N + 1):
        trajectory = build_trajectory(x, claim, max_steps=max_steps)
        raw_witnesses.append(CertWitnessWire(leaf=leaf, trajectory=trajectory))
    return BoundedInputCertificateWire(
        N=N, rawWitnesses=raw_witnesses, claim=claim
    )


__all__ = [
    "SCHEMA_VERSION",
    "FiniteOrbitClaimWire",
    "CertWitnessWire",
    "BoundedInputCertificateWire",
    "build_trajectory",
    "build_bounded_input_certificate",
]
