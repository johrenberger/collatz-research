"""BDD tests for the Q5 PR #3 bounded-input certificate producer.

Trust boundary: this is the producer-side. Producer is UNTRUSTED;
only the Lean verifier + soundness theorem need to be trusted.

These tests pin the producer-side contract:
  - `BoundedInputCertificateWire` round-trips through deterministic JSON.
  - Trajectories emitted under `acceleratedStep` (Lean's def) match the
    PR #62 v5 expected scenarios (A, D, E).
  - JSON shape conforms to `schemas/bounded-input-certificate-v1.json`.

Lean-side rejection tests (malformed JSON, wrong schemaVersion,
missing fields, etc.) live in
`Lean/CollatzResearch/BoundedInputCertificateParserTests.lean` (the
Q5 PR #3 parser tests).

Test convention (per BDD Discipline note in MEMORY.md): these are
local Python tests run via `uv run pytest`; Lean tests run only in
GitHub CI.
"""

from __future__ import annotations

import json
import pathlib

import pytest
from collatz_research.bounded_input_certificate import (
    SCHEMA_VERSION,
    BoundedInputCertificateWire,
    CertWitnessWire,
    FiniteOrbitClaimWire,
    build_bounded_input_certificate,
    build_trajectory,
)
from collatz_research.tree import CoverageLeaf
from jsonschema import Draft202012Validator

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
SCHEMA_PATH = REPO_ROOT / "schemas" / "bounded-input-certificate-v1.json"


# Single-leaf fixture matching PR #62 v5's `singleLeafTree`:
#   { root := .leaf { leafId := "L", leafProperty := "0:0-0" },
#     leaves := [{ leafId := "L", leafProperty := "0:0-0" }],
#     maxDepth := 1 }
# Tree-shape verification is PR #4's job; this producer only stamps
# the leaf onto each witness.
SINGLE_LEAF = CoverageLeaf(leaf_id="L", leaf_property="0:0-0")


def _load_schema() -> dict:
    return json.loads(SCHEMA_PATH.read_text())


# ===== Schema conformance =====


class TestSchemaConformance:
    """The producer's JSON output conforms to schemas/bounded-input-certificate-v1.json."""

    def test_schema_version_constant_is_1_0(self):
        assert SCHEMA_VERSION == "1.0"

    def test_empty_claim_matches_schema(self):
        wire = BoundedInputCertificateWire(
            N=1,
            rawWitnesses=[CertWitnessWire(SINGLE_LEAF, [1])],
            claim=FiniteOrbitClaimWire.empty(),
        )
        Draft202012Validator(_load_schema()).validate(wire.to_dict())

    def test_singleton_claim_matches_schema(self):
        wire = BoundedInputCertificateWire(
            N=2,
            rawWitnesses=[
                CertWitnessWire(SINGLE_LEAF, [1]),
                CertWitnessWire(SINGLE_LEAF, [2, 1]),
            ],
            claim=FiniteOrbitClaimWire.singleton(1),
        )
        Draft202012Validator(_load_schema()).validate(wire.to_dict())

    def test_bounded_claim_matches_schema(self):
        wire = BoundedInputCertificateWire(
            N=2,
            rawWitnesses=[
                CertWitnessWire(SINGLE_LEAF, [1]),
                CertWitnessWire(SINGLE_LEAF, [2, 1]),
            ],
            claim=FiniteOrbitClaimWire.bounded(2),
        )
        Draft202012Validator(_load_schema()).validate(wire.to_dict())

    def test_full_emitted_bytes_validate_against_schema(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=3)
        Draft202012Validator(_load_schema()).validate(json.loads(wire.to_json_bytes()))


# ===== Deterministic emit =====


class TestDeterministicEmit:
    """Same input → same bytes (per Q5 v5 spec § 4.1 determinism requirement)."""

    def test_emit_is_byte_stable(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=2)
        assert wire.to_json_bytes() == wire.to_json_bytes()

    def test_emit_no_whitespace_default(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=1)
        text = wire.to_json_bytes().decode("ascii")
        assert " " not in text
        assert "\n" not in text
        assert "\t" not in text

    def test_emit_ascii_only(self):
        claim = FiniteOrbitClaimWire.bounded(2)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=2)
        wire.to_json_bytes().decode("ascii")  # raises if not ASCII

    def test_pretty_print_is_human_readable(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=1)
        pretty = wire.to_json_bytes(indent=2).decode("ascii")
        assert "\n" in pretty
        # Pretty form also validates against the schema.
        Draft202012Validator(_load_schema()).validate(json.loads(pretty))


# ===== Trajectory correctness =====


class TestTrajectory:
    """Trajectories emitted under Lean's `acceleratedStep` def."""

    def test_x_1_singleton_1(self):
        # accelerated_orbit 1 0 = 1; claim.Holds 1 = True.
        traj = build_trajectory(1, FiniteOrbitClaimWire.singleton(1))
        assert traj == [1]

    def test_x_2_singleton_1(self):
        # acceleratedStep 2 = 7 (since 3*2+1 = 7, v2(7) = 0, 7/1 = 7).
        traj = build_trajectory(2, FiniteOrbitClaimWire.singleton(1))
        assert traj[0] == 2
        assert traj[-1] == 1
        # Sanity: each step is acceleratedStep of the previous.
        self._assert_accelerated_steps(traj)

    def test_x_3_singleton_1(self):
        # 3 → 5 → 1 (acceleratedStep 3 = 5, acceleratedStep 5 = 1).
        traj = build_trajectory(3, FiniteOrbitClaimWire.singleton(1))
        assert traj == [3, 5, 1]

    def test_x_5_singleton_1(self):
        # acceleratedStep 5 = 1 (3*5+1 = 16, v2(16) = 4, 16/16 = 1).
        traj = build_trajectory(5, FiniteOrbitClaimWire.singleton(1))
        assert traj == [5, 1]

    def test_x_7_singleton_1_matches_pr62_narrative(self):
        # 7 → 11 → 17 → 13 → 5 → 1 (matches PR #62 v5 narrative).
        traj = build_trajectory(7, FiniteOrbitClaimWire.singleton(1))
        assert traj == [7, 11, 17, 13, 5, 1]

    def test_empty_claim_does_not_terminate(self):
        with pytest.raises(RuntimeError, match="did not satisfy claim"):
            build_trajectory(1, FiniteOrbitClaimWire.empty(), max_steps=10)

    def test_zero_start_rejected(self):
        with pytest.raises(ValueError, match="start must be positive"):
            build_trajectory(0, FiniteOrbitClaimWire.singleton(1))

    def test_negative_start_rejected(self):
        with pytest.raises(ValueError, match="start must be positive"):
            build_trajectory(-1, FiniteOrbitClaimWire.singleton(1))

    def test_bounded_2_satisfies_immediately_at_1(self):
        # .bounded 2 holds for any y ≤ 2; x=1 satisfies immediately.
        traj = build_trajectory(1, FiniteOrbitClaimWire.bounded(2))
        assert traj == [1]

    def test_singleton_n_zero_rejected(self):
        with pytest.raises(ValueError, match="singleton claim requires n >= 1"):
            FiniteOrbitClaimWire.singleton(0)

    def test_bounded_K_zero_rejected(self):
        with pytest.raises(ValueError, match="bounded claim requires K >= 1"):
            FiniteOrbitClaimWire.bounded(0)

    @staticmethod
    def _assert_accelerated_steps(traj: list[int]) -> None:
        """Verify each consecutive pair (a, b) satisfies b = (3a+1) / 2^v2(3a+1)."""
        for a, b in zip(traj, traj[1:], strict=False):
            succ = 3 * a + 1
            v2 = 0
            n = succ
            while n % 2 == 0:
                n //= 2
                v2 += 1
            assert b == succ >> v2, (
                f"trajectory step {a} → {b} is not acceleratedStep "
                f"(3*{a}+1={succ}, v2={v2}, expected {succ >> v2})"
            )


# ===== Producer integration (matches PR #62 v5 scenarios) =====


class TestProducerIntegration:
    """The producer emits trajectories that match PR #62 v5's 8 scenarios."""

    def test_singleton_1_N_1_matches_pr62_scenario_A(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=1)
        assert wire.N == 1
        assert len(wire.rawWitnesses) == 1
        assert wire.rawWitnesses[0].trajectory == [1]

    def test_singleton_1_N_2_matches_pr62_scenario_D(self):
        """PR #62 v5 scenario D: rawWitnesses[1] (canonical input 2)
        has trajectory [2, 7, 11, 17, 13, 5, 1]."""
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=2)
        assert wire.N == 2
        assert wire.rawWitnesses[0].trajectory == [1]
        assert wire.rawWitnesses[1].trajectory == [2, 7, 11, 17, 13, 5, 1]

    def test_singleton_1_N_3_matches_pr62_scenario_E(self):
        """PR #62 v5 scenario E: rawWitnesses[2] (canonical input 3)
        has trajectory [3, 5, 1]."""
        claim = FiniteOrbitClaimWire.singleton(1)
        wire = build_bounded_input_certificate(SINGLE_LEAF, claim, N=3)
        assert wire.N == 3
        assert wire.rawWitnesses[0].trajectory == [1]
        assert wire.rawWitnesses[1].trajectory == [2, 7, 11, 17, 13, 5, 1]
        assert wire.rawWitnesses[2].trajectory == [3, 5, 1]

    def test_zero_N_rejected(self):
        with pytest.raises(ValueError, match="N must be positive"):
            build_bounded_input_certificate(SINGLE_LEAF, FiniteOrbitClaimWire.singleton(1), N=0)


# ===== Round-trip =====


class TestRoundTrip:
    """emit → parse → reconstruct equals original."""

    def test_roundtrip_singleton_1_N_3(self):
        claim = FiniteOrbitClaimWire.singleton(1)
        original = build_bounded_input_certificate(SINGLE_LEAF, claim, N=3)
        text = original.to_json_bytes().decode("ascii")
        parsed = json.loads(text)

        # Reconstruct the claim.
        p_claim = parsed["claim"]
        if p_claim["type"] == "empty":
            c: FiniteOrbitClaimWire = FiniteOrbitClaimWire.empty()
        elif p_claim["type"] == "singleton":
            c = FiniteOrbitClaimWire.singleton(p_claim["n"])
        elif p_claim["type"] == "bounded":
            c = FiniteOrbitClaimWire.bounded(p_claim["K"])
        else:
            pytest.fail(f"unexpected claim type: {p_claim['type']!r}")

        # Reconstruct the raw witnesses.
        raw_witnesses = [
            CertWitnessWire(
                leaf=CoverageLeaf(
                    leaf_id=w["l"]["leafId"],
                    leaf_property=w["l"]["leafProperty"],
                ),
                trajectory=w["trajectory"],
            )
            for w in parsed["rawWitnesses"]
        ]

        reconstructed = BoundedInputCertificateWire(
            N=parsed["N"], rawWitnesses=raw_witnesses, claim=c
        )

        assert reconstructed.N == original.N
        assert reconstructed.claim == original.claim
        assert len(reconstructed.rawWitnesses) == len(original.rawWitnesses)
        for a, b in zip(reconstructed.rawWitnesses, original.rawWitnesses, strict=False):
            assert a.leaf == b.leaf
            assert a.trajectory == b.trajectory

    def test_roundtrip_bounded_2_N_2(self):
        claim = FiniteOrbitClaimWire.bounded(2)
        original = build_bounded_input_certificate(SINGLE_LEAF, claim, N=2)
        text = original.to_json_bytes().decode("ascii")
        parsed = json.loads(text)
        # .bounded 2 ⟹ trajectory is just [start] (claim holds immediately).
        # Each x ∈ [1, 2] satisfies y ≤ 2 immediately.
        assert parsed["N"] == 2
        assert parsed["rawWitnesses"][0]["trajectory"] == [1]
        assert parsed["rawWitnesses"][1]["trajectory"] == [2]
