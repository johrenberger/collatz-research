"""Differential tests: Python implementations against the canonical test vectors.

The test vectors in `docs/test-vectors.json` are the single source of truth
for expected outputs. They are the contract that the Lean counterpart
(`CollatzResearch.Dynamics`) is also expected to satisfy; a future Story
will run the Lean executable and assert equality against these vectors.
"""

import json
from pathlib import Path

from collatz_research.accelerated import accelerated_step, two_adic_valuation
from collatz_research.standard import standard_step

VECTORS_PATH = Path(__file__).parent.parent / "docs" / "test-vectors.json"


def _load_vectors() -> dict:
    with VECTORS_PATH.open() as f:
        return json.load(f)


def test_two_adic_vectors() -> None:
    data = _load_vectors()
    for entry in data["two_adic"]:
        assert two_adic_valuation(entry["input"]) == entry["expected"], entry


def test_accelerated_outputs() -> None:
    data = _load_vectors()
    for vec in data["vectors"]:
        assert accelerated_step(vec["input"]) == vec["accelerated_output"], vec["name"]


def test_standard_next_steps() -> None:
    data = _load_vectors()
    for vec in data["vectors"]:
        assert standard_step(vec["input"]) == vec["standard_next"], vec["name"]


def test_standard_trajectories() -> None:
    data = _load_vectors()
    for vec in data["vectors"]:
        if "standard_trajectory_to_1" not in vec:
            continue
        trajectory = [vec["input"]]
        for _ in range(vec["standard_steps_to_1"]):
            trajectory.append(standard_step(trajectory[-1]))
        assert trajectory == vec["standard_trajectory_to_1"], vec["name"]


def test_accelerated_trajectories() -> None:
    data = _load_vectors()
    for vec in data["vectors"]:
        if "accelerated_trajectory_to_1" not in vec:
            continue
        trajectory = [vec["input"]]
        for _ in range(vec["accelerated_steps_to_1"]):
            trajectory.append(accelerated_step(trajectory[-1]))
        assert trajectory == vec["accelerated_trajectory_to_1"], vec["name"]
