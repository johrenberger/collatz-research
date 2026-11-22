from __future__ import annotations

import sys
from pathlib import Path
from subprocess import CompletedProcess, TimeoutExpired
from unittest.mock import patch

SCRIPTS = Path(__file__).parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))

import full_validate  # noqa: E402


def test_full_gate_runs_ci_once_and_retains_complete_log(tmp_path: Path, capsys) -> None:
    result = CompletedProcess(args=["make", "ci"], returncode=0, stdout="all green\n", stderr="")
    with (
        patch.object(full_validate.shutil, "which", return_value="/usr/bin/make"),
        patch.object(full_validate.subprocess, "run", return_value=result) as run,
    ):
        assert full_validate.main(["--log-dir", str(tmp_path)]) == 0

    run.assert_called_once()
    assert run.call_args.args[0] == ["/usr/bin/make", "ci"]
    assert (tmp_path / "make-ci.log").read_text(encoding="utf-8") == "all green\n"
    assert "PASS make ci" in capsys.readouterr().out


def test_full_gate_fails_closed_and_does_not_retry(tmp_path: Path, capsys) -> None:
    result = CompletedProcess(args=["make", "ci"], returncode=9, stdout="failed\n", stderr="")
    with (
        patch.object(full_validate.shutil, "which", return_value="/usr/bin/make"),
        patch.object(full_validate.subprocess, "run", return_value=result) as run,
    ):
        assert full_validate.main(["--log-dir", str(tmp_path)]) == 9

    run.assert_called_once()
    assert "failed\n" in (tmp_path / "make-ci.log").read_text(encoding="utf-8")
    assert "FAIL make ci exit=9" in capsys.readouterr().out


def test_full_gate_timeout_is_failure_and_preserves_partial_output(tmp_path: Path, capsys) -> None:
    timeout = TimeoutExpired(["make", "ci"], 5, output="partial", stderr="stderr")
    with (
        patch.object(full_validate.shutil, "which", return_value="/usr/bin/make"),
        patch.object(full_validate.subprocess, "run", side_effect=timeout) as run,
    ):
        assert full_validate.main(["--log-dir", str(tmp_path), "--timeout-seconds", "5"]) == 124

    run.assert_called_once()
    assert (tmp_path / "make-ci.log").read_text(encoding="utf-8") == "partialstderr"
    assert "timed out after 5s" in capsys.readouterr().out


def test_full_gate_requires_make(tmp_path: Path, capsys) -> None:
    with (
        patch.object(full_validate.shutil, "which", return_value=None),
        patch.object(full_validate.subprocess, "run") as run,
    ):
        assert full_validate.main(["--log-dir", str(tmp_path)]) == 127

    run.assert_not_called()
    assert "no gate ran" in capsys.readouterr().out


def test_cert_test_is_covered_by_the_full_pytest_gate() -> None:
    root = Path(__file__).parents[1]
    makefile = (root / "Makefile").read_text(encoding="utf-8")
    config = (root / "pyproject.toml").read_text(encoding="utf-8")

    assert "ci: format-check lint test lean axiom-audit" in makefile
    assert "test:\n\tuv run pytest" in makefile
    assert (
        "cert-test:\n\tuv run pytest tests/test_checker.py tests/test_checker_lean.py" in makefile
    )
    assert 'testpaths = ["tests"]' in config
    assert (root / "tests/test_checker.py").is_file()
    assert (root / "tests/test_checker_lean.py").is_file()
