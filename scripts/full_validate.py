#!/usr/bin/env python3
"""Run the repository's final CI gate once, retaining raw output outside stdout."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path


def _captured_text(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def _run_ci(make: str, repo_root: Path, log_path: Path, timeout_seconds: int) -> int:
    command = [make, "ci"]
    try:
        result = subprocess.run(
            command,
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as error:
        log_path.write_text(
            _captured_text(error.stdout) + _captured_text(error.stderr), encoding="utf-8"
        )
        print(f"FAIL make ci timed out after {timeout_seconds}s; log={log_path}")
        return 124
    except OSError as error:
        log_path.write_text(f"failed to start make ci: {error}\n", encoding="utf-8")
        print(f"FAIL make ci could not start; log={log_path}")
        return 127

    log_path.write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        print(f"FAIL make ci exit={result.returncode}; log={log_path}")
        return result.returncode
    print(f"PASS make ci; log={log_path}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-dir", type=Path, help="directory for complete gate logs")
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    args = parser.parse_args(argv)
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")

    repo_root = Path(__file__).resolve().parents[1]
    log_dir = args.log_dir or Path(tempfile.mkdtemp(prefix="collatz-full-validate-"))
    log_dir.mkdir(parents=True, exist_ok=True)
    make_name = os.environ.get("MAKE", "make")
    make = shutil.which(make_name)
    if make is None:
        print(f"FAIL make executable not found ({make_name!r}); no gate ran")
        return 127

    # `make ci` includes `make test`, whose pytest discovery includes both files
    # named by `make cert-test`; an additional cert-test invocation is redundant.
    return _run_ci(make, repo_root, log_dir / "make-ci.log", args.timeout_seconds)


if __name__ == "__main__":
    sys.exit(main())
