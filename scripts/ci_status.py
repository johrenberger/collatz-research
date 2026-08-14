#!/usr/bin/env python3
"""Poll GitHub Actions runs by commit SHA without the Checks API permission.

This uses the Actions runs endpoint, which is useful when `gh pr checks`
cannot read check-runs. It is a polling fallback, not a replacement for branch
protection or a GitHub App with `checks: read`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections.abc import Iterable
from typing import Any


def summarize_runs(runs: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return newest run per workflow, ordered by workflow name."""
    newest: dict[str, dict[str, Any]] = {}
    for run in runs:
        name = str(run.get("name", "unnamed"))
        current = newest.get(name)
        if current is None or str(run.get("created_at", "")) > str(current.get("created_at", "")):
            newest[name] = {
                "name": name,
                "status": run.get("status"),
                "conclusion": run.get("conclusion"),
                "url": run.get("html_url"),
                "run_id": run.get("id"),
            }
    return [newest[name] for name in sorted(newest)]


def fetch_runs(repo: str, sha: str) -> list[dict[str, Any]]:
    endpoint = f"repos/{repo}/actions/runs?head_sha={sha}&per_page=100"
    raw = subprocess.check_output(["gh", "api", endpoint], text=True)
    return json.loads(raw).get("workflow_runs", [])


def is_terminal(summary: list[dict[str, Any]]) -> bool:
    return bool(summary) and all(run["status"] == "completed" for run in summary)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="owner/repository")
    parser.add_argument("--sha", required=True, help="full commit SHA")
    parser.add_argument("--watch", action="store_true")
    parser.add_argument("--interval", type=float, default=20)
    args = parser.parse_args()
    while True:
        summary = summarize_runs(fetch_runs(args.repo, args.sha))
        print(json.dumps({"repo": args.repo, "sha": args.sha, "runs": summary}, sort_keys=True))
        if not args.watch or is_terminal(summary):
            return 0
        time.sleep(args.interval)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        raise SystemExit(2) from None
