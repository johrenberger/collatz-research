import importlib.util
from pathlib import Path

_SCRIPT = Path(__file__).parents[1] / "scripts" / "ci_status.py"
_SPEC = importlib.util.spec_from_file_location("ci_status", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)
is_terminal = _MODULE.is_terminal
summarize_runs = _MODULE.summarize_runs


def test_summarize_uses_newest_run_per_workflow() -> None:
    summary = summarize_runs(
        [
            {
                "name": "Lean CI",
                "created_at": "2026-08-14T01:00:00Z",
                "status": "completed",
                "conclusion": "failure",
                "id": 1,
            },
            {
                "name": "Lean CI",
                "created_at": "2026-08-14T02:00:00Z",
                "status": "completed",
                "conclusion": "success",
                "id": 2,
            },
            {
                "name": "Python CI",
                "created_at": "2026-08-14T02:00:00Z",
                "status": "in_progress",
                "conclusion": None,
                "id": 3,
            },
        ]
    )
    assert [run["run_id"] for run in summary] == [2, 3]
    assert not is_terminal(summary)


def test_terminal_requires_at_least_one_completed_run() -> None:
    assert not is_terminal([])
    assert is_terminal([{"status": "completed"}])
