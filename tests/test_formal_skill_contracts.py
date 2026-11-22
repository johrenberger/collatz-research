from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]
SCHEMA = ROOT / ".openclaw/skills/formal-math-effect-dispatch/SCHEMA.sql"
MIGRATION = ROOT / ".openclaw/skills/formal-math-effect-dispatch/migrations/002_pilot_contracts.sql"


def test_new_schema_defaults_two_rounds_and_caps_at_three(tmp_path: Path) -> None:
    connection = sqlite3.connect(tmp_path / "new-state.sqlite")
    connection.executescript(SCHEMA.read_text(encoding="utf-8"))
    connection.execute(
        "INSERT INTO story_budget (story_id, declared_at, updated_at) VALUES (?, ?, ?)",
        ("default", "now", "now"),
    )
    connection.execute(
        "INSERT INTO story_budget (story_id, max_rounds, declared_at, updated_at) "
        "VALUES (?, ?, ?, ?)",
        ("ceiling", 3, "now", "now"),
    )
    assert connection.execute(
        "SELECT max_rounds FROM story_budget WHERE story_id = 'default'"
    ).fetchone() == (2,)
    with pytest.raises(sqlite3.IntegrityError):
        connection.execute(
            "INSERT INTO story_budget (story_id, max_rounds, declared_at, updated_at) "
            "VALUES (?, ?, ?, ?)",
            ("over-ceiling", 4, "now", "now"),
        )
    connection.close()


def _insert_dispatch_log(
    connection: sqlite3.Connection,
    values: tuple[object, ...],
    extra_column: str,
    extra_value: object,
) -> None:
    columns = (
        "story_id, work_packet_id, cycle_index, effect_label, primitive, ok, "
        "tokens_used, started_at, data_json"
    )
    markers = ", ".join("?" for _ in range(len(values) + 1))
    connection.execute(
        f"INSERT INTO dispatch_log ({columns}, {extra_column}) VALUES ({markers})",
        (*values, extra_value),
    )


def test_aggregate_usage_is_not_double_counted_with_leaf_usage(tmp_path: Path) -> None:
    connection = sqlite3.connect(tmp_path / "usage.sqlite")
    connection.executescript(SCHEMA.read_text(encoding="utf-8"))
    _insert_dispatch_log(
        connection,
        ("story", "packet", 1, "op_LLM", "leaf-a", 1, 10, "now", "{}"),
        "strategy_id",
        "strategy-a",
    )
    _insert_dispatch_log(
        connection,
        ("story", "packet", 1, "deterministic", "par", 1, None, "now", '{"tokens":10}'),
        "usage_kind",
        "aggregate",
    )
    total = connection.execute(
        "SELECT SUM(tokens_used) FROM dispatch_log "
        "WHERE story_id = 'story' AND usage_kind = 'leaf'"
    ).fetchone()
    assert total == (10,)
    with pytest.raises(sqlite3.IntegrityError):
        _insert_dispatch_log(
            connection,
            ("story", "packet", 1, "deterministic", "bad-par", 1, 10, "now", "{}"),
            "usage_kind",
            "aggregate",
        )
    connection.close()


def test_migration_preserves_budget_and_enables_three_round_ceiling(tmp_path: Path) -> None:
    connection = sqlite3.connect(tmp_path / "legacy-state.sqlite")
    connection.executescript(
        """
        CREATE TABLE dispatch_log (
            story_id TEXT NOT NULL,
            work_packet_id TEXT NOT NULL,
            cycle_index INTEGER NOT NULL,
            primitive TEXT NOT NULL,
            tokens_used INTEGER,
            failure_signature TEXT,
            PRIMARY KEY (story_id, work_packet_id, cycle_index, primitive)
        );
        CREATE TABLE story_budget (
            story_id TEXT PRIMARY KEY,
            max_tokens INTEGER NOT NULL DEFAULT 40000,
            max_wallclock_seconds INTEGER NOT NULL DEFAULT 1800,
            max_rounds INTEGER NOT NULL DEFAULT 2 CHECK (max_rounds >= 1 AND max_rounds <= 2),
            max_cycles INTEGER NOT NULL DEFAULT 8,
            declared_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            notes TEXT
        );
        INSERT INTO story_budget (story_id, declared_at, updated_at, notes)
        VALUES ('existing', 'created', 'updated', 'keep me');
        """
    )
    connection.executescript(MIGRATION.read_text(encoding="utf-8"))
    assert connection.execute(
        "SELECT max_rounds, notes FROM story_budget WHERE story_id = 'existing'"
    ).fetchone() == (2, "keep me")
    connection.execute("UPDATE story_budget SET max_rounds = 3 WHERE story_id = 'existing'")
    with pytest.raises(sqlite3.IntegrityError):
        connection.execute("UPDATE story_budget SET max_rounds = 4 WHERE story_id = 'existing'")
    columns = {row[1] for row in connection.execute("PRAGMA table_info(dispatch_log)")}
    assert {"strategy_id", "usage_kind"} <= columns
    connection.close()
