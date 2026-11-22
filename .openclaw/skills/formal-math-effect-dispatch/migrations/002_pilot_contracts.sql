-- One-time upgrade for an isolated copy of the original pilot schema.
-- Do not run against production state: this repository has no formal-math
-- runtime or version-aware migration runner.
BEGIN IMMEDIATE;

ALTER TABLE dispatch_log ADD COLUMN strategy_id TEXT;
ALTER TABLE dispatch_log ADD COLUMN usage_kind TEXT NOT NULL DEFAULT 'leaf'
    CHECK (usage_kind IN ('leaf', 'aggregate') AND (usage_kind = 'leaf' OR tokens_used IS NULL));
CREATE INDEX IF NOT EXISTS idx_dispatch_log_strategy
    ON dispatch_log (story_id, strategy_id);

CREATE TABLE story_budget_new (
    story_id              TEXT PRIMARY KEY,
    max_tokens            INTEGER NOT NULL DEFAULT 40000 CHECK (max_tokens > 0),
    max_wallclock_seconds INTEGER NOT NULL DEFAULT 1800 CHECK (max_wallclock_seconds > 0),
    max_rounds            INTEGER NOT NULL DEFAULT 2 CHECK (max_rounds >= 1 AND max_rounds <= 3),
    max_cycles            INTEGER NOT NULL DEFAULT 8 CHECK (max_cycles >= 1 AND max_cycles <= 8),
    declared_at           TEXT NOT NULL,
    updated_at            TEXT NOT NULL,
    notes                 TEXT
);

INSERT INTO story_budget_new (
    story_id, max_tokens, max_wallclock_seconds, max_rounds, max_cycles,
    declared_at, updated_at, notes
)
SELECT
    story_id, max_tokens, max_wallclock_seconds, max_rounds, max_cycles,
    declared_at, updated_at, notes
FROM story_budget;

DROP TABLE story_budget;
ALTER TABLE story_budget_new RENAME TO story_budget;
COMMIT;
