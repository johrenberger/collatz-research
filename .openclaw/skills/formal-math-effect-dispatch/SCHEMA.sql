-- ============================================================================
-- formal-math-effect-dispatch / SCHEMA.sql
-- ============================================================================
-- Design-time schema for the proposed EFFECT_DISPATCH log and PR_REVIEW rows.
-- This repository has no executable formal-math dispatcher or migration runner;
-- do not apply it to the live OpenClaw database as though these contracts were
-- enforced. Validate migrations against an isolated SQLite fixture first.
-- ============================================================================

PRAGMA foreign_keys = ON;
PRAGMA journal_mode = WAL;     -- safe under concurrent dispatcher writes
PRAGMA synchronous  = NORMAL;  -- writer throughput, durable on commit

-- ----------------------------------------------------------------------------
-- dispatch_log: one row per primitive dispatched by EFFECT_DISPATCH
-- ----------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS dispatch_log (
    story_id         TEXT    NOT NULL,
    work_packet_id   TEXT    NOT NULL,
    cycle_index      INTEGER NOT NULL,
    effect_label     TEXT    NOT NULL CHECK (effect_label IN ('deterministic','code_review','op_LLM')),
    primitive        TEXT    NOT NULL,
    parent_state     TEXT,                                      -- controller state (e.g. PR_REVIEW, IMPLEMENT); null for stateless dispatches
    sub_state        TEXT,                                      -- sub-state inside parent (e.g. DISPATCH_REVIEW, RE_VALIDATE)
    ok               INTEGER NOT NULL CHECK (ok IN (0,1)),
    tokens_used      INTEGER,                                   -- null for deterministic
    started_at       TEXT    NOT NULL,                          -- ISO-8601
    finished_at      TEXT,                                      -- ISO-8601
    failure_signature TEXT,                                     -- error identity, not strategy identity
    strategy_id      TEXT,                                      -- only for explicit repair_attempt events
    usage_kind       TEXT NOT NULL DEFAULT 'leaf' CHECK (usage_kind IN ('leaf','aggregate') AND (usage_kind = 'leaf' OR tokens_used IS NULL)),
    data_json        TEXT,                                      -- leaf payload; aggregate usage is informational JSON
    PRIMARY KEY (story_id, work_packet_id, cycle_index, primitive)
);

-- Common query patterns: filter by parent_state, look up by story+time
CREATE INDEX IF NOT EXISTS idx_dispatch_log_parent_state
    ON dispatch_log (parent_state, started_at);

CREATE INDEX IF NOT EXISTS idx_dispatch_log_story_time
    ON dispatch_log (story_id, started_at);

CREATE INDEX IF NOT EXISTS idx_dispatch_log_effect
    ON dispatch_log (effect_label, started_at);

CREATE INDEX IF NOT EXISTS idx_dispatch_log_strategy
    ON dispatch_log (story_id, strategy_id);

-- ----------------------------------------------------------------------------
-- pr_review_round: one row per round of the PR_REVIEW cycle
-- ----------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS pr_review_round (
    story_id          TEXT    NOT NULL,
    -- Review round counts include the initial review; the protocol permits at most
    -- three total rows for a story (default story budget is two).
    round             INTEGER NOT NULL CHECK (round >= 1 AND round <= 3),
    pr_number         INTEGER,
    pr_url            TEXT,
    head_sha          TEXT    NOT NULL,
    reviewer_model    TEXT    NOT NULL,                         -- openai/gpt-6.1-terra; effort=high
    verdict           TEXT    CHECK (verdict IN ('approve','request_changes','comment')),
    findings_json     TEXT,                                     -- JSON array of typed findings
    disposition_json  TEXT,                                     -- JSON array of typed dispositions
    ok                INTEGER NOT NULL CHECK (ok IN (0,1)),
    transition        TEXT    CHECK (transition IN ('HUMAN_MERGE_READY','REVIEW_AGAIN','HUMAN_GATE')),
    created_at        TEXT    NOT NULL,                         -- ISO-8601
    PRIMARY KEY (story_id, round)
);

CREATE INDEX IF NOT EXISTS idx_pr_review_round_story
    ON pr_review_round (story_id, round);

CREATE INDEX IF NOT EXISTS idx_pr_review_round_verdict
    ON pr_review_round (verdict, created_at);

-- ----------------------------------------------------------------------------
-- pr_review_state: one row per story; tracks the running PR_REVIEW state
-- ----------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS pr_review_state (
    story_id          TEXT PRIMARY KEY,
    current_round     INTEGER NOT NULL DEFAULT 0,
    pr_number         INTEGER,
    last_head_sha     TEXT,
    last_verdict      TEXT,
    last_transition   TEXT,
    last_exit_at      TEXT,
    findings_open     INTEGER NOT NULL DEFAULT 0                -- P0/P1 with no remediated disposition
);

-- ----------------------------------------------------------------------------
-- working_state: the typed working memory of the agent (Stage 2 / FAOP χ + FNF-2)
-- ----------------------------------------------------------------------------
-- One row per story. Read on every state entry, written on every state exit
-- and on every hypothesis change. Anti-pattern: re-deriving the working state
-- from the conversation transcript. See formal-math-working-state/SKILL.md.
-- ----------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS working_state (
    story_id                          TEXT PRIMARY KEY,
    work_packet_id                    TEXT,
    current_state                     TEXT,
    current_sub_state                 TEXT,
    state_entered_at                  TEXT,
    state_updated_at                  TEXT,
    checkpoint_count                  INTEGER NOT NULL DEFAULT 0,
    branch                            TEXT,
    base_commit                       TEXT,
    last_green_commit                 TEXT,
    current_head_sha                  TEXT,
    current_hypothesis_json           TEXT,                     -- RepairHypothesis (FNF-2 typed)
    current_strategy_id               TEXT,
    current_strategy_attempt_count    INTEGER NOT NULL DEFAULT 0,
    last_validation_json              TEXT,                     -- ValidationResult (FNF-2 typed)
    last_validation_exit_code         INTEGER,
    current_rcs                       REAL    NOT NULL DEFAULT 0,
    proof_debt_baseline               INTEGER NOT NULL DEFAULT 0,
    proof_debt_current                INTEGER NOT NULL DEFAULT 0,
    trust_boundary_baseline_json      TEXT,                     -- TrustBoundary
    trust_boundary_current_json       TEXT,                     -- TrustBoundary
    review_feedback_json              TEXT                      -- ReviewFeedback
);

CREATE INDEX IF NOT EXISTS idx_working_state_packet
    ON working_state (work_packet_id, current_state);

CREATE INDEX IF NOT EXISTS idx_working_state_updated
    ON working_state (state_updated_at DESC);

-- ----------------------------------------------------------------------------
-- story_budget: per-story cost/time/round/cycle caps (Stage 3 / FAOP +B)
-- ----------------------------------------------------------------------------
-- Declared once at PLAN, optionally overridden per work packet. The dispatcher
-- reads this row on every pre-dispatch check and refuses launches that would
-- push the story over budget. See formal-math-bounds/SKILL.md.
-- ----------------------------------------------------------------------------

CREATE TABLE IF NOT EXISTS story_budget (
    story_id              TEXT PRIMARY KEY,
    max_tokens            INTEGER NOT NULL DEFAULT 40000 CHECK (max_tokens > 0),
    max_wallclock_seconds INTEGER NOT NULL DEFAULT 1800 CHECK (max_wallclock_seconds > 0),
    max_rounds            INTEGER NOT NULL DEFAULT 2 CHECK (max_rounds >= 1 AND max_rounds <= 3),
    max_cycles            INTEGER NOT NULL DEFAULT 8 CHECK (max_cycles >= 1 AND max_cycles <= 8),
    declared_at           TEXT    NOT NULL,
    updated_at            TEXT    NOT NULL,
    notes                 TEXT
);

-- ============================================================================
-- Schema upgrades are not applied here. See `migrations/002_pilot_contracts.sql`;
-- it is a one-time migration for an isolated copy of a legacy schema. There is
-- no runtime migration runner in this repository.
-- ============================================================================

-- ============================================================================
-- Verification queries
-- ============================================================================
-- (1) Full PR_REVIEW timeline for one story:
--
--   SELECT cycle_index, primitive, sub_state, effect_label, ok,
--          tokens_used, started_at, finished_at
--   FROM dispatch_log
--   WHERE story_id = '<STORY_ID>' AND parent_state = 'PR_REVIEW'
--   ORDER BY started_at ASC;
--
-- (2) Round count and exit:
--
--   SELECT MAX(cycle_index) AS final_round,
--          json_extract(data_json, '$.transition_to')      AS exit_to,
--          json_extract(data_json, '$.findings_open_at_exit') AS open_at_exit
--   FROM dispatch_log
--   WHERE story_id = '<STORY_ID>' AND primitive = 'pr_review_exit';
--
-- (3) PR review rounds (typed, separate from dispatch_log):
--
--   SELECT round, pr_number, pr_url, head_sha, verdict, transition, created_at
--   FROM pr_review_round
--   WHERE story_id = '<STORY_ID>'
--   ORDER BY round ASC;
--
-- (4) Open findings at exit (HUMAN_MERGE_READY invariant):
--
--   SELECT story_id, current_round, findings_open, last_transition
--   FROM pr_review_state
--   WHERE findings_open > 0;
--
-- (5) Working-state recovery after context compaction:
--
--   SELECT story_id, work_packet_id, current_state, current_sub_state,
--          state_entered_at, state_updated_at, checkpoint_count,
--          branch, last_green_commit, current_head_sha,
--          current_strategy_id, current_strategy_attempt_count,
--          current_rcs, proof_debt_current, trust_boundary_current_json
--   FROM working_state
--   WHERE story_id = '<STORY_ID>';
--
-- (6) Stories that have not been checkpointed recently (stuck):
--
--   SELECT story_id, current_state, current_sub_state,
--          (julianday('now') - julianday(state_updated_at)) AS days_since_update
--   FROM working_state
--   WHERE julianday(state_updated_at) < julianday('now', '-1 day')
--   ORDER BY state_updated_at ASC;
--
-- (7) Composite bound for a story (FAOP +B):
--
--   SELECT
--       (SELECT COALESCE(SUM(tokens_used), 0) FROM dispatch_log
--         WHERE story_id = ? AND usage_kind = 'leaf' AND tokens_used IS NOT NULL) AS tokens_used,
--       (SELECT COALESCE(SUM(
--           (julianday(finished_at) - julianday(started_at)) * 86400
--         ), 0) FROM dispatch_log
--         WHERE story_id = ? AND usage_kind = 'leaf' AND finished_at IS NOT NULL)      AS wallclock_used,
--       (SELECT COUNT(*) FROM pr_review_round WHERE story_id = ?) AS rounds_used
--   ;
--
-- (8) Story budget remaining:
--
--   SELECT b.story_id,
--          b.max_tokens    - <tokens_used from (7)>    AS tokens_remaining,
--          b.max_wallclock - <wallclock_used from (7)> AS wallclock_remaining,
--          b.max_rounds    - <rounds_used from (7)>    AS rounds_remaining,
--          b.max_cycles    - <cycles_used from working_state> AS cycles_remaining
--   FROM story_budget b WHERE b.story_id = ?;
--
-- (9) Bound violations in a story (refused dispatches):
--
--   SELECT started_at, primitive, parent_state, sub_state,
--          json_extract(data_json, '$.bound')          AS bound,
--          json_extract(data_json, '$.budget_remaining') AS budget_remaining,
--          json_extract(data_json, '$.leaf_c_max')     AS leaf_c_max
--   FROM dispatch_log
--   WHERE story_id = ? AND ok = 0
--     AND json_extract(data_json, '$.bound') IS NOT NULL
--   ORDER BY started_at DESC;
-- ============================================================================
