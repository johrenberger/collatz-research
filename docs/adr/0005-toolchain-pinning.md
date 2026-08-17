# ADR 0005: Pin Python and Lean toolchains

Status: accepted.

## Context

Story 01 (Repository hardening and executable baseline) requires that
"a clean supported workstation, when documented bootstrap is run, then
Python dependencies and the pinned Lean toolchain resolve without
undeclared global dependencies." The backlog also forbids broad version
ranges and requires deterministic lockfiles.

The pre-Story-01 state had:

- `requires-python = ">=3.12"` (no upper bound — Python 3.13+ would silently
  satisfy the constraint).
- `pyproject.toml` build and dev dependencies specified with `>=` minimal
  ranges (no upper bound).
- No `uv.lock` committed.
- `lean-toolchain` pinned to `leanprover/lean4:v4.19.0` with `lake-manifest.json`
  locking transitive revisions — the Lean side was already correct.

  *Updated 2026-08-17:* bumped to `leanprover/lean4:v4.33.0` via PR #32
  (Story 08, merge commit `98831ae`). The bump itself was driven by the
  spec doc `docs/story-08-toolchain-bump.md` which records the
  rationale, the iterative commit sequence, and the Phase 2 source
  adaptations. `lake-manifest.json` revs were updated to match Mathlib
  v4.33.0's own manifest; toolchain-keyed `.olean` caches were
  invalidated for the cold build. The pin-decision discipline
  ("toolchain updates require their own story") is preserved: this ADR
  is the post-hoc update, and Story 08 + PR #32 are the bump-record.

## Decision

- **Python interpreter:** pin to `3.12.x`. `pyproject.toml` declares
  `requires-python = ">=3.12,<3.13"`. The interpreter is resolved by
  `uv` itself; no system Python is required.
- **Python build backend:** `hatchling==1.26.3`.
- **Python runtime/dev dependencies:** exact pins for all packages
  declared in `[dependency-groups].dev`:
  - `pytest==8.3.4`
  - `jsonschema==4.23.0`
  - `ruff==0.8.6`
- **`uv.lock`** is committed and verified with `uv sync --frozen`.
  Lockfile-driven bootstrap reproduces the same environment on every
  supported workstation.
- **Lean toolchain:** `leanprover/lean4:v4.33.0` via `lean-toolchain`,
  with transitive revisions locked in `lake-manifest.json`. `lake build`
  uses the locked manifest without an implicit `lake update`. (Was
  `v4.19.0`; bumped 2026-08-17 via PR #32 — see Story 08 spec doc.)
- **Toolchain version policy:** toolchain updates require their own
  story (or an explicit ADR-driven change to this decision). They are
  never incidental.

## Consequences

- A clean clone runs `uv sync --group dev && lake build` and produces a
  reproducible environment.
- Toolchain drift cannot silently change behaviour; any upgrade produces
  a diff in `uv.lock` or `lake-manifest.json` and is reviewable.
- Failing-version tests in `tests/test_toolchain.py` assert the
  interpreter version is 3.12.x and the `pyproject.toml`/`lean-toolchain`
  files still match the pinned string.
- The Makefile's `make ci` aggregator runs `format-check`, `lint`, `test`,
  and `lake build` in sequence. CI workflows route through `make ci`
  rather than direct commands, so the documented surface and the CI
  surface are identical.

## Note on the Python version pin

Choosing `3.12.x` (rather than `3.13.x` or a wider range) is consistent
with the project's "small trusted core" principle and the Ubuntu CI
baseline. Python 3.12 is the LTS-style stable target supported by
`uv`, `ruff`, and `jsonschema` as of the decision date. Promoting to
3.13.x requires its own ADR and a Story to update the lockfile and
`requires-python` in the same change.
