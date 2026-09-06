.PHONY: help format format-check lint test lean cert-test reproduce ci smoke clean check

# Default: print help.
help:
	@echo "Targets:"
	@echo "  format        — apply ruff format to Python sources"
	@echo "  format-check  — verify Python formatting without modifying files"
	@echo "  lint          — run ruff lint on Python sources"
	@echo "  test          — run pytest"
	@echo "  lean          — build Lean modules via lake"
	@echo "  cert-test     — run certificate checker (placeholder; Story 05)"
	@echo "  reproduce     — run canonical reproduction (smoke + experiment smoke)"
	@echo "  ci            — full CI gate (format-check + lint + test + lean)"
	@echo "  smoke         — minimal Python dependency-free sanity check"
	@echo "  clean         — remove local cache directories"

# Apply ruff format to all Python sources.
format:
	uv run ruff format .

# Verify formatting without changing files. Used by CI.
format-check:
	uv run ruff format --check .

# Lint Python sources.
lint:
	uv run ruff check .

# Run the Python test suite.
test:
	uv run pytest

# Build Lean via lake. Uses the locked manifest in lake-manifest.json.
lean:
	lake build

cert-test:
	uv run pytest tests/test_checker.py tests/test_checker_lean.py

# Canonical reproduction command. Runs the Python smoke check and the
# experiment smoke. After Story 09 lands, this will also regenerate canonical
# experiment artifacts.
reproduce: smoke
	uv run python scripts/check.py

# CI aggregator. Formatting, lint, Python tests, and Lean build.
# Per backlog: "make ci runs, then formatting, lint, Python tests, and lake build pass."
ci: format-check lint test lean

# Python-only CI gate (no Lean build). Used by python-ci.yml to keep the
# Python gate fast; the Lean gate is owned by lean-ci.yml.
python-ci: format-check lint test

# Lightweight sanity check used by the reproducibility workflow.
smoke:
	uv run python scripts/check.py

# Remove local cache directories. Non-destructive to source.
clean:
	rm -rf .pytest_cache .ruff_cache

# Backwards-compatible alias for `ci`. The backlog uses `make ci`.
check: ci
