# Contributing

This repository follows the BDD story backlog in the project charter and the
status vocabulary defined there. Every change is a single story-sized
vertical slice with focused tests, documentation updates, deterministic
commands, and a short evidence note.

## Bootstrap

```sh
# Python 3.12 toolchain resolved by uv automatically.
uv sync --group dev

# Lean toolchain resolved by elan/lake automatically.
lake build
```

After bootstrap, you should be able to run `make ci` cleanly.

## Required commands

The backlog defines the canonical command set. Always invoke via the
top-level `Makefile` targets so local runs and CI use the same surface:

| Target            | Purpose |
|-------------------|---------|
| `make format`     | Apply `ruff format` to Python sources |
| `make format-check` | Verify formatting without modifying files (used by CI) |
| `make lint`       | Run `ruff check` on Python sources |
| `make test`       | Run `pytest` |
| `make lean`       | Build Lean modules via `lake` |
| `make cert-test`  | Run certificate checker (Story 05; placeholder until then) |
| `make reproduce`  | Run the canonical reproduction (smoke + experiment smoke) |
| `make ci`         | Full CI gate: `format-check` + `lint` + `test` + `lean` |
| `make smoke`      | Minimal Python sanity check (no `pytest` deps) |

Replace a command only by updating the backlog and CI in the same change.

## Branch and commit protocol

- Create a branch per story: `story-<NN>-<slug>` (e.g.
  `story-01-repository-hardening`).
- Keep changes within one story. Do not silently bundle unrelated edits.
- Commit subject: `Story <NN>: <title>` (matches the backlog header).
- Body: list the acceptance criteria addressed, the validation commands
  executed, and a one-line evidence note (toolchain version, lockfile
  digest, result).
- Push the branch and open a PR. Codex validates before merge.

## Story workflow

1. Read the relevant story section of the backlog.
2. If the change touches canonical semantics, schema, trust boundary, or
   claim language, write an ADR in `docs/adr/` first and request maintainer
   review before implementation.
3. Implement the acceptance criteria. Add focused tests for each BDD
   criterion.
4. Update `docs/theorem-status.md` for any Lean theorem or definition.
5. Run `make ci` and capture the output.
6. Write the evidence note (toolchain, seed/input digest, commands,
   result) and attach it to the PR.
7. Run the independent Codex PR review gate in
   `docs/codex-pr-review-gate.md`. Record the reviewed full head SHA, review
   URL, round, verdict, and disposition of every P0/P1 finding in the PR.
   A new push requires a new review of the new head before merge.
8. Request maintainer merge authorization only after the reviewed SHA is the
   current head, required CI is green for that SHA, and the Codex gate is
   approved with no unresolved P0/P1 findings.

## Status vocabulary

Use the project's status vocabulary verbatim when describing results:

- **Hypothesis** — untested idea or conjectured invariant.
- **Observed** — finite computational result with recorded metadata.
- **Checked certificate** — finite artifact accepted by its checker
  (checker soundness may still be pending).
- **Formally established** — Lean theorem builds from the pinned toolchain
  without prohibited placeholders.
- **Released claim** — formally established result with reproducibility
  and review record.

Do not elevate an observation or a checked certificate to a formal
theorem in prose or documentation.

## Determinism and provenance

- Pin exact versions in `pyproject.toml` and `uv.lock`. Do not use `>=`
  ranges for runtime or test dependencies.
- Pin the Lean toolchain via `lean-toolchain` and the `lake-manifest.json`
  transitive revisions.
- Persist seeds, inputs, and toolchain versions in experiment manifests.
- Do not commit secrets, generated caches, or bulky transient outputs.

## Code review

Codex is the independent validation authority. Codex may:

- Re-run all gates from a clean state.
- Inspect diffs against the story's acceptance criteria.
- Challenge trust-boundary changes.
- Verify proof status, reproducibility, and schema/test coverage.
- Reject a change that is correct-looking but nonreproducible,
  undertested, or semantically ambiguous.

Maintainers own acceptance of new mathematical claims, schema versions,
dependency additions, and publication language.

The Codex gate is a required independent-review quality gate, not an automatic
merge authority. Maintainers retain final merge authorization.

## License

License selection and contributor policy are intentionally pending
maintainer direction. See `CITATION.cff` for current metadata.
