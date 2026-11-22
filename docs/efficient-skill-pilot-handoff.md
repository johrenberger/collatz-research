# EfficientSkill pilot handoff

## Starting point and scope

Base: `e2a8ebae78f4039c0650f0723a23c10002212fd0` on `feature/r03-descent-to-convergence`. Run this pilot in an isolated checkout and isolated OpenClaw state. Use GPT-6-Luna as the controller where available; retain the repository-mandated independent reviewer model and effort. Do not publish reviews, push, or merge as part of replay.

The desktop pilot made no skill or runtime changes. On Windows, `tests/test_agent_lifecycle.py` plus the extractor tests passed (21 tests). A broader run of lifecycle, review-gate and reviewer-resume tests passed 40 and failed 12; the failures involved Unix-style fake executables on Windows. Re-run on the supported OpenClaw host before treating these as baseline outcomes. No live token, latency, or accuracy measurements were obtained.

## Execute the pilot

1. Record the checkout SHA, runtime version, model routes, pricing, enabled skills, and relevant configuration. Inspect repository instructions and establish a clean baseline. Do not use production state or perform external mutations during replay.
2. Build a representative set of historical work packets and failure cases, split by story into development, validation, and sealed holdout sets. Include Lean and Python validation, interrupted recovery, repeated and distinct strategies, exhausted budgets, stale review SHA, review-session resumption, and unrelated dirty files. Save replay fixtures without secrets. Record the sample size and exclusions.
3. Replay the unchanged baseline with the same task snapshots, model configuration, limits, and verifier for each variant. Collect per-episode input, cached-input, output and available reasoning tokens for controller and reviewer, billed cost, tool calls, elapsed time, outcome, and failure category. Record unavailable metrics as unavailable. Capture exact gate evidence and raw logs outside model context.
4. Prepare and evaluate variants sequentially: (A) baseline; (B) policy consistency fixes; (C) B plus executable helper and validation changes; (D) C plus concise operational skill instructions. Keep each variant reproducible as a separate commit or patch. Use development failures for iteration, validation for selection, and the holdout only once after selection. Re-run on multiple seeds if the runtime permits.

## Candidate changes

- Reconcile review-round rules: workflow/bounds default to two, review protocol permits three, and schema caps the budget at two while allowing three review rows. Define counting and default versus ceiling explicitly; do not weaken the repository review protocol. Reconcile reviewer model and continuation instructions with `scripts/dispatch_codex_pr_review.py` and `docs/codex-pr-review-gate.md`.
- Replace `FULL_VALIDATE.v1`'s duplicate component commands with a tested executable final gate. `make ci` already runs format, lint, tests, Lean and axiom audit. Preserve explicit `cert-test` unless coverage is verified; use realistic timeouts and fail closed on any failure. Keep narrow checks during repair.
- Audit actual state/dispatch implementation before claiming enforcement. Reuse the lifecycle ledger where appropriate; preserve cumulative budget and strategy history after recovery. Avoid double counting parallel aggregate and leaf usage. Distinguish strategy identity from normalized error identity.
- Keep compact exact Lean goals, local hypotheses, types, relevant source and a full-log pointer available for diagnosis. Keep proof debt, trust-boundary, exact-head review, CI and human-merge requirements intact.
- Move repeated deterministic work to tested helpers and shorten operational instructions only after the anchor works. Do not treat shell commands as equivalent solely because an extractor sorts, lowercases or deduplicates their lines.

## Acceptance and reporting

Reject a candidate for any false merge-ready decision, unapproved proof or trust change, missing required validation, lost recovery evidence, or observed completion regression. Treat zero observed failures as bounded evidence, not proof of zero risk. Target a 20% reduction in total tokens per successfully validated packet without p95 latency regression; these are pilot targets, not established results. Report raw counts and denominators, uncertainty, per-model costs, and p50/p95 only when sample sizes support them. Do not transfer the paper's 90% accuracy floor to formal correctness gates.

Run focused regression tests and the applicable full repository gates on every selected variant. Record commands, outcomes, evidence paths, differences from baseline, limitations, and the selected commit. If the runtime, fixture set, or metrics are unavailable, report the pilot as blocked or partial; do not infer savings from shorter Markdown. Preserve all independent review and human authorization requirements.
