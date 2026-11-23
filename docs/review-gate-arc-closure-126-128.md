# Review-gate arc closure — PRs #122, #124, #125, #126, #127, #128

**Status:** The arc's per-finding verification is complete and every finding is
RESOLVED in the final tree. The one **published** closing review that the
protocol asks for has **not** been obtained: the mandated reviewer route
(`openai/gpt-6.1-terra` at `high`) cannot start while the OpenAI provider fails
to authenticate. That gap is recorded below and in the disposition comment on
each pull request, not papered over.

**Arc:** PRs #122, #124, #125, #126, #127, #128 — the review-gate arc that
introduced the published-review requirement, the mandated reviewer route, the
transitive-axiom audit, and the R02 standard-map bridge.

**First merged:** #122 (`37499293`, 2026-11-14T01:21:22Z).
**Arc final tree:** #128 (`c28174cd`, 2026-11-19T00:36:57Z).
**Verified against:** `main` at `f56f25ea` (2026-11-23).

## Why this record exists

`docs/codex-pr-review-gate.md` and the `collatz-pr-review-gate` skill (step 11)
require a multi-PR arc to close with two things:

1. an evidence-backed **disposition comment on each affected PR** naming where
   its finding landed; and
2. **one** closing verification that checks the union of every finding raised
   across the arc against the final tree — a per-PR diff cannot do this, because
   each finding was reported against a different PR head.

The merge of #128 was detected on 2026-11-19 and handed back for that close
(`state/collatz-research/review-gate/arc-close-ready.json`). The close was not
performed. Part (1) is now done: PRs #122, #124, #125, #126, #127 and #128 each
carry a disposition comment. This record is part (2).

## The eight findings, each checked against the final tree

| # | PR | Severity | Finding | Landed in | Where it is now | Status |
|---|---|---|---|---|---|---|
| 1 | #126 r1 | P1 | `record-review-posting` accepted caller-supplied JSON after only a superficial URL-prefix check, so an approval could be fabricated with no real published review | `9a3f895` | `scripts/pr_review_evidence.py` + `scripts/agent_lifecycle.py`; regression `test_posting_evidence_without_a_published_review_is_refused` at `tests/test_pr_review_gate.py:370` | **RESOLVED** |
| 2 | #126 r1 | P2 | review fetching did not paginate, so a valid review beyond the first 100 was invisible | `9a3f895` | `scripts/pr_review_evidence.py:278` (`fetch_reviews`, `per_page` at `:281`, the pagination note at `:286`) | **RESOLVED** |
| 3 | #126 r3 | P1 | indented Lean declarations could bypass reachability-result discovery and the axiom completeness gate | `dd982e6` | `scripts/check_theorem_axioms.py:472` — discovery matches the declaration keyword anywhere on the line and tracks enclosing namespaces | **RESOLVED** |
| 4 | #126 r3 | P2 | binder-style hypotheses (`theorem t (h : P) : ReachesOne n`) were misclassified as unconditional `kernel_proof` | `dd982e6` | `scripts/check_theorem_axioms.py` — conditionality now reads the elaborated environment and counts proposition-valued binders | **RESOLVED** |
| 5 | #126 r4 | P2 | proposition-valued instance binders such as `[Fact P]` were excluded from conditionality | `32f6f9f` | `scripts/check_theorem_axioms.py:92`, the self-test fixture at `:102`, the rationale at `:705` | **RESOLVED** |
| 6 | #126 r5 | P2 | instance synthesis could specialize theorem-parameter metavariables, making a conditional theorem look unconditional | `c9400c1` | `scripts/prop_binder_probe.lean:14` (rigid local constants for theorem parameters); the specialized-instance regression at `scripts/check_theorem_axioms.py:122` | **RESOLVED** |
| 7 | #128 r2 | P2 | the domain documentation claimed the accelerated and standard maps agree on odd inputs | `1264872` | `Lean/CollatzResearch/StandardMapBridge.lean:14` — "The two are not the same map" | **RESOLVED** |
| 8 | #128 r2 | P2 | the delivered-story line named a nonexistent fully qualified bridge theorem | `1264872` | `docs/collatz-next-stories.md:73` — `CollatzResearch.universal_standard_convergence_of_universal_odd_convergence` | **RESOLVED** |

Two negative checks confirm the two P2 documentation findings did not merely
move: `git grep` over `main` finds **no** occurrence of
`CollatzResearch.StandardMapBridge.universal_standard_convergence` and **no**
false map-equality claim in any tracked `.md` or `.lean` file.

## PR #127 — the merge that carried no review

#127 merged with **0 published review objects and 0 issue comments**, so the
ledger records it as `merged_without_required_review`. The protocol requires the
closing verification to state explicitly whether that merged code is sound.

It is, on the evidence in the final tree:

- `scripts/agent_lifecycle.py`, `scripts/check_pr_review_gate.py`,
  `scripts/dispatch_codex_pr_review.py`, `scripts/pr_review_evidence.py` and
  `docs/codex-pr-review-gate.md` — the files this PR touched — are **byte-identical**
  between the arc's final tree (`c28174cd`) and the current `main` (`f56f25ea`).
  The only later edits to any of them came from PR #129, and `git diff --stat`
  shows `docs/codex-pr-review-gate.md` is the sole one of them that changed
  (+26/-7, the pilot-tooling round-counting text).
- The route it pinned is still pinned: `scripts/dispatch_codex_pr_review.py`
  declares `REVIEWER_MODEL = "openai/gpt-6.1-terra"` and
  `REVIEWER_THINKING = "high"`, and both dispatch paths pass `--thinking`.
- The gate it depends on refuses an approval without a published GitHub review
  (finding 1 above) and paginates review fetching (finding 2 above).

So the code #127 merged is sound; what it lacked was a published review, which
is recorded as a process gap rather than a code defect.

## How the arc's files were counted

The protocol says to count the arc's files with
`git diff --name-only <first-merged>...<final-head>` rather than summing
per-PR counts, because files touched by more than one PR get counted twice.

- `git diff --name-only 37499293...c28174cd` → **29 files**.
- `git diff --name-only 37499293...f56f25ea` → **62 files**: the arc's 29 plus
  everything PRs #129–#131 added afterwards. The delta is the pilot tooling and
  the R03 documentation, not the arc's own content.

## Validation for the final tree

- Hosted Lean CI on `main` at `f56f25ea` (run 45226969120): **success**, with
  `Build and validate Lean`, `Enforce Lean admission budget`,
  `Admission oracle regression checks` and `Audit transitive theorem axioms` all
  success. Hosted CI is the sole Lean gate for this repository.
- `docs/theorem-axiom-manifest.json` at `main`: **97** recorded results —
  51 `conditional_generic_theorem`, 38 `kernel_proof`, 8
  `compiler_dependent_instance`.
- The repo's own gate suites (`tests/test_pr_review_gate.py`,
  `tests/test_theorem_axioms.py`) are the executable evidence for findings 1–6;
  the result recorded in the closing pull request is the observed outcome of
  that run.

## What is NOT closed

The protocol's part (2) is **one published review** attesting that the union of
these eight findings is still fixed at the final tree. That review has not
been published. The mandated reviewer route
(`openai/gpt-6.1-terra` at `high`, pinned by
`scripts/dispatch_codex_pr_review.py`) produces no response in this deployment:
a direct probe of the route returned no output and was killed at its timeout
(exit 137, zero bytes on stdout and stderr), and the OpenAI provider reports a
failed sign-in.

So the arc is closed on **evidence and disposition**, but not on **independent
attestation**. The gap is recorded on all six pull requests and in the closing
pull request's review-gate section; a top-up on the OpenAI Platform account (or
a restored Codex subscription) unblocks the published review, and the handoff
and its payload are already recorded in
`state/collatz-research/review-gate/payloads/template-arc-close.json`.

## Follow-up

- Publish the one closing review when the reviewer route authenticates; it must
  re-check the union of the eight findings above against the final tree and mark
  each one RESOLVED.
- Consider teaching `docs/codex-pr-review-gate.md` to name the arc-closure
  vehicle explicitly. This record is the first arc closed this way in this
  repository, and the protocol currently leaves the vehicle unspecified.
