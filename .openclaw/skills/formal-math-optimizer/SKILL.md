---
name: formal-math-optimizer
description: "FAOP +O (Optimized). Owns the L1–L5 law catalog and the `par` dispatcher. Identifies independent leaves in a sequence and rewrites them as concurrent subagent fan-outs. The PR_REVIEW cycle's fetchers and the controller's pre-flight reads are the first targets."
---

# Formal Math Engineering — Optimizer (+O)

> Companion skill invoked by the controller and by `formal-math-effect-dispatch` when the same-state-machine path has a known parallelization opportunity. Implements FAOP `+O`: the L1–L5 law catalog from Table 4 of arXiv 2610.22061, applied to the formal-math-engineering controller.

This skill is the throughput lever. Stages 1–3 fixed the regression (LLM bypass, typed working state, composite bounds). Stage 4 makes the workflow faster without changing what it does.

## The Five Laws (recap of FAOP Table 4)

| Law | Optimization | Effect in this workflow |
|---|---|---|
| **L1** Safe instrumentation | Insert or remove a pure value step (logging, metric) without changing surrounding function | Validation now has a "log_dispatch" hook; an instrumented step is `L1`-compatible iff it touches no fields outside `data_json` |
| **L2** Sub-workflow extraction | Regroup a sub-sequence and register it as a FAOP under FNF-3 | `OPEN_OR_VERIFY_PR` + `DISPATCH_REVIEW` are extracted as a single `REVIEW_ROUND.v1` FAOP for reuse across rounds |
| **L3** Commutativity of independent steps | `a ⊥ b ⇒ seq(a,b) = seq(b,a) = par(a,b)` | **The throughput lever.** Independent fetchers run in parallel; sequential stragglers across the controller state machine are rewritten as `par` calls |
| **L4** Branch distribution | `seq(if(p,a,b),c) = if(p,seq(a,c),seq(b,c))` | Each PR_REVIEW sub-arm (P0/P1/P2) gets its own copy of the post-branch validation step, optimized for that arm |
| **L5** Canonical reuse | Replace inlined sub-sequence by `call(id)` to registered body | Every `git status`-then-`git rev-parse` pair becomes one `GIT_HEAD.v1` call; every `make ci` invocation routes through the single canonical validation path |

The optimizer owns the **law catalog** (what's safe to rewrite) and the **parallel dispatcher** (how `par` actually runs).

## L3 — The Throughput Lever (Commutativity)

### Independence Test (Definition 7 from FAOP)

Two steps `a, b` are independent (`a ⊥ b`) iff:

```text
S_out(a) ∩ (S_in(b) ∪ S_out(b)) = ∅
       AND
S_out(b) ∩ S_in(a) = ∅
```

In our working-state terms: step `a` and step `b` are independent iff neither writes a field the other reads or writes. Because `working_state` is a finite map, this is a **pairwise check** that runs in O(|F|·|V|).

The optimizer computes the independence graph (Convention 3 in FAOP: one node per step, one directed edge per dependency) and reads the answer off reachability: a step can move past another iff there's no path in the graph between them.

### The `par` Dispatcher

The repository has no executable formal-math dispatcher. This describes the target contract; it must not be presented as an implemented capability. The proposed dispatcher would accept a `par_request`:

```yaml
par_request:
  effect_label: "deterministic" | "code_review" | "op_LLM"
  leaves: list[DispatchRequest]                    # the independent sub-requests
  isolation: "fork"                                 # sessions_spawn context
  timeout_seconds: int                              # wallclock cap for the whole par
  failure_mode: "fail_fast" | "best_effort" | "all_required"
```

The proposed dispatcher would execute `par_request` by:

1. **FAN-OUT**: for each leaf in `leaves`, call `sessions_spawn(taskName=<leaf.primitive>, context: "fork", toolsAllow=<leaf.scope.tools_allow>, ...)` with the leaf's full `dispatch_request`. Each leaf's tokens_used and wallclock are scoped to that subagent.
2. **WAIT**: wait for all subagent returns, capped by `par_request.timeout_seconds`.
3. **MERGE**: aggregate the typed `dispatch_result` rows into a single `par_result` envelope:
   ```yaml
   par_result:
     effect_label: <echo>
     ok: bool
     leaves: list[DispatchResult]                 # one per subagent
     tokens_used: int                              # sum of leaf.tokens_used
     wallclock_seconds: int                        # max of leaf.wallclock_seconds (true parallel)
     started_at: iso8601
     finished_at: iso8601
   ```
4. **RECORD**: append one aggregate `dispatch_log` row with `usage_kind="aggregate"`, `tokens_used=NULL`, and summary usage only in `data_json`; append one `usage_kind="leaf"` row per leaf with that leaf's actual usage.
5. **ENFORCE BOUNDS**: composite queries sum only `usage_kind="leaf"` rows. Never count the aggregate envelope and its leaves together. The aggregate token sum remains a summary, not another usage event.

### Independence Requirements for `par`

A `par` request is **refused** if the optimizer cannot prove pairwise independence between every pair of leaves. The refusal is a typed `dispatch_log` row with `failure_signature.fingerprint = "not_independent"` and `data.conflicting_pair = [primitive_a, primitive_b]`. The controller falls back to sequential execution.

This is the FAOP Proposition 1 (Type safety) guard applied to `par`: independent leaves commute; dependent leaves cannot be parallelized without violating the data-flow contract.

## L2 — Sub-Workflow Extraction (FNF-3)

The PR_REVIEW cycle has a natural sub-sequence: `OPEN_OR_VERIFY_PR` → `DISPATCH_REVIEW`. The optimizer extracts this as a single FAOP:

```yaml
REVIEW_ROUND.v1:
   body: seq(OPEN_OR_VERIFY_PR, DISPATCH_REVIEW)
   inputs:  { story_id, round, pr_url, head_sha }
   outputs: { pr_review_round_row }
```

The benefit: every round reuses the same `REVIEW_ROUND.v1` call site rather than re-inlining the two primitives. Drift between rounds is impossible; one edit propagates.

## L1 — Safe Instrumentation (Logging as a First-Class Citizen)

The dispatcher's `dispatch_log` is itself an L1 application: a pure append step that doesn't change behavior, only records. The optimizer treats any new logging primitive as L1-compatible iff:

```text
- reads nothing from working_state (other than the story_id for the key)
- writes only to dispatch_log
- never appears in a `reads-from` position
```

A new metric primitive that violates these rules is not L1-safe and is rejected at registration.

## L4 — Branch Distribution

The PR_REVIEW cycle has three arms (P0/P1/P2) that each follow with a `re_validate` step. Currently `re_validate` is shared. L4 rewrites the shared step into per-arm copies, so each arm's `re_validate` is specialized:

```text
BEFORE:  seq(if(p_findings, REMEDIATE_P1, RESOLVE_P2), RE_VALIDATE)
AFTER:   if(p_findings,
            seq(REMEDIATE_P1, RE_VALIDATE_P1)        # P1-specific: full make ci
            seq(RESOLVE_P2, RE_VALIDATE_P2))         # P2-specific: narrow gate only
```

The benefit: a P2-only finding does not trigger the full `make ci`; it triggers a narrow lint or test gate. Wallclock and tokens drop on the P2 path.

## L5 — Canonical Reuse (FNF-3 dedup)

The companion skills have at least three places where the same sub-sequence is inlined twice:

| Sub-sequence | Sites | Reuse as |
|---|---|---|
| `git status` + `git rev-parse HEAD` + `git branch --show-current` | `formal-math-discovery`, `formal-math-baseline`, `formal-math-classify-failure` (twice) | `GIT_HEAD.v1` (one call, returns a typed record) |
| `make format-check && make lint && make test` (narrow gate) | `formal-math-validate` (twice), `formal-math-pr-review` (`RE_VALIDATE`) | `NARROW_VALIDATE.v1` |
| `dispatch_log` append + read-modify-write of `working_state` | every companion skill | `CHECKPOINT_AND_LOG.v1` (the χ primitive) |

L5 extracts each into a single canonical FAOP. After extraction, drift between sites is impossible; the optimizer verifies no inlined reconstruction remains at commit time.

## The Optimizer's API

```text
identify_parallelization_opportunities(story_id) -> list[ParallelizationPlan]
   -> reads working_state, recent dispatch_log rows, the current state-machine path
   -> returns a list of {state, par_candidate, leaves, expected_latency_delta}

rewrite_as_par(plan) -> DispatchResult
   -> constructs a par_request, dispatches it, returns the par_result
   -> refuses if independence is not proven

extract_subworkflow(FAOP, body) -> FAOP
   -> L2: register a new FAOP from an inlined sub-sequence

apply_L1_instrumentation(primitive) -> bool
   -> checks the L1-safety contract

distribute_branch(branch_faop) -> list[FAOP]
   -> L4: returns the per-arm specializations

canonicalize(site) -> FAOP
   -> L5: returns the canonical FAOP for the inlined sub-sequence

verify_no_drift(FAOP) -> bool
   -> at commit time, verifies all inlined reconstructions of FAOP have been removed
```

## Where Stage 4 First Applies (the Targets)

The optimizer is invoked the first time on the following known opportunities:

| Target | Law | Expected gain |
|---|---|---|
| PR_REVIEW: `fetch_pr_comments ‖ fetch_ci_status ‖ fetch_last_diff` (replace the `OPEN_OR_VERIFY_PR` step's three sequential `gh` calls) | L3 | up to 3× latency reduction on PR_REVIEW entry |
| `DISPATCH_REVIEW` of gpt-5.6-terra: parallel fetch of PR URL, head SHA, last review SHA, reviewer model registration check | L3 | up to 4× latency reduction on review dispatch |
| `NARROW_VALIDATE.v1` extraction across `formal-math-validate` and `formal-math-pr-review` | L2 + L5 | drift impossible, single edit propagates |
| `GIT_HEAD.v1` extraction across 4 sites | L5 | drift impossible, 1 fewer API call per dispatch |
| PR_REVIEW arm specialization (`RE_VALIDATE_P1` vs `RE_VALIDATE_P2`) | L4 | up to 60% wallclock reduction on P2 path |

After the first run, the optimizer's `identify_parallelization_opportunities` will find more — likely in the IMPLEMENT and VALIDATE cycles where Lean rebuilds can run alongside Python lints.

## What This Skill Does Not Do (Stage 5+ scope)

- **No automatic proof that the independent-test passes.** A future Stage 5 (or a SkillBase toolchain) can statically check `S_in ∩ S_out` from the working_state schema. For now, the optimizer runs the O(n²) pairwise check on the leaf's declared `inputs` / `outputs` schemas.
- **No automatic extraction.** L2 and L5 are run by hand for now. A future Stage 6 toolchain (SkillBase-style) can register and verify FAOPs automatically.
- **No streaming aggregation.** The `par_result` envelope waits for all leaves. A future Stage 5+ can stream leaves as they complete.

## Co-Signed Invariant (controller invariant #20)

> **#20 Independent leaves in the same state-machine path are dispatched as `par` requests via `formal-math-optimizer` whenever the optimizer can prove pairwise independence from the working_state schema. The dispatcher refuses any `par` request whose leaves are not provably independent. The optimizer's `par_result` is recorded as a single `dispatch_log` row plus per-leaf rows; bounds enforcement uses the leaf totals.**
