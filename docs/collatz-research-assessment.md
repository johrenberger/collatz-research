# Collatz research: assessment and recommended next direction

Reviewed 2026-11-13. Repository: johrenberger/collatz-research. Baseline: `b76819b7fefb8590ba1a9614f83e0aa7c0c85e81` on main, committed 2026-11-10.

**Recommendation: move from certificate plumbing to symbolic descent over infinite families.** Preserve the existing formal foundation, correct the trust accounting, and make the next research milestone an explicit, universally quantified descent theorem for a family of inputs. Do not measure progress toward Collatz by merged PRs, admission count, or the number of finite trajectories checked.

Assumptions:

- The objective is the standard Collatz conjecture on all positive integers, with Lean as the final proof authority.
- Main is the accepted baseline; open PR #122 concerns review orchestration and is not included in the mathematical assessment.
- This request authorizes analysis and a new backlog. The deliverables are local documents; no issues, comments, branches, or PRs were created.
- Effort budgets in the companion backlog are planning caps, not promises that a mathematical assertion can be proved within a deadline.

## What has actually been produced

| Area | Current evidence | Assessment |
|---|---|---|
| Canonical arithmetic | `Basic`, `Dynamics`, `Equivalence`: positivity, oddness, odd-input accelerated/standard trajectory transport | Useful checked foundation; retain |
| Symbolic execution | `Affine`: composition laws and `BranchWord.execute_eq_toAffine_apply` under `appliesTo` | Best starting point for the next research phase |
| Residue partitions and routing | `Residues`, `CoverageTree`, including orbit-aware routing completeness | Structural completeness is established; it is not descent or convergence |
| Certificate soundness | Q3/Q4 conditional transport; Q5 bounded routing-partition soundness, including terminal-value-one specialization | Substantial reusable machinery, but input coverage remains bounded or semantic premises remain caller-supplied |
| Concrete inhabitation | Two-leaf fixtures and `ReachesOne 2` under the totalized accelerated map | A real integration demonstration; native-evaluation dependencies require accurate reporting |
| Proof debt | Admission ledger records zero; obsolete admitted declarations were removed and proven witness infrastructure retained | Good hygiene; deletion of obligations must not count as proving them |
| Discovery experiments | `experiments/` contains README instructions and a smoke README explicitly reporting no committed numerical output | No committed research campaign or quantitative residual-domain analysis found |
| Reproducibility | `make reproduce` invokes `scripts/check.py` through smoke and again directly | A smoke check, not reproduction of research artifacts |

Sources: [theorem ledger](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/docs/theorem-status.md), [affine semantics](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Affine.lean), [bounded soundness](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Q5RoutingPartition.lean#L318-L353), [experiment smoke](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/experiments/smoke/README.md), [Makefile](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Makefile#L40-L44).

The historical progression is substantive: Stories 02/03 eventually closed dynamics and trajectory proofs; Story 04 eventually closed affine semantics; Story 07 established routing; Q3/Q4 introduced structured semantic evidence; Q5 established bounded certificate transport; NT-5 narrowed claims and retired unsupported paths. Those are not stories to recreate. However, repeated scope reductions from a semantic objective to a structural theorem mean “arc closed” cannot be read as “original mathematical objective achieved.”

## Findings that change the next plan

**[P0: claim accuracy] Native evaluation remains in the transitive proof dependency.**

`twoLeafRoutingPartition_reaches_one_two` passes `(by native_decide)` to `RoutingPartitionCertificate_sound`. The terminal-value-one concrete theorem does the same. The checker being evaluated includes trajectory transitions, not merely string metadata. Consequently, the final concrete reachability proof depends on the native-evaluation evidence even though its last inference is symbolic. A sound conditional theorem `check = true → ReachesOne x` does not make the proof of `check = true` disappear from the trusted base.

This is a reporting/trust-model defect, not evidence that the Collatz conclusions are false. The documentation's distinction between a “data-side” premise and a reachability conclusion does not justify describing the instantiated result as independent of the compiler. The pinned Lean 4.33 documentation states that `native_decide` generates per-invocation axioms and that `#print axioms` reports transitive dependencies. Exact axiom names for this repository must still be captured in a Lean run.

Evidence: [concrete theorem, lines 375–389](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Q5Stage4Tests.lean#L375-L389), [terminal-value-one instance, lines 434–439](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Q5Stage4Tests.lean#L434-L439), [checker, lines 248 onward](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/BoundedInputCertificateData.lean#L248), [Lean 4.33 axioms reference](https://lean-lang.org/doc/reference/4.33.0/Axioms/).

**[P1: research direction] Failed reduction attempts are being treated as a mathematical limit.**

The convergence-frontier document extrapolates from failed direct reductions of `Nat.factorization` to an overly restrictive view of what kernel proofs can establish. Failure of `rfl`, `decide`, or one rewrite sequence does not rule out an alternative representation with a proved equivalence.

A concrete alternative is arithmetic evidence for a step: positive odd `n`, positive odd `m`, and `3*n + 1 = 2^k*m`. A generic uniqueness-of-valuation lemma can establish `acceleratedStep n = m`; concrete arithmetic equations can then be proved without directly reducing the factorization implementation. This is a proposed engineering proof path, not an already compiled implementation.

Likewise, a certificate ending at `y != 1` can compose with separately proved reachability of `y`; the repository already has `orbit_predecessor_reaches_one`. Terminal value one is a reasonable existing certificate policy, not a mathematical ceiling. Extending that policy requires an explicit ADR update, not silently bypassing it.

Evidence: [frontier §§3–5](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/docs/convergence-frontier.md), [orbit composition and transport](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/CoverageTree.lean#L147-L197), [ADR 0009](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/docs/adr/0009-reachability-evidence-tier.md).

**[P1: semantics] The totalized accelerated map and standard Collatz must remain distinct.**

Lean defines `acceleratedStep` on all naturals. Thus the fixture follows `2 → 7 → 11 → 17 → 13 → 5 → 1`, whereas standard Collatz follows `2 → 1`. The existing transport theorem requires an odd starting input. The fixture is valid for the defined total map; it is not itself the standard trajectory from 2.

The clean theorem spine is: normalize a positive standard input to its odd part, prove convergence for positive odd inputs, and transport back along the initial halving steps. Explicitly bridge the duplicate `trajectory` and `accelerated_orbit` interfaces. This prevents later bounded or universal claims from quietly changing domains.

Evidence: [map definition](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Basic.lean#L14-L16), [odd-input transport](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/Equivalence.lean#L250-L278).

**[P1: planning] Bounded coverage has no automatic route to universal descent.**

The useful target is:

`∀ n > 1, Odd n → ∃ k > 0, 0 < T^k(n) ∧ T^k(n) < n`.

Strong induction, orbit composition, and domain preservation turn this into convergence. The reduction is routine formal mathematics; proving its universal premise is the unsolved research obligation. Naming that premise inside a certificate or a leaf structure does not discharge it.

There is also a concrete obstruction to a naive finite-depth strategy. For every `L >= 1`, let `n = 2^(L+1) - 1`. For `0 <= j <= L`,

`T^j(n) = 3^j * 2^(L+1-j) - 1`.

Each of the first L transitions has valuation one, and every positive-length prefix in that range stays above n. Therefore no fixed accelerated-step bound can witness strict descent for every positive odd input. A finite collection of fixed-length branch words has a maximum length and cannot supply universal strict descent. This does not exclude finite proofs with parameterized lemmas, well-founded recursion, or a different ranking function.

This identity is derived here, not claimed as a new research discovery. Independent BigInt diagnostics checked 2,080 identities for L=1..64 and 512 parameterized run endpoints. Those diagnostics are not Lean proofs; formalizing the obstruction is an early backlog item.

**[P2: integration scope] The external parser and the final routing-partition interface are different formats.**

The Python producer and Lean JSON parser implement `BoundedInputCertificateWire`; the later theorem consumes `RoutingPartitionCertificateData` with a leaf-claim registry. The inspected parser does not implement a routing-partition decoder. The successful concrete fixtures do not by themselves demonstrate an external multi-leaf JSON-to-theorem pipeline. Complete that integration only if it supports the chosen research campaign; it should not dominate the next phase.

Evidence: [Python producer](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/python/collatz_research/bounded_input_certificate.py), [parser API](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/BoundedInputCertificateParser.lean#L510), [routing-partition wire model](https://github.com/johrenberger/collatz-research/blob/b76819b7fefb8590ba1a9614f83e0aa7c0c85e81/Lean/CollatzResearch/BoundedInputCertificateData.lean).

## Recommended research strategy

Use the existing affine executor to prove statements about whole input classes, then study the exact residual classes. For a valid branch word of length r and valuation sum K, derive the exact integer relation

`2^K * T^r(n) = 3^r*n + b`.

Strict descent follows when `(2^K - 3^r)*n > b`. A useful certificate must establish that the word actually applies throughout the claimed class, not just that this inequality holds for a sampled representative.

Start with a deliberately simple infinite-family theorem: positive odd n with `n > 1` and `n ≡ 1 (mod 4)` has `T(n) < n`. This is a baseline, not novelty. Then extend to multi-step exact residue families and explicitly enumerate what remains unresolved. Do not assume every starting value in a residue class shares a valuation sequence without proof.

Handle arbitrarily long ascent runs symbolically. For `n = 2^a*u - 1`, with a>=1 and positive odd u, the first a-1 accelerated steps satisfy

`T^(a-1)(n) = 2*3^(a-1)*u - 1`.

The next numerator is `2*(3^a*u - 1)`, so the next transition has valuation at least two. This compresses an unbounded run into one lemma. It does not establish net descent: the later contraction and behavior of u remain the research problem.

**Speculative:** a finite set of such parameterized transitions plus a well-founded ranking invariant may organize the residual families into a proof. There is no evidence yet that this representation closes all cases. Fund a bounded falsification campaign before building a general synthesis framework.

An improving density statistic is useful for selecting conjectures, but it cannot eliminate an exceptional orbit. Tao's result concerns almost-all behavior in logarithmic density, not convergence for every input; any probabilistic or density-based branch must state what bridges that quantifier gap. [Primary source](https://arxiv.org/abs/1909.03562).

## Delivery and decision gates

The companion backlog contains 12 primary stories and one conditional integration story. Execute R01–R05 first: trust classification, canonical semantics, descent reduction, step-evidence proofs, and the fixed-depth obstruction. Then deliver R06–R09 as the first substantive infinite-family campaign. Fund R10–R12 only against explicit residual hypotheses and a fixed compute budget.

Suggested ongoing allocation after the initial assurance work: 60% mathematical lemmas and formalization, 25% bounded discovery/falsification, 15% necessary maintenance. This is a planning recommendation, not an observed productivity estimate. No new orchestration work should displace the research path unless it blocks execution.

Progress measures:

- Universally quantified family theorems proved, with exact domains and axiom dependencies.
- Residual families characterized; conjectures refuted with reusable counterexamples.
- Certificate replay time and artifact size at fixed benchmark inputs.
- Explicit obligations removed from the convergence dependency graph.

Do not use PR count, a zero admission ledger, finite verification range, or “arc closed” as a percentage-complete estimate for Collatz. There is no defensible percentage here.

## Evidence and limits of this assessment

Inspected the complete recursive repository file inventory, current mathematical/trust/frontier documentation and ADRs, core dynamics/affine/descent definitions, certificate representations and principal soundness/concrete-instance paths, producer/parser interfaces, workflow definitions, and historical PR/issue summaries through #122. This is a research-planning audit, not a line-by-line correctness review of every implementation or every historical diff.

Observed [Lean CI run 42823211015](https://github.com/johrenberger/collatz-research/actions/runs/42823211015) succeeded at the reviewed head. Its job steps include explicit Q5 targets, Stage-4 tests, admission-budget enforcement, and admission-oracle regression checks. Scheduled smoke reproduction also succeeded. The latter is not evidence of full Python test execution or research reproducibility.

No local Lean/Lake installation was available, so no clean build, theorem axiom printout, or repository test suite was independently rerun. The trust finding follows from the visible proof terms and pinned Lean documentation; collecting the exact dependency output is R01. The only newly executed mathematical checks were the independent BigInt diagnostics described above.
