# Collatz research: next stories

Baseline: `b76819b7fefb8590ba1a9614f83e0aa7c0c85e81`, reviewed 2026-11-13. These are proposed stories, not GitHub issues and not promises of a Collatz proof. Read alongside `collatz-research-assessment.md`.

**Primary objective:** establish useful universally quantified descent facts, characterize the unresolved domain, and test a specific route toward the universal descent obligation.

## Execution order

| ID | Priority | Deliverable | Depends on | Initial effort cap |
|---|---|---|---|---|
| R01 | P0 | Transitive axiom audit and corrected claim tiers | — | 2 focused workdays |
| R02 | P1 | Canonical odd-domain/standard-map bridge | — | 3 workdays |
| R03 | P1 | Strong-induction reduction from descent to convergence | R02 | 3 workdays |
| R04 | P1 | Arithmetic step witnesses without native evaluation | R01, R02 | 5 workdays |
| R05 | P1 | No fixed bound on first-descent time | R02; R04 reusable | 3 workdays |
| R06 | P1 | Branch-word semantics connected to actual orbits | R02, R04 | 4 workdays |
| R07 | P1 | Infinite-family descent certificate semantics | R03, R06 | 5 workdays |
| R08 | P1 | First exact residue-family theorem suite | R07 | 5 workdays |
| R09 | P1 | Reproducible residual-family search | R08 | 5 workdays + capped runs |
| R10 | P1 | Parameterized ascent-run theorem | R04, R05, R06 | 5 workdays |
| R11 | P1 | Falsify a bounded grammar of ranking candidates | R09, R10 | 5 workdays + capped runs |
| R12 | P1 | Formalize one surviving invariant, or publish its obstruction | R03, R07, R11 | 10-workday research spike |
| R13 | P2, conditional | External multi-leaf certificate replay | R01, R04; campaign need | 5 workdays |

Caps bound investigation before a decision; they are not effort estimates calibrated from this project's velocity. A missed cap produces a precise blocker and revised scope, not an admitted release theorem. R05 and R10 are known mathematical targets, not speculative claims. R11–R12 are research with unknown outcomes.

## Shared acceptance contract

- Every mathematical story records its exact proposition, domain, hypotheses, and intended use in the descent-to-convergence chain before implementation.
- Zero `sorry`/`admit` and no unapproved axioms in release dependencies. A new conditional theorem is labeled conditional; its hypotheses remain visible in the obligation ledger.
- Audit transitive axioms of exported results. A native-evaluated acceptance premise makes the instantiated result compiler-dependent, regardless of the last tactic or premise label.
- Tests cover meaningful boundaries, malformed evidence, independent arithmetic comparisons, and actual theorem application where relevant. Concrete examples alone do not test whether a generic theorem was used.
- Search cutoffs produce `unknown` or `budget_exhausted`, never “no descent,” “nonconvergent,” or a negative universal conclusion.
- A research story may succeed by refuting its candidate and publishing a reusable obstruction. Engineering completion does not promote the original mathematical claim automatically.
- Keep ADR 0009's existing behavior until a reviewed successor explicitly extends it for composed terminal evidence or inductive descent certificates. The proposed extension strengthens dependency accounting and does not authorize compiler trust on the proof path.

## R01 — Audit transitive proof dependencies and correct the evidence tiers

**Story:** As a researcher, I need each named result's actual trusted base so that a native-evaluated premise cannot be presented as a kernel-only concrete theorem.

**Scope:** Extend the existing admission gate rather than replacing it. Audit the general terminal-value-one soundness theorem separately from its concrete instances.

**Acceptance criteria:**

1. Capture `#print axioms` output for `RoutingPartitionCertificate_sound_terminal_value_one`, `twoLeafRoutingPartition_reaches_one_two`, `twoLeafRoutingPartition_sound_terminal_value_one`, and the concrete per-leaf certificate definitions.
2. Classify exported results as conditional generic theorem, kernel proof under the approved standard axiom set, or compiler-dependent instantiated result. Record exact native-generated names on the pinned toolchain.
3. CI checks transitive dependencies against an explicit allowlist for theorem-facing results, including dynamically generated native-evaluation axioms; a wrapper around a native-evaluated proof must fail that release gate.
4. Update the trust model, ADR 0009 clarification/successor, theorem status, and frontier language together. Keep existing compiler-dependent test fixtures usable under an explicitly separate category.
5. Replace the inference “these tactics failed, therefore a kernel proof is unavailable” with the measured fact: those reductions failed on that implementation and toolchain.

**Validation:** a known clean proof, an admitted proof, a direct native proof, and an indirect wrapper around a native proof exercise the gate. No global convergence claim changes.

**Completion artifact:** machine-readable theorem/axiom manifest and a short decision record.

## R02 — Make the standard-Collatz theorem boundary explicit

**Story:** As a formalizer, I need odd-domain accelerated results to imply the intended standard-map statement for every positive input.

**Acceptance criteria:**

1. Prove the equality of `trajectory n k` and `accelerated_orbit n k`, or consolidate them behind a compatibility theorem without breaking callers.
2. Define standard-map reachability explicitly, keeping it distinct from the totalized accelerated `ReachesOne` predicate.
3. For every positive n, establish an odd positive q and a>=0 with `n = 2^a*q`, and prove `standardTrajectory n a = q`. Reuse `standardTrajectory_pow_div`.
4. Compose normalization with the existing odd-input transport theorem to prove: universal positive-odd accelerated convergence implies universal positive standard convergence.
5. Regression cases cover 0 excluded from the final theorem, 1 as the base case, 2 and 8 via halving, and 3 via the odd bridge. Explicitly record `acceleratedStep 2 = 7` versus `standardStep 2 = 1`.

**Non-goal:** changing the totalized map's established semantics or proving convergence.

**Completion artifact:** one named public bridge theorem and exact domain documentation.

## R03 — Prove the descent-to-convergence reduction

**Story:** As a researcher, I need the remaining mathematical obligation to be a precise strict-descent proposition rather than a vague missing leaf certificate.

**Target premise:** for every odd n>1 there is k>0 with `0 < trajectory n k < n`.

**Acceptance criteria:**

1. Define `EventuallyDescends n` with explicit positive length, positive endpoint, and strict inequality.
2. Prove by strong induction that universal odd-input descent implies odd-input reachability of one, using oddness preservation and orbit composition.
3. Compose with R02 to obtain standard positive-input convergence under that explicit descent hypothesis.
4. Also prove the converse on the odd domain: convergence implies eventual descent for n>1. This makes the residual obligation mathematically precise, not apparently weaker than Collatz.
5. Record the complete dependency graph and label the universal descent premise as OPEN. Do not introduce it as an axiom or as the default field of a purportedly inhabited certificate.

**Validation:** n=1 is the terminal base, not a strict-descent case; zero-step and equal-endpoint witnesses cannot satisfy descent; the proof consumes positive odd closure at every inductive call.

**Non-goal:** claiming the universal premise has been established.

## R04 — Verify arithmetic step witnesses without native evaluation

**Story:** As a certificate consumer, I need finite trajectories certified by explicit arithmetic equations and generic lemmas, without trusting native evaluation of `Nat.factorization`.

**Design:** for an odd-input step, supply k>=1 and a positive odd m with `3*n+1 = 2^k*m`. Prove once that this entails `twoAdicValuation (3*n+1) = k` and `acceleratedStep n = m`. This is a proposed implementation route; inspect the pinned Mathlib lemmas before choosing the proof shape.

**Acceptance criteria:**

1. Prove the generic arithmetic-to-step bridge with all positivity and oddness hypotheses explicit.
2. Define a total finite-trace checker over raw numeric data and prove acceptance implies the canonical trajectory endpoint. The checker must establish transitions, not carry the desired endpoint theorem as a proof field supplied by the producer.
3. Produce a named, audited proof for the odd trajectory `3 → 5 → 1`, and at least one nontrivial longer trace such as the trajectory from 27. Use the standard normalization bridge for even starts.
4. Reject altered exponent, non-odd successor, incorrect arithmetic equation, empty required trace, and wrong start/end. State how the zero-step trace for input 1 is represented.
5. `#print axioms` for concrete results contains no native-evaluation axiom and no admission. Any generated Lean terms are deterministic and compiled in CI.

**Fallback within scope:** deterministic arithmetic proof-term generation is acceptable if a reducible Boolean checker is impractical. Python still supplies untrusted numbers; Lean checks the equations.

**Non-goal:** optimizing million-input verification or reviving the retired digest-based Lean acceptance bridge. Hashes establish artifact identity, not arithmetic soundness.

## R05 — Formalize the obstruction to fixed-depth universal descent

**Story:** As a research planner, I need a proof of what the current finite-prefix representation cannot establish before spending more time enlarging it.

**Target:** for L>=1, n=`2^(L+1)-1`, and 0<=j<=L,

`trajectory n j = 3^j * 2^(L+1-j) - 1`.

**Acceptance criteria:**

1. Prove n is positive odd and each of the first L transitions has valuation one.
2. Prove the displayed identity with natural-subtraction side conditions explicit.
3. Derive `trajectory n j > n` for 1<=j<=L.
4. State and prove that no fixed L bounds first strict descent for all positive odd n>1. Extend the formulation to exclude rescuing such a bound with only finitely many exceptional inputs.
5. Document the precise architectural consequence: finite lists of explicit fixed-length descent words cannot cover the full domain. Parameterized proofs, recursion, and other ranking measures remain possible.

**Validation:** L=1, 2, 3 examples plus the universally quantified theorem. The assessment's numerical diagnostics are examples only.

**Completion artifact:** an obstruction theorem and a scope constraint on future coverage stories.

## R06 — Connect branch words to canonical trajectories and exact affine identities

**Story:** As a formalizer, I need the existing affine algebra to certify real orbit segments, not only a separate executor.

**Acceptance criteria:**

1. Prove `word.appliesTo n → word.execute n = trajectory n word.length` with intermediate oddness and positivity accounted for.
2. Prove the induced affine coefficient is `3^word.length`, its denominator exponent is the sum of valuations, and its offset is nonnegative.
3. Establish the exact integer relation `2^K * trajectory n r = 3^r*n + b` under `appliesTo`; do not rely on a truncated quotient as if divisibility were automatic.
4. Derive a strict-descent criterion from `(2^K - 3^r)*n > b`, using integer arithmetic or explicit nonnegative-domain hypotheses so subtraction cannot silently truncate.
5. Add proof applications for a nonempty word and the empty-word boundary. A test that proves a concrete equality solely by `decide` does not substitute for applying the exported generic theorem.

**Reuse:** `AffineMap.comp_apply_eq` and `BranchWord.execute_eq_toAffine_apply` remain the algebraic foundation.

## R07 — Define sound infinite-family descent certificates

**Story:** As a researcher, I need a finite certificate that proves descent for all members of a specified infinite family, rather than enumerating finite starting values.

**Design:** a family contains explicit modulus/residue and lower-bound constraints; evidence establishes branch applicability throughout that family, exact affine execution, and a descent inequality. Keep this separate from legacy `.interval` reachability claims.

**Acceptance criteria:**

1. Formalize the family denotation over positive odd inputs and distinguish an infinite family from a bounded sample.
2. Prove exact valuation constraints using congruences at sufficient modulus: divisibility by `2^k` alone is insufficient; exclude divisibility by `2^(k+1)`.
3. Prove checker acceptance entails `∀ n ∈ family, EventuallyDescends n`, with lower-bound assumptions explicit.
4. Support a finite exceptional prefix via separately checked evidence. Every exception is enumerated and covered; none is silently dropped.
5. Define a conditional composition theorem from a family cover plus family-descent facts to R03's premise. Do not claim a global cover exists.
6. Record the policy extension for inductive descent separately from ADR 0009's finite terminal-one certificates. Preserve the axiom gate.

**Failure tests:** wrong residue, insufficient modulus, strict-versus-nonstrict endpoint, missing exceptions, and overlapping families mistaken for completeness. Overlap is acceptable if the proof only requires coverage; disjointness must not be demanded without a consumer.

## R08 — Prove the first residue-family descent suite

**Story:** As a researcher, I need an end-to-end demonstration of universal family reasoning before designing a larger search engine.

**Mandatory target:** for positive odd n>1 with n mod 4=1, prove `acceleratedStep n < n`. This covers an infinite class without enumerating its members.

**Acceptance criteria:**

1. Prove the mandatory theorem from the fact that `4 | 3*n+1`, handling n=1 separately.
2. Instantiate R07 for exact valuation subclasses where needed; explicitly distinguish a valuation lower bound from a fixed exact branch word.
3. Produce at least one checked multi-step class outside the mandatory n mod 4=1 family. Select the concrete class by exact search before freezing the implementation packet; publish its modulus, residue, word, threshold, and exceptions.
4. Produce the exact complement of the finite family union at a common modulus, with every lower-bound exception separately listed.
5. Label these as baseline formal results, not novel number theory or global convergence.

**Success measure:** named theorems over infinite sets and an explicit unresolved set, not the largest tested starting input.

## R09 — Run a reproducible search over unresolved residue families

**Story:** As a researcher, I need a deterministic campaign that generates candidate symbolic descent certificates and explains why remaining classes resist them.

**Initial bounds:** modulus exponents 4..12, explicit branch depth at most 12, one deterministic seed/configuration, 30 CPU-minutes per run and 2 GB memory. Treat these as adjustable experiment parameters after the first benchmark, not implied permission for paid infrastructure.

**Acceptance criteria:**

1. Search only within declared resource and representation bounds; preserve arbitrary-precision integer arithmetic.
2. Export accepted family candidates and a residual-class manifest. Label every cutoff `unknown`; no enumeration result asserts universal convergence.
3. For every promoted family, Lean checks universal applicability and descent using R07. Python checks guide discovery only.
4. `make reproduce` regenerates one small committed campaign's manifest and stable digests, rather than rerunning only the smoke script.
5. Report exact residue coverage, separately tracked finite exceptions, hardest surviving families, wall/CPU time, artifact bytes, and Lean replay time. Any density is explicitly a density of the certified set under stated conventions.
6. Include the R05 ascent family as an adversarial regression and keep failed candidates/counterexamples in a reusable corpus.

**Stop condition:** reaching a bound ends the run with a residual manifest. Increasing bounds requires a specific hypothesis about what that increase will teach.

## R10 — Compress unbounded ascent runs into a parameterized theorem

**Story:** As a researcher, I need one symbolic transition to handle the arbitrarily long valuation-one runs that defeat fixed-depth coverage.

**Target:** for a>=1 and positive odd u, with `n = 2^a*u - 1`, prove

`trajectory n (a-1) = 2*3^(a-1)*u - 1`.

At that endpoint the next numerator is `2*(3^a*u - 1)` and its two-adic valuation is at least two.

**Acceptance criteria:**

1. Prove the formula and the exact valuation-one prefix for all admissible parameters.
2. Prove every positive odd n has this representation using a=`v₂(n+1)` and positive odd u.
3. Handle a=1 as a zero-length prefix; prove the subsequent contracted transition separately and retain its exact valuation parameter.
4. Expose a reusable theorem for composition with R06/R07. No fixed a cutoff is allowed in its formal statement.
5. Record the residual inequality required for net descent and show examples where a single such block does not descend. Do not label the compression lemma a convergence result.

**Completion artifact:** a universally quantified macro-step lemma and residual obligations, with audited axioms.

## R11 — Falsify a bounded grammar of ranking-function candidates

**Story:** As a researcher, I need to test a specific invariant hypothesis against the residual families before spending weeks attempting a universal proof.

**Speculative hypothesis:** the parameterized blocks from R10 admit a finite-state piecewise ranking argument. No evidence currently establishes that this grammar contains a successful ranking function.

**Acceptance criteria:**

1. Freeze the candidate grammar and ordering before the campaign: a finite residue-state partition, bounded integer coefficients, and natural-valued or lexicographic natural-valued rank components. Include a defined nonnegativity/well-foundedness obligation.
2. Enumerate candidate expressions with exact arithmetic. Use the residual corpus, high-a ascent runs, boundary values, and held-out inputs for falsification. SMT, if used, is an untrusted candidate generator.
3. For each surviving candidate, state the universal decrease proposition and all branch-coverage/termination premises. Distinguish “no counterexample found” from a proof.
4. For each rejected candidate, emit a small concrete counterexample with a replayable arithmetic trace. Solver timeout is `unknown`.
5. Use an initial aggregate cap of 10 CPU-hours; stop earlier if the entire grammar is refuted. Record whether rejection is numerical, symbolic, or proved in Lean.

**Completion artifact:** a ranked shortlist with proof obligations, or a negative-result report that rules out the tested grammar. Do not expand the grammar automatically to keep the story alive.

## R12 — Formalize one surviving invariant or its precise obstruction

**Story:** As a researcher, I need one decisive formal result from the discovery campaign, even if it shows that the chosen approach cannot close the conjecture.

**Entry gate:** R11 provides either a concrete surviving invariant with explicit domains or a general obstruction worth proving. If neither exists, do not start this story.

**Acceptance criteria:**

1. Freeze the theorem statement, including exact residual domain and all assumptions, before coding.
2. Prove initialization, domain preservation, coverage of applicable transitions, strict decrease, and well-foundedness for the selected invariant. A real-valued heuristic with negative average drift is not a well-founded ranking proof.
3. If the invariant only covers a subset, export that subset theorem and the exact complement. If a needed implication is false, formalize the obstruction/counterexample instead.
4. Compose a successful descent result with R03 only on the established domain. Universal convergence can be claimed only if the domain-cover obligation is also proved with no circular reachability premise.
5. Produce a review package with the dependency graph, transitive axiom output, commands, proof artifact, and a primary-literature comparison. State novelty conservatively.

**Research cap:** ten focused workdays, then choose continue, revise, or stop based on the identified missing lemma. A bounded negative result is a valid outcome; an admitted theorem or renamed assumption is not.

## R13 — Complete external multi-leaf certificate replay only if needed

**Story:** As a campaign operator, I need external serialized evidence to reach the routing-partition theorem without hand-built Lean fixtures.

**Entry gate:** R09 or another approved campaign actually needs this route. Otherwise defer it; finite replay is useful infrastructure but is not the research objective.

**Acceptance criteria:**

1. Introduce a versioned routing-partition format containing the claim registry and canonical input slots; do not imply the existing single-leaf parser already supports it.
2. Decode raw fields into the checked representation with explicit rejection of malformed length, duplicate/conflicting leaf registry entries, absent registrations, and invalid values.
3. Replay a Python-generated two-leaf payload through parsing, validation, arithmetic evidence checking, and a named bounded theorem; no manual proof fields in the wire data.
4. Use R04 evidence or disclose compiler dependence consistently with R01. A release result must satisfy the approved transitive axiom policy.
5. Mutating a transition, registry claim, input slot, or bound causes rejection. Deterministic regeneration and artifact digests are recorded.

**Non-goal:** unbounded convergence or a new proof-search framework.

## First milestone and stop rules

**Milestone A:** R01–R05 establish truthful evidence tiers, the standard-map bridge, a precise open descent obligation, a clean finite-evidence path, and a proof that fixed-depth universal descent is impossible.

**Milestone B:** R06–R09 produce at least two explicit infinite-family results, a reproducible search, and a mathematically specified residual domain.

**Milestone C:** R10–R12 test a parameterized route across the residual domain. Its successful outcome may be a stronger family theorem or a formal obstruction; global Collatz remains unclaimed unless all universal obligations close.

Do not make cycle exclusion a separate primary workstream now. Universal strict descent would exclude nontrivial positive cycles as a consequence, while bounded cycle enumeration would not rule out divergent trajectories. Reconsider a cycle-specific story only when an affine identity from this campaign provides a concrete new theorem target.

Do not revive `.interval` reachability, the retired v1 Lean digest bridge, or general agent orchestration as default next work. Each needs a demonstrated consumer on this research path.
