# Trust model

The Lean kernel is the final checker. Python, package resolvers, CI runners, LLMs, SMT solvers, and JSON files are untrusted input producers.

- A passing Python test validates tooling only.
- Schema validation validates shape only.
- A finite certificate is not a universal statement.
- Theorem-facing generated Lean files must be deterministic and built in CI.
- Dependency revisions are pinned by `lake-manifest.json` after the first `lake update`.

## Reachability evidence tier (ADR 0009)

- Every `ReachesOne` conclusion is kernel-checked. The Lean kernel remains the final checker for reachability, exactly as for every other theorem in this repository.
- A reachability witness is admissible only when the certificate's terminal value is 1 — that is, when the claim's `Holds` reduces to `y = 1`. `FiniteOrbitClaim.singleton 1` is the canonical instance of that shape.
- No reachability theorem evaluates an orbit equation. The orbit equation at `k >= 1` is transported symbolically (`trajectory_index`, `terminal_claim_transport`), never computed.
- `native_decide` is admissible for data-side obligations only (for example the `ValidTree` / `IsComplete` checks and the parser's `ParseError` rejection cases). It may never discharge a reachability conclusion.
- A claim shape that does not reduce to `y = 1` (`.singleton n` for `n != 1`, `.bounded K`) carries no unconditional reachability witness under this tier. `.interval` is excluded from `FiniteOrbitClaim` by construction.
- The `.interval` claim shape is **not funded** (NT-5 decision 4). `LeafClaim` retains `.interval` for legacy `"2:1-1"` property decoding, but a well-formed `.interval` claim makes a `LeafCertificate`'s `claim_reaches_one` obligation range over an infinite residue class, and this tier admits no unconditional reachability witness for such a shape. No theorem in this repository discharges a `.interval` obligation. This records that the shape is unfunded; it does not assert that any particular `.interval` claim holds or fails, and it does not assert convergence, cycle exclusion, or global descent.

The tier narrows what may be claimed; it does not weaken the checker, so the trust boundary stated above is unchanged. Decision record: `docs/adr/0009-reachability-evidence-tier.md`. Regression: `Lean/CollatzResearch/ReachabilityEvidenceTierTests.lean`. The `.interval` disposition is recorded in `docs/adr/0012-record-interval-claim-as-unfunded.md`; the exclusion of `.interval` from `FiniteOrbitClaim` is pinned by `Lean/CollatzResearch/ReachabilityEvidenceTierTests.lean` Scenario 5.

## Transitive axiom tiers (ADR 0013)

The tier above fixes **which premises** a reachability theorem may
discharge by evaluation. It does not say which axioms a finished result
rests on. A result can have a kernel-only proof body and still depend
on compiler-evaluated evidence, because the **data** it quantifies over
may have been built by evaluation. ADR 0013 measures that dependency
directly and records it.

- **Every exported reachability result has a recorded trusted base.**
  `docs/theorem-axiom-manifest.json` records, per result, its tier,
  its approved axioms, and the owners and counts of its
  native-evaluation axioms, together with the exact generated axiom
  names measured on the pinned toolchain.
- **Three tiers.** `conditional_generic_theorem` and `kernel_proof`
  rest on exactly `propext`, `Classical.choice`, `Quot.sound`.
  `compiler_dependent_instance` rests on those plus the
  native-evaluation axioms it inherits.
- **Kernel-checked is a property of the result, not of the tactic.** The
  generic tier theorems are kernel-checked. The concrete two-leaf
  instances are compiler-dependent, because the fixture
  `twoLeafRoutingPartition` discharges its own well-formedness fields
  by `native_decide` and every instance that mentions it inherits that
  dependency. The tier's claim that no reachability theorem evaluates an
  orbit equation remains true; the two facts are independent.
- **The gate is transitive.** `scripts/check_theorem_axioms.py` fails
  when a recorded result's trusted base changes, and when a reachability
  result is not recorded at all. A wrapper around a natively-evaluated
  proof fails the gate even when its own tactic is kernel-only.
- **The trust boundary is unchanged.** The audit reports what already
  was true; no proof was weakened and no axiom was added to a release
  module. It narrows what may be *claimed* about a result, which is
  what the tier was for.

Decision record: `docs/adr/0013-transitive-axiom-tiers.md`.
