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

The tier narrows what may be claimed; it does not weaken the checker, so the trust boundary stated above is unchanged. Decision record: `docs/adr/0009-reachability-evidence-tier.md`. Regression: `Lean/CollatzResearch/ReachabilityEvidenceTierTests.lean`.
