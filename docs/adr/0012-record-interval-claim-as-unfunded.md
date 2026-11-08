# ADR 0012 - Record the `.interval` claim shape as unfunded

- **Status:** Accepted (maintainer decision, 2026-11-08)
- **Decides:** NT-5 decision 4 in `docs/convergence-frontier.md` section 9
- **Related:** [ADR 0009](0009-reachability-evidence-tier.md) (decision 1, the reachability evidence tier); [ADR 0010](0010-legacy-v1-descent-certificate-path.md) (decision 3); [ADR 0011](0011-remove-coverage-tree-soundness-orbit.md) (decision 2)

## Context

Two claim types exist, and they sit on opposite sides of the
tractable/open boundary:

- `FiniteOrbitClaim` (Q4, orbit-aware routing) has three constructors -
  `.empty`, `.singleton n`, `.bounded K` - and no `.interval` constructor.
  The exclusion is structural.
- `LeafClaim` (Q3, residue-only routing) retains `.interval period lo hi`,
  and `parse_leaf_claim` decodes a legacy `"2:1-1"` property into it.

The obligation is what makes `.interval` expensive. For a `.interval`
claim, `LeafClaim.Holds x` is `lo ≤ x % period ∧ x % period ≤ hi`, and the
`claim_reaches_one` obligation of `LeafCertificate` is
`∀ x, claim.Holds x → ReachesOne x`.

For every interval a `LeafCertificate` can actually carry, that
obligation is over an infinite set rather than a bounded enumeration: the
certificate's `well_formed` field requires `LeafClaim.WellFormed`, i.e.
`period > 0 ∧ lo ≤ hi ∧ hi < period`, so the residue class is non-empty
and infinite. (The public constructor still permits malformed intervals
such as `.interval 0 0 0` or `.interval 2 2 1`; those denote a finite or
empty set and cannot be carried by a certificate.)

Two facts bound what can be funded:

1. ADR 0009 restricts the reachability evidence tier to claims whose
   `Holds` reduces to `y = 1`. An `.interval` claim does not reduce to
   `y = 1`, so it carries **no unconditional reachability witness** under
   the tier - exactly like `.singleton n` for `n != 1` and `.bounded K`.
2. The `.interval` shape is residue-only routing territory. The
   orbit-aware certificate type `BoundedOrbitCertificate` takes a
   `FiniteOrbitClaim`, so `.interval` cannot enter the orbit-aware path
   at all.

The `LeafCertificate` type therefore permits a `.interval` claim
structurally, while the obligations it carries make populating a
well-formed one an unbounded commitment.

## Decision

**Leave the claim type unused and record it.** The repository states
plainly that no `.interval` reachability obligation is funded, and no
code changes.

## Consequences

- The claim type is unchanged. `LeafClaim.interval` stays, legacy
  `"2:1-1"` decoding keeps working, and `LeafClaimTests.lean` and the
  Python-side `lean_interval` / `leaf_in_interval` helpers are untouched.
- `docs/trust-model.md` gains an explicit statement that the `.interval`
  shape is not funded, next to the ADR 0009 tier it sits under.
- The `LeafClaim` docstring in `Lean/CollatzResearch/CoverageTree.lean`
  states that a well-formed `.interval` claim's obligation is unbounded
  and that no theorem in this repository discharges it.
- The exclusion of `.interval` from `FiniteOrbitClaim` stays pinned by an
  existing regression: `Lean/CollatzResearch/ReachabilityEvidenceTierTests.lean`
  Scenario 5 case-splits over `FiniteOrbitClaim`'s three constructors, so
  adding a fourth breaks it at elaboration time. No new test is needed.
- This decision asserts **no** convergence, cycle exclusion, or global
  descent result. It states which obligations the repository declines to
  fund.
- The shape stays on the open side of the seam (`docs/convergence-frontier.md`
  section 6). Funding a concrete residue class would be a new maintainer
  decision, scoped as its own work packet, and it would require proving that
  an infinite class reaches 1.

## Alternatives considered

- **(a) Leave unused and record it** - **chosen**, above.
- **(b) Fund per instance** - rejected: each funded instance requires
  proving that an infinite residue class reaches 1, which is the unbounded
  obligation ADR 0009 rejected, and it does not compose with a certificate
  pipeline.
- **(c) Remove `.interval` from `LeafClaim`** - rejected: it breaks legacy
  `"2:1-1"` property decoding, the `LeafClaimTests.lean` scenarios that
  exercise it, and the Python-side helpers that mirror it - a
  cross-language breaking change for a shape with no funded user.

## Evidence

| Claim | How verified |
| --- | --- |
| `FiniteOrbitClaim` excludes `.interval`; `LeafClaim` retains it | The inductive definitions and their constructor sets in `CoverageTree.lean` |
| The exclusion is pinned by a regression | `ReachabilityEvidenceTierTests.lean` Scenario 5, which case-splits over the three constructors |
| The `.interval` obligation is infinite **for well-formed intervals** | `LeafClaim.Holds` and `LeafCertificate.claim_reaches_one` in `CoverageTree.lean`; malformed intervals are excluded by the certificate's `well_formed` field, which requires `LeafClaim.WellFormed` (`period > 0 ∧ lo ≤ hi ∧ hi < period`) |
| `.interval` cannot enter the orbit-aware path | `BoundedOrbitCertificate` takes a `FiniteOrbitClaim` |
| ADR 0009 admits no unconditional reachability witness for `.interval` | The ADR 0009 tier, which requires `Holds` to reduce to `y = 1` |
| Legacy decoding and its tests still work | `parse_leaf_claim` and `LeafClaimTests.lean` scenarios 1, 6 and 7; the Python-side `lean_interval` / `leaf_in_interval` helpers in `python/collatz_research/tree.py` |
