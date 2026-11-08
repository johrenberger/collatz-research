# ADR 0011 - Delete `coverage_tree_soundness_orbit`

- **Status:** Accepted (maintainer decision, 2026-11-07)
- **Decides:** NT-5 decision 2 in `docs/convergence-frontier.md` section 9
- **Work packet:** WP-CF-4
- **Related:** [ADR 0010](0010-legacy-v1-descent-certificate-path.md) (decision 3); [ADR 0009](0009-reachability-evidence-tier.md) (decision 1, the evidence tier)

## Context

`coverage_tree_soundness_orbit` (in `Lean/CollatzResearch/CoverageTree.lean`) stated:

```lean
theorem coverage_tree_soundness_orbit (t : CoverageTree)
    (hv : ValidTree t) (hic : IsComplete t) (ha : OrbitAlignedTree t)
    (x : Nat) (hx : x > 0) :
    exists l, l in t.leaves /\ verified t l /\ descendOrbit t x 0 = some l /\ SatOrbit t x l
```

Its body was admitted via `sorry`. Its docstring named two promotion blockers, the first being a formal proof of `OrbitAlignedTree t` from the existing `ValidTree t /\ IsComplete t` hypotheses.

That first blocker is **false on the current definitions**, not merely open (frontier section 7.1): a one-leaf tree whose `leafProperty` is not a parseable interval satisfies `verified`, `ValidTree`, and `IsComplete`, yet fails `OrbitAlignedTree`, because `OrbitAlignedAux.leafA` requires `WellFormed l` and `WellFormed` is `False` whenever `leanInterval` cannot parse the leaf property.

The theorem also has no consumer. Its conclusion `SatOrbit t x l` is residue-interval membership, and it is **not interchangeable** with the checked companion `coverage_tree_soundness_orbit_cert`, which concludes the strictly stronger `OrbitLeafReachesOne t l`. A grep over `Lean/`, `python/`, `tests/`, and `scripts/` finds no theorem that depends on it - only prose references.

## Decision

**Delete the theorem.** The repository stops carrying a statement whose conclusion nothing uses and whose documented route to establishment is refuted rather than merely unproven.

## Consequences

- The `Lean/CollatzResearch/CoverageTree.lean` admission baseline drops from 1 to **0**, recorded in the same change in `docs/lean-sorry-budget.json`. The budget script enforces this bidirectionally, so the baseline and the code must move together.
- After this change and [ADR 0010](0010-legacy-v1-descent-certificate-path.md), the release-relevant Lean modules carry **no** admitted declarations.
- `docs/theorem-status.md` loses the `coverage_tree_soundness_orbit` row.
- The checked orbit-aware certificate theorem `coverage_tree_soundness_orbit_cert` is **unaffected**: it is proved from `descend_orbit_complete` and an explicit `BoundedOrbitCertificate` hypothesis, and does not depend on the deleted theorem.
- The `SatOrbit` and `OrbitAlignedTree` predicates are **kept**. They are the invariant the refutation was stated against, the Python side mirrors `SatOrbit` semantics, and `OrbitAlignedAux` remains the documented alignment structure. They become unused by any Lean theorem, which is intentional: they record the seam that was refuted rather than silently disappearing.
- The two prose references to the deleted theorem in `CoverageTree.lean` are corrected to name `coverage_tree_soundness_orbit_cert` and ADR 0011 respectively.

## Alternatives considered

- **(a) Delete** - **chosen**, above.
- **(b) Redefine the alignment predicate** - rejected: it is a definitional change to the tree model, not a repair of a proof, and every consumer of `OrbitAlignedTree` would need re-checking.
- **(c) Add a hypothesis** - rejected: the theorem would survive with an honest hypothesis, but `SatOrbit` still has no consumer, so the admission would remain in the budget without buying a result.

## Evidence

| Claim | How verified |
| --- | --- |
| The theorem's body is admitted | `CoverageTree.lean`, `sorry` in the theorem body |
| `ValidTree /\ IsComplete` does not imply `OrbitAlignedTree` | The frontier's section 7.1 refutation, with a one-leaf witness whose `leafProperty` does not parse |
| No dependent theorem | `grep` over `Lean/`, `python/`, `tests/`, `scripts/` finds only prose references |
| `SatOrbit` and `OrbitLeafReachesOne` are not interchangeable | The two theorem statements side by side |
| `coverage_tree_soundness_orbit_cert` does not depend on the deleted theorem | Its proof uses `descend_orbit_complete` and an explicit `BoundedOrbitCertificate` hypothesis |

## Scope note

This change exceeds the frontier's WP-CF-4 `allowed_files`, which listed `CoverageTree.lean`, `docs/lean-sorry-budget.json`, and `docs/theorem-status.md`. The recommended option additionally requires the frontier itself (its section 7 ledger, its section 7.1 note, its section 9 decision record) and the decision briefs, because the repository must not record a decision in documents that still describe the old state. The extra files are listed explicitly in the pull request so the reviewer can check them against scope.
