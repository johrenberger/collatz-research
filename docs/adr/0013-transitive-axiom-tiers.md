# ADR 0013 - Transitive axiom tiers for exported results

- **Status:** Accepted (2026-11-15)
- **Implements:** Story R01 in `docs/collatz-next-stories.md`
- **Related:** [ADR 0009](0009-reachability-evidence-tier.md) (the reachability evidence tier, which this record clarifies); [ADR 0012](0012-record-interval-claim-as-unfunded.md)

## Context

ADR 0009 fixed the reachability evidence tier: a reachability witness is
admissible only when the certificate's terminal value is 1, and
`native_decide` stays admissible for data-side obligations only, never
for discharging a reachability conclusion.

That decision reasons about **premises**. It says which obligations a
reachability theorem may discharge by evaluation and which it must
discharge symbolically. It says nothing about the **trusted base** a
finished result actually rests on.

The gap is visible in the repository's own concrete instances. The
terminal-value-one tier is discharged by the *generic* theorems
`RoutingPartitionCertificate_sound_terminal_value_one`
(`Q5RoutingPartition.lean:346`) and
`routing_partition_certificate_slot_reaches_one_terminal_value_one`
(`Q5RoutingPartition.lean:303`), and by the per-leaf constructors
`routing_partition_leaf_certificate_terminal_value_one`
(`BoundedInputCertificateTree.lean:400`) and
`per_leaf_available_bounded_of_check_terminal_value_one`
(`BoundedInputCertificateTree.lean:417`). Those are the tier's
substance, and they are the results the repository cites.

The concrete two-leaf instances rest on those generic theorems, but they
also mention a **fixture**: `twoLeafRoutingPartition`
(`Q5VerifierTests.lean:278`). That fixture's proof fields are
discharged by `native_decide`:

```lean
registry_unique := by native_decide,
witness_claim_registered := by
  intro w hw
  ...
  · native_decide
```

So the dependency does not arrive through the instance's own proof. It
arrives through the **data** the instance is about. Measured on the
pinned toolchain (Lean 4.33.0) with `#print axioms`:

| Result | Own proof uses `native_decide`? | Transitive native axioms |
| --- | --- | --- |
| `RoutingPartitionCertificate_sound_terminal_value_one` | no | 0 |
| `RoutingPartitionCertificate_sound` | no | 0 |
| `routing_partition_leaf_certificate_terminal_value_one` | no | 0 |
| `per_leaf_available_bounded_of_check_terminal_value_one` | no | 0 |
| `twoLeafRoutingPartition_claim_reaches_one` | no | 3 |
| `twoLeafRoutingPartition_registry` | no | 3 |
| `twoLeafRoutingPartition_reaches_one_two` | yes | 4 |
| `twoLeafRoutingPartition_sound_terminal_value_one` | yes | 4 |
| `twoLeaf_per_leaf_available_bounded_of_check_terminal_value_one` | yes | 4 |
| `twoLeaf_routing_partition_leaf_certificate` | yes | 4 |

The row that matters is the third: `twoLeafRoutingPartition_claim_reaches_one`
has a **kernel-only proof body** and still depends on three
native-evaluation axioms, because the claim registry it quantifies over
lives inside the natively-evaluated fixture.

The existing documentation states the tier's conclusion as "every
`ReachesOne` conclusion is kernel-checked"
(`docs/lessons-learned-meta.md` section 3.5, `docs/trust-model.md`).
For the generic theorems that is true. For the instantiated results it
is not, and no sentence in the repository said which was which.

## Decision

**Classify every exported reachability result by its measured trusted
base, record that classification, and gate it in CI.**

1. **Three tiers.** An exported result is one of:
   - `conditional_generic_theorem` - kernel-clean, statement carries
     hypotheses;
   - `kernel_proof` - kernel-clean, unconditional;
   - `compiler_dependent_instance` - depends on compiler-evaluated
     evidence, whether directly or through the data it quantifies over.

   The first two tiers rest on exactly the approved standard axiom set
   (`propext`, `Classical.choice`, `Quot.sound`). The third rests
   on that set **plus** the native-evaluation axioms it inherits.

2. **A machine-readable manifest.**
   `docs/theorem-axiom-manifest.json` records, for every exported
   reachability result, its tier, its approved axioms, the owners and
   counts of its native axioms, and the exact generated axiom names
   measured on the pinned toolchain.

3. **A transitive release gate.** `scripts/check_theorem_axioms.py`
   re-measures every recorded result with `#print axioms` and fails
   when a result's trusted base changed. The check is transitive by
   construction, so a wrapper around a natively-evaluated proof fails
   the gate even when the wrapper's own tactic is kernel-only. The gate
   also fails when a result is not recorded at all, so a new reachability
   theorem cannot enter the trusted surface unclassified.

4. **Compiler-dependent fixtures stay usable.** The two-leaf instances
   remain in the repository and remain usable as regression fixtures.
   They are simply classified honestly, in their own tier, instead of
   being presented as kernel-only results.

5. **Discovery is bounded by declaration boundaries.** The gate
   discovers exported results by scanning declarations, so a
   declaration whose type does not end on its own line must not
   consume the declaration that follows it. A swallowed declaration
   would never enter the manifest, and the "every exported reachability
   result is recorded" check would then pass over a result it never
   saw. The scanner therefore stops a declaration at the next
   declaration, and a test asserts that every declaration the
   pattern matches is returned.

6. **ADR 0009 stands.** This record does not weaken, replace, or extend
   the reachability evidence tier. The tier still says that no
   reachability theorem evaluates an orbit equation, and that remains
   true: the measurements above show native axioms in the trusted base
   of the instantiated results, but no orbit equation is evaluated on
   any reachability path. What this record adds is the distinction
   between a tier that is kernel-checkable and a result that is
   kernel-checkable.

## Consequences

- **The trust boundary is unchanged.** No proof changed, no theorem was
  weakened, and no axiom was added to any release module. The audit
  reports what already was true.
- **No global convergence claim changes.** Nothing here asserts
  convergence, cycle exclusion, or global descent. The two unclaimed rows
  of `docs/theorem-status.md` stay unclaimed.
- **The documentation becomes exact.** The sentence "every `ReachesOne`
  conclusion is kernel-checked" is now scoped: the tier's generic
  theorems are kernel-checked, and the concrete instances that mention a
  natively-evaluated fixture are compiler-dependent. That distinction
  is the substance of this record.
- **The gate is a release gate, not a lint.** A result that acquires a
  native dependency, or an admission, fails CI until the manifest is
  re-recorded deliberately with `--update` and the change is reviewed.
- **The manifest is toolchain-pinned.** It records the toolchain it was
  measured against, exactly as `docs/lean-sorry-budget.json` records
  its own baseline. A toolchain bump re-measures it.

## Alternatives considered

- **(a) Keep reasoning about premises only, and state the tier more
  carefully in prose** - rejected: prose is what the audit was written
  to replace. The distinction between "this theorem's proof is
  kernel-only" and "this result rests only on the kernel" is exactly
  the distinction a reader cannot check by reading the proof.
- **(b) Re-prove the fixture without `native_decide`** - rejected for
  this record: it is a real option and a separate story. The fixture's
  well-formedness fields are decidable Boolean checks that Mathlib may
  be able to evaluate in the kernel. That work would move results
  between tiers rather than establish the tiers, and it is not R01's
  scope.
- **(c) Delete or quarantine the two-leaf instances** - rejected: they
  are the repository's regression coverage for the tier, and the shared
  acceptance contract keeps compiler-dependent test fixtures usable
  under an explicitly separate category.
- **(d) Gate on `native_decide` occurrences in the source text**
  - rejected: a source scan cannot see a dependency that arrives
  through data, which is the case this record exists to catch.

## Evidence

| Claim | How verified |
| --- | --- |
| generic tier theorems are kernel-clean | `#print axioms` on the pinned toolchain; each reports exactly `propext`, `Classical.choice`, `Quot.sound` |
| concrete instances depend on native axioms | `#print axioms`; the exact generated names are recorded per result in `docs/theorem-axiom-manifest.json` |
| the dependency arrives through the fixture, not the proof body | `twoLeafRoutingPartition_claim_reaches_one` has a kernel-only proof body and still reports the fixture's three native axioms |
| no orbit equation is evaluated on a reachability path | unchanged from ADR 0009; the audit measures dependencies, not orbit equations |
| the gate catches a wrapper around a native proof | self-test case `indirect wrapper around a native proof` in `scripts/check_theorem_axioms.py` |
| the gate catches an admitted proof | self-test case `admitted proof`; the admission budget gate in `scripts/check_sorry_budget.py` remains the primary admission check |
| the gate catches a directly native proof | self-test case `direct native proof` |
| a clean result passes the gate | self-test case `known clean proof` |
| every exported reachability result is recorded | `test_every_exported_reachability_result_is_recorded` in `tests/test_theorem_axioms.py` |
| discovery does not drop a declaration | `test_scanner_drops_no_declaration_it_matches` and `test_one_line_declaration_does_not_swallow_the_next` in `tests/test_theorem_axioms.py`; the scanner returns every declaration the pattern matches |
