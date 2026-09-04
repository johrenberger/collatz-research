# Story Q5 — Global Input-to-Leaf Routing-Partition Certificates

## Status and scope

This is the follow-up to merged PR #64.  It replaces the **single fixed
leaf** checker interface with architecture **(b)**: one bounded certificate
whose canonical input positions are routed to their own leaves.  It is a
design specification only; it adds no Lean definitions, checker, parser, or
soundness theorem.

The existing `checkBoundedCertificate t l d` is intentionally preparatory:
its fixed `l` cannot represent a bounded domain whose inputs route to
multiple leaves.  No theorem removed from PR #64 is reintroduced here.

## Goal

For a concrete coverage tree `t` and bound `N`, a global certificate must
provide one trajectory witness for every input in `{1, ..., N}`, identify
the leaf reached by that input, and associate that leaf with one finite orbit
claim.  Lean must recompute the routing and trajectory checks; external
certificate data remains untrusted.

The intended future soundness conclusion is bounded and conditional:

```lean
checkRoutingPartitionCertificate t d = true ->
  (forall x, 0 < x -> x <= d.N -> ReachesOne x)
```

It additionally requires the explicit hypothesis that each accepted finite
claim reaches one.  It is not a global Collatz claim and it does not assert
anything for `x = 0` or `x > N`.

## Data model

### Canonical input assignment

The certificate has `N` witness slots.  Slot `i : Fin N` represents exactly
`i.val + 1`; the input is not trusted as a wire field.  A witness contains:

```lean
structure RoutingWitnessWire where
  leaf : CoverageLeaf
  trajectory : List Nat
```

The checked view retains the indexed type:

```lean
RoutingWitness d i : Type  -- witness for input i.val + 1
```

This preserves PR #66's important type-level canonical-input identity.

### Leaf-claim registry

Claims are leaf-indexed rather than global:

```lean
structure LeafClaimWire where
  leaf : CoverageLeaf
  claim : FiniteOrbitClaim
```

The checked registry must establish, with a local fieldwise leaf comparison:

1. no duplicate leaf entries;
2. every witness leaf resolves to exactly one registry claim; and
3. no global `BEq CoverageLeaf` instance is introduced merely for this
   certificate format.

The design permits a registry entry for a leaf with no input in the current
bound.  Soundness obligations are required only for inputs `1..N`.

### Checked global bundle

The future checked bundle contains the wire payload plus proofs/validated
facts for list length, claim-registry uniqueness, and total claim lookup for
witness leaves.  Parser/schema work remains a separate untrusted-input
boundary; it must construct this bundle only by explicit rejection checks.

## Checker contract

`checkRoutingPartitionCertificate t d : Bool` folds over `Fin d.N`.  At each
canonical input `x = i.val + 1`, it recomputes all of:

1. nonempty trajectory with head `x`;
2. fieldwise equality of the witness leaf and the recomputed
   `descendOrbit t x 0` result;
3. lookup of that leaf's unique registry claim;
4. terminal membership in that claim; and
5. all adjacent accelerated-orbit transitions.

Acceptance is therefore a global routing partition over the bounded input
domain, not a statement that every input routes to one supplied leaf.

## Soundness boundary

The eventual proof is split in two layers:

1. **Checker soundness:** accepted canonical witness `i` supplies a valid
   trajectory ending in the registered claim for its recomputed routed leaf.
2. **Reachability composition:** an explicit hypothesis maps each registered
   claim membership to `ReachesOne`; trajectory indexing plus
   `orbit_predecessor_reaches_one` yields `ReachesOne (i.val + 1)`.

No `sorry`, default certificate, external-generator assertion, or universal
per-leaf acceptance is permitted.  A future optional theorem may package the
per-input facts into leaf-indexed bounded certificates, but only after the
registry-to-leaf quantifiers are proved correct.

## Work packets

```yaml
plan:
  mathematical_goal: >-
    Represent and verify a bounded global input-to-leaf routing partition;
    later derive bounded reachability from accepted trajectories and explicit
    claim-reachability hypotheses.
  computational_evidence_goal: >-
    Define a deterministic Bool checker for all canonical inputs 1..N and
    regressions for multi-leaf routing, lookup failure, duplicate claims, and
    wrong-route witnesses.
  formalization_goal: >-
    Kernel-check checker decomposition and bounded soundness without adding
    proof debt; keep parser and external producer untrusted.
  work_packets:
    - id: Q5-RP-1
      objective: Specify the routing-partition certificate contract.
      type: infrastructure
      dependencies: []
      allowed_files: [docs/story-q5-routing-partition.md]
      validation: [git diff --check]
      risk: low
      trust_boundary_change: false
    - id: Q5-RP-2
      objective: Add wire and checked routing-partition data definitions.
      type: parser
      dependencies: [Q5-RP-1]
      allowed_files: [Lean/CollatzResearch/BoundedInputCertificateData.lean]
      validation: [lake build CollatzResearch.BoundedInputCertificateData]
      risk: medium
      trust_boundary_change: false
    - id: Q5-RP-3
      objective: Implement the global Bool checker and focused regressions.
      type: test
      dependencies: [Q5-RP-2]
      allowed_files: [Lean/CollatzResearch/BoundedInputCertificateData.lean, Lean/CollatzResearch/Q5VerifierTests.lean]
      validation: [lake build CollatzResearch.BoundedInputCertificateData, lake build CollatzResearch.Q5VerifierTests]
      risk: medium
      trust_boundary_change: false
    - id: Q5-RP-4
      objective: Prove accepted-witness decomposition and bounded per-input soundness.
      type: proof
      dependencies: [Q5-RP-3]
      allowed_files: [Lean/CollatzResearch/Q5RoutingPartition.lean, Lean/CollatzResearch/Q5RoutingPartitionTests.lean, docs/theorem-status.md]
      validation: [lake build CollatzResearch.Q5RoutingPartition, lake build CollatzResearch.Q5RoutingPartitionTests, python3 scripts/check_sorry_budget.py]
      risk: high
      trust_boundary_change: false
    - id: Q5-RP-5
      objective: Compose bounded reachability with explicit registered-claim hypotheses.
      type: proof
      dependencies: [Q5-RP-4]
      allowed_files: [Lean/CollatzResearch/Q5RoutingPartition.lean, Lean/CollatzResearch/Q5RoutingPartitionTests.lean, docs/theorem-status.md]
      validation: [lake build CollatzResearch.Q5RoutingPartition, lake build CollatzResearch.Q5RoutingPartitionTests, make ci]
      risk: high
      trust_boundary_change: false
  critical_path: [Q5-RP-1, Q5-RP-2, Q5-RP-3, Q5-RP-4, Q5-RP-5]
  expected_checkpoints: [Q5-RP-1, Q5-RP-2, Q5-RP-3, Q5-RP-4, Q5-RP-5]
  known_design_decisions:
    - Architecture (b): global input-to-leaf routing partition.
    - Inputs are canonical list positions 1..N; zero is outside the domain.
    - Claims are registered per leaf with local fieldwise comparison.
    - Soundness remains conditional on explicit claim-reachability hypotheses.
```

## Non-goals

- Reopening PR #64's removed `checkBoundedCertificate_sound` theorem.
- A global convergence theorem or any claim beyond the explicit bound.
- JSON parser or Python generator implementation.
- Changing the Lean/Python trust boundary or adding FFI/native execution.
