# ADR 0009: The reachability evidence tier is kernel-checkable, restricted to terminal value 1

Status: accepted. A reachability witness is admissible only when the
certificate's terminal value is 1. Every reachability conclusion is then
proved in the Lean kernel, and no reachability theorem evaluates an orbit
equation. `native_decide` remains admissible for data-side obligations only,
exactly as it is today.

## Context

`docs/convergence-frontier.md` section 9 listed four decisions for the
maintainer. This record resolves the first: the evidence tier for reachability
witnesses (work packet `WP-CF-2`).

The question is forced by a measurement, not by preference. Section 4 of the
frontier document records that an orbit equation at `k >= 1` is not
kernel-reducible: `rfl` fails, `decide` gets stuck at the `Decidable`
instance, and only `native_decide` closes it. The same measurement records
that the terminal-is-1 case IS kernel-checkable (`ReachesOne 1` via
`accelerated_orbit_zero 1`, `CoverageTree.lean:123`).

The decision turns on why those two facts sit together. `ReachesOne` is
defined as

```
ReachesOne n := ∃ k, accelerated_orbit n k = 1      -- CoverageTree.lean:170
```

so a reachability conclusion needs an orbit that reaches 1. A certificate
supplies the orbit's VALUES; it does not supply the equation `accelerated_orbit
x k = <value>` as something the kernel can evaluate. The kernel-side chain
transports that equality instead:

- `trajectory_index` (`Q5Integration.lean:570`) proves
  `trajectory[k]! = accelerated_orbit x k` by induction, rewriting with
  `accelerated_orbit_zero` (`CoverageTree.lean:123`) and `accelerated_orbit_succ`
  (`CoverageTree.lean:130`). Both are `rfl`; neither evaluates an orbit
  equation.
- `terminal_claim_transport` (`Q5Integration.lean:650`) rewrites the terminal
  value to `accelerated_orbit x (length - 1)` and applies the claim's `Holds`.
- `orbit_predecessor_reaches_one` (`CoverageTree.lean:193`) closes a
  predecessor's reachability from a successor's.

Now split on the terminal value `y` the certificate attests:

- **`y = 1`.** The claim's `Holds` reduces to `y = 1`, so the terminal fact IS
  the orbit equation the conclusion needs: `accelerated_orbit x k = 1` for
  `k = length - 1`. The kernel obtains it by rewriting and concludes
  `ReachesOne x`. The `k` is supplied by the certificate, and the orbit is
  never evaluated.
- **`y != 1`.** The terminal fact gives `accelerated_orbit x k = y`. To turn
  that into `ReachesOne x` one must continue the orbit from `y` to 1, which
  requires evaluating `acceleratedStep` on `y` - that is, computing
  `twoAdicValuation`/`Nat.factorization`, which is exactly the reduction
  section 4 measured as not kernel-reducible.

So the tier boundary and the claim-shape boundary are the same boundary, and
that is why the two questions in the frontier document are not independent.
The terminal value is what decides whether the conclusion is reachable without
evaluating an orbit.

This is inhabited, not hypothetical. Two unconditional reachability facts
already exist and already have this shape: `twoLeafRoutingPartition_claim_reaches_one`
(`Q5Stage4Tests.lean:257`) and `twoLeafRoutingPartition_reaches_one_two`
(`Q5Stage4Tests.lean:386`). Both are built on `FiniteOrbitClaim.singleton 1`,
whose `Holds` reduces to `y = 1`, and the second one concludes `ReachesOne 2` -
a witness at `k >= 1` - without evaluating an orbit.

The obligations needed to admit such a witness are already kernel-clean:
`transitionOk_implies_step_forall` (`Q5BoundedInputBridge.lean:160`) turns
`transitionOk w = true` into per-step `acceleratedStep` facts, and
`checkCertWitness_decompose` (`Q5Integration.lean:453`) splits acceptance into
its conjuncts.

The three options on the table were: keep every result kernel-checkable by
restricting claims to a terminal value of 1; accept `native_decide` for the
orbit equation and say so in the trust model; or hand-prove orbit equations
per instance.

## Decision

- **Tier: kernel-checkable, restricted to terminal value 1.** A reachability
  witness is admissible only when the certificate's terminal value is 1. The
  orbit equation at `k >= 1` is never evaluated on the reachability path: it
  is transported symbolically, as `trajectory_index` and
  `terminal_claim_transport` already do.
- **No reachability theorem evaluates an orbit equation.** The Lean kernel
  remains the final checker for every `ReachesOne` conclusion. This narrows
  what may be claimed; it does not weaken the checker, so the trust boundary
  in `docs/trust-model.md` is unchanged.
- **`native_decide` remains admissible for data-side obligations**, exactly as
  it is today, and is unaffected by this record. The existing data-side sites
  stay disclosed as they are: `ValidTree depthTwoTree` and `IsComplete
  depthTwoTree` in `Q5Integration.lean:292-293`, and the parser's `ParseError`
  constructor in `BoundedInputCertificateParser.lean:112-113` and `:155`,
  which already state in prose that this "rests on the core native-decide
  axiom, not kernel-checked". A certificate's Boolean acceptance is a
  data-side obligation of this kind and is unchanged by this decision; what
  this decision fixes is that no REACHABILITY THEOREM may discharge its own
  conclusion that way.
- **The witness shape is the record of the tier.** A claim whose `Holds`
  reduces to `y = 1` is a terminal-value-1 claim; `FiniteOrbitClaim.singleton 1`
  is its canonical instance. Shapes that do not reduce to `y = 1`
  (`.singleton n` for `n != 1`, `.bounded K`) carry no unconditional
  reachability witness under this tier. `.interval` remains excluded by
  construction (`FiniteOrbitClaim` has no `.interval` constructor,
  `CoverageTree.lean:463`).
- **The scope of this record is the tier decision only.** It does not assert
  global convergence, does not promote any row of `docs/theorem-status.md`,
  and does not claim that any new declaration is proven. `WP-CF-1`
  (terminal-is-1 instance), `WP-CF-2` (recording the tier in the trust model
  and the affected docstrings), and `WP-CF-3` (per-leaf availability) remain
  separate work packets.

## Consequences

- `WP-CF-2` is unblocked and proceeds under this tier: it records the tier in
  `docs/trust-model.md` and in the module docstrings that rely on it, and its
  regression covers `.empty`, `.singleton 1`, `.singleton n` for `n != 1`,
  `.bounded K`, and `.interval` excluded by construction.
- `WP-CF-3` becomes reachable, since per-leaf availability is now stated in
  terms of a terminal-value-1 witness.
- The frontier does not advance to a general `k >= 1` orbit equation, and this
  record does not claim it will. Option (b) was rejected because it would move
  a reachability conclusion off the kernel, contradicting the trust model this
  repository has maintained since ADR 0003. Option (c) was rejected as
  unbounded: hand-proving orbit equations per instance is an infinite
  obligation in the same shape as the `.interval` question (decision 4), and it
  does not compose with a certificate pipeline.
- The remaining three decisions are unaffected: the
  `coverage_tree_soundness_orbit` disposition (decision 2), the legacy v1.0
  path (decision 3), and whether `.interval` claims are funded (decision 4).
