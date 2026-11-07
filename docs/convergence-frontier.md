# Convergence frontier

**Status:** Approved and merged - PR #105 (squash commit `515a8d52`,
2026-11-03). This document changes no theorem, no claim level, and no trust
boundary.
**Base commit:** `3f28799` (`main`) - the repository state this document
describes.

It states precisely where the formalization stops, separates what is
mechanically closable from what is open mathematics, and proposes the bounded
work packets that close the closable part.

This document does **not** assert global convergence, does not change any entry
in [`docs/theorem-status.md`](theorem-status.md), and does not change the trust
boundary described in [`docs/trust-model.md`](trust-model.md).

---

## 1. The frontier, stated

[`docs/theorem-status.md`](theorem-status.md) records exactly two rows as
unclaimed (lines 66-67):

| Identifier | Status | Lean location | Claim scope |
| --- | --- | --- | --- |
| `Global convergence` | Not started | - | No claim |
| `Nontrivial cycle exclusion` | Not started | - | No claim |

Every other row is `Checked`, `Defined (predicate)`, or `Admitted (not
established)`. Those two unclaimed rows are the *stated* frontier. This
document explains what they actually require, and what sits between them and
the current results.

## 2. The structural pattern: routing is proven, reachability is assumed

Every reachability-flavored theorem in `main` has the same two-layer shape.

**Layer 1 - routing and completeness: proven unconditionally.**

- `coverage_tree_soundness` (`CoverageTree.lean:717`) - for a valid, complete
  tree, every `x > 0` descends to a verified leaf:
  `∃ l, l ∈ t.leaves ∧ verified t l ∧ descend t x = some l`.
- `descend_orbit_complete` (`CoverageTree.lean:873`) - the orbit-aware analogue.
- `orbit_predecessor_reaches_one` (`CoverageTree.lean:180`) - transport: if a
  later orbit state reaches 1, so does the earlier one.

**Layer 2 - reachability: carried as a hypothesis.**

| Theorem | Location | Reachability premise |
| --- | --- | --- |
| `coverage_tree_soundness_full` | `CoverageTree.lean:778` | `hLeaf : ∀ l ∈ t.leaves, verified t l → LeafReachesOne t l` |
| `coverage_tree_soundness_cert` | `CoverageTree.lean:820` | `hCert : ∀ l ∈ t.leaches, verified t l → LeafCertificate t l` |
| `coverage_tree_soundness_orbit_cert` | `CoverageTree.lean:970` | `hCert : ∀ l ∈ t.leaves, verified t l → BoundedOrbitCertificate t l` |
| `coverage_tree_soundness_orbit_cert_bounded` | `Q5Integration.lean:194` | `hCert : ... → BoundedInputOrbitCertificate t l N` |
| `RoutingPartitionCertificate_sound` | `Q5RoutingPartition.lean:222` | `hClaimReachesOne` per registry entry |
| `checkBoundedCertificateTree_sound` | `BoundedInputCertificateTree.lean:117` | same, by delegation |
| `routing_trajectory_reaches_one` | `Q5RoutingPartition.lean:105` | `hAnchor`, `hTrans`, `hLast`, `hClaimReachesOne` |
| `routing_partition_witness_reaches_one` | `Q5RoutingPartition.lean:166` | `hClaimReachesOne` |
| `routing_partition_certificate_slot_reaches_one` | `Q5RoutingPartition.lean:205` | `hClaimReachesOne` |

These premises are not discharged inside the repository. They are *supplied by
the caller*. `docs/lessons-learned-meta.md` section 2.11 states this as the
governing pattern: per-leaf certificate construction is "**external** - supplied
by the caller at certificate construction time (Python oracle, finite-trajectory
checker, manual construction)", and the companion theorem "doesn't prove any new
global Collatz result; it only transports the per-leaf certificate".

**Consequence.** The formalization proves *routing* and proves *transport*. It
does not prove *reachability for any general input*. The only unconditional
reachability in `main` is fixture-local:

- `twoLeafRoutingPartition_claim_reaches_one` (`Q5Stage4Tests.lean:252`) -
  holds because both registry entries carry `FiniteOrbitClaim.singleton 1`,
  whose `Holds` reduces to `y = 1`, and `ReachesOne 1` is witnessed by
  `k := 0` (`accelerated_orbit 1 0 = 1`).
- `twoLeafRoutingPartition_reaches_one_two` (`Q5Stage4Tests.lean:369`) -
  `ReachesOne 2` from the even witness `[2, 7, 11, 17, 13, 5, 1]`.

That is the frontier in one sentence: **the repository can check that a
trajectory is an `acceleratedStep` chain and route it to a leaf; it cannot yet
check that the chain reaches 1, except for the two-leaf fixture.**

## 3. What is missing: a Lean-side verifier soundness theorem

`docs/lessons-learned-meta.md` section 3.1 prescribes the architecture:

> Python search/generator → serialized proof artifact → small Lean verifier →
> verifier soundness theorem → `BoundedOrbitCertificate` → existing companion theorem

The first, second and fifth stages exist; **the verifier soundness theorem does
not**. Verified: `git grep -E 'checkTrajectory|verifier_sound|checkReachability'`
over `Lean/` returns nothing.

What exists on the Lean side today:

- a **parser** - `BoundedInputCertificateParser.lean`, hand-rolled, kernel-clean,
  root-imported (PR #104).
- **Boolean checkers** - `checkCertWitness`
  (`BoundedInputCertificateData.lean:248`), `checkBoundedCertificate` (`:273`),
  `checkRoutingPartitionCertificate` (`:407`), `checkBoundedCertificateTree`
  (`BoundedInputCertificateTree.lean:97`).
- **decomposition lemmas** - `checkCertWitness_decompose`
  (`Q5Integration.lean:423`) rewrites the checker into `anchorOk ∧ leafMatchOk ∧
  routingOk ∧ terminalClaimOk ∧ transitionOk`; `transitionOk_implies_step` and
  `transitionOk_implies_step_forall` (`Q5BoundedInputBridge.lean:101`, `:141`)
  turn the transition fold into a per-index `acceleratedStep` equation;
  `trajectory_index` (`Q5Integration.lean:535`) and
  `trajectory_anchor_orbit_step` (`Q5Stage4Subproofs.lean:274`) index the
  trajectory against the orbit; `terminal_claim_transport`
  (`Q5Integration.lean:604`) carries the terminal claim onto the orbit.

What is missing is the final step: **from "this trajectory is a valid
`acceleratedStep` chain out of `x`" to "`x` reaches 1"**.

## 4. The decisive measurement: which evidence can be kernel-checked

The gap above is not a single missing lemma. Its shape is determined by what
the Lean kernel can actually reduce, so that was measured directly against the
pinned toolchain (Lean 4.33.0, `lean-toolchain`). Each row below was compiled
as a standalone file with `lake env lean`; the reported result is the compiler
exit code.

| Proposition | Tactic | Result |
| --- | --- | --- |
| `accelerated_orbit 2 1 = 7` | `rfl` | **FAILED** - not reducible |
| `accelerated_orbit 2 1 = 7` | `decide` | **FAILED** - reduction got stuck at the `Decidable` instance |
| `accelerated_orbit 2 1 = 7` | `native_decide` | **PROVED** - compiler-evaluated |
| `accelerated_orbit 2 6 = 1` | `rfl` | **FAILED** |
| `accelerated_orbit 2 6 = 1` | `native_decide` | **PROVED** |
| `Nat.factorization 7 2 = 0` | `decide` | **FAILED** |
| `twoAdicValuation 7 = 0` | `rfl` | **FAILED** |
| `twoAdicValuation 7 = 0` | `simp [twoAdicValuation, Nat.factorization]` | **PROVED** - kernel-checked |
| `ReachesOne 1` (`⟨0, accelerated_orbit_zero 1⟩`) | direct term | **PROVED** - kernel-checked |
| `accelerated_orbit 2 1 = 7` | `rw` + `simp` + `norm_num` | **FAILED** - unsolved goals |

This is the repo's own known limitation, recorded in
`docs/lessons-learned-meta.md` section 3.5: `acceleratedStep` routes through
`twoAdicValuation` → `Nat.factorization`, which is "opaque to kernel
reduction". The measurement above pins the consequence precisely.

**The frontier is therefore a tier boundary, not a single missing lemma:**

- `ReachesOne 1` and any reachability whose witness is `k := 0` **is**
  kernel-checkable. So is a claim whose terminal value is 1.
- A reachability witness at `k ≥ 1` is **not** kernel-reducible, and not
  provable by `decide` or by `rw`/`simp`/`norm_num` in the direct form. It is
  obtainable only via `native_decide`, which the repository already flags as
  "compiler-evaluated ... rests on the core native-decide axiom, **not
  kernel-checked**" (`docs/lessons-learned-meta.md` section 3.5, and
  `BoundedInputCertificateParserTests.lean:19-21`).

So the composition *from an accepted trajectory to `ReachesOne x`* is
kernel-checkable in exactly the case the two-leaf fixture already covers
(terminal value 1), and for every other terminal value it requires accepting
compiler-evaluated evidence for the orbit equation. That is a trust-boundary
question about evidence, not a proof-effort question, and it is the substantive
content of this frontier.

## 5. The claim shape decides what is closable

The reachability obligation is carried by `claim_reaches_one` in the
certificate structures (`CoverageTree.lean:593` for `LeafCertificate`,
`CoverageTree.lean:654` for `BoundedOrbitCertificate`,
`Q5Integration.lean:158` for `BoundedInputOrbitCertificate`). Its difficulty
is decided by the claim's shape, because `ReachesOne n` is the unbounded
existential `∃ k, accelerated_orbit n k = 1`
(`CoverageTree.lean:157`) and has **no** `Decidable` instance.

| Claim shape | `Holds` | Obligation | Closable? |
| --- | --- | --- | --- |
| `.empty` | `False` (`:449`) | vacuous | yes, trivially and kernel-checkably |
| `.singleton 1` | `y = 1` | `ReachesOne 1` | yes, kernel-checkably: `⟨0, accelerated_orbit_zero 1⟩` |
| `.singleton n`, `n ≠ 1` | `y = n` | `ReachesOne n` at some `k ≥ 1` | only with compiler-evaluated evidence, or a hand-proved orbit equation |
| `.bounded K` | `y ≤ K` | `∀ y ≤ K, ReachesOne y` | as above, per `y`; each `y ≠ 1` inherits the same issue |
| `.interval period lo hi` | `lo ≤ y % period ∧ y % period ≤ hi` | reachability of an **infinite** residue class | **no** - finitely many witnesses cannot discharge it |

Two structural facts make this the right seam to work along:

1. **`FiniteOrbitClaim` already excludes `.interval` by construction**
   (`CoverageTree.lean:434`; its docstring records that `FiniteOrbitClaim` and
   `LeafClaim` "are independent - `FiniteOrbitClaim` excludes `.interval` by
   construction; `LeafClaim` retains `.interval` for residue-only routing").
   The repository has already drawn the tractable/open boundary in its types.
2. **`LeafClaim`'s `.interval` obligation is acknowledged as unfunded**:
   `CoverageTree.lean:339` records that "No `routed_implies_claim` proof exists
   for any claim shape yet - the structural `descend t x = some l → claim.Holds x`
   obligation requires an alignment invariant that is not yet formalized".

The open mathematics is therefore concentrated in exactly one shape.

## 6. Where the open mathematics actually is

Two things are genuinely open, and neither is a work item this project can
schedule:

1. **Global convergence** - `∀ x > 0, ReachesOne x` on the accelerated map.
   This is the Collatz conjecture. `README.md` states the project "does **not**
   claim a proof of the Collatz conjecture"; `docs/mathematical-model.md`
   states it "asserts no global convergence result".
2. **Nontrivial cycle exclusion** - excluding cycles other than the trivial one.

A third item is *not* open mathematics but is currently unfunded: the
`.interval` claim shape (section 5). Its obligation is infinite, but for a
*fixed* concrete residue class it is a bounded-arithmetic statement about one
orbit family. It is tractable per instance and out of reach universally - which
is why it belongs on the open side of the seam rather than in a work packet.

## 7. Admitted-sorry ledger, and one finding that changes the plan

[`docs/lean-sorry-budget.json`](lean-sorry-budget.json) records an exact
per-file baseline of admitted *declarations* (schema 3: counted from Lean's own
`hasSorry` diagnostics, plus lexical `axiom`/`opaque`; three holes inside one
declaration count as one). Current state:

| File | Baseline | Admitted declaration |
| --- | --- | --- |
| `Lean/CollatzResearch/CoverageTree.lean` | 1 | `coverage_tree_soundness_orbit` (`:882`, `sorry` at `:888`) |

The **legacy v1.0 descent-certificate path**
(`Certificate.lean` / `Importer.lean`) is retired (decision 3, taken 2026-11-07):
the current Q5 routing-partition architecture bypasses it, and
`check_certificate_sound` depended on a SHA-256 digest whose Lean module
(`Digest.lean`) **does not exist in `main`**; only the Python side computes it
(`python/collatz_research/canonical.py`). The **proven** witness infrastructure
the retired files carried is not discarded but relocated to
`Lean/CollatzResearch/DescentWitness.lean` (`DescentWitness`,
`DescentWitness.Valid`, and its `ends_at` / `strict_descent` / `start_pos_odd` /
`trajectory_odd` lemmas).

### 7.1 The documented promotion path for `coverage_tree_soundness_orbit` is refutable

Its docstring (`CoverageTree.lean:839`) names two promotion blockers, the first
being "A formal proof of `OrbitAlignedTree t` from the existing `ValidTree t ∧
IsComplete t` hypotheses - currently `OrbitAlignedTree` is taken as an explicit
hypothesis, and the implication `ValidTree ∧ IsComplete → OrbitAligned` is open."

On the current definitions that implication is **false**, not open:

- `OrbitAlignedAux.leafA` (`:667`) requires `WellFormed l`, and
  `WellFormed` for a leaf (`:295`) is `False` whenever `leanInterval l`
  (`:259`) fails to parse, and otherwise requires
  `period > 0 ∧ lo ≤ hi ∧ hi < period`.
- `IsCompleteAux.leafC` (`:679`) requires only `verified t l`, and
  `verified` (`:253`) requires merely
  `l ∈ t.leaves ∧ l.leafProperty ≠ "" ∧ l.leafId ≠ ""`.
- `ValidNode` (`:83`) makes every leaf valid unconditionally.

A tree whose single leaf has `leafProperty = "garbage"` therefore satisfies
`ValidTree` and `IsComplete` (the string is non-empty, so `verified` holds;
`leanInterval` returns `none`, so `WellFormed` is `False`), yet fails
`OrbitAlignedTree`. So blocker (1) cannot be closed as written; it needs a
**decision**, not proof effort. Blocker (2) - Mathlib `Nat.factorization` plus
`omega` residue-bounds arithmetic for the `SatOrbit` witness - remains
arithmetic work.

Note also that `coverage_tree_soundness_orbit` concludes `SatOrbit t x l`
(residue-interval membership, `:316`) whereas the checked
`coverage_tree_soundness_orbit_cert` concludes `OrbitLeafReachesOne t l`; they
are **not** interchangeable, and `coverage_tree_soundness_orbit` is referenced by
no other theorem in `main`.

### 7.2 The budget gate is bidirectional

`scripts/check_sorry_budget.py` rejects a count *below* the recorded baseline
as well as above it. Closing any admission therefore requires lowering the
recorded number in the same change - and the current baseline is exact, so a
change that closes one declaration and forgets the JSON fails CI.

## 8. Work packets

Plan in the controller's `plan:` form. Every packet below is bounded and
kernel-checkable, and none weakens the trust boundary: Python stays an untrusted
producer, and the Lean verifier plus its soundness theorem are the only bridge
into the trusted computing base (per `docs/trust-model.md` and META section 3.5).

Note the constraint from section 4: a packet may only claim a *kernel-checked*
result if every orbit equation it relies on reduces in the kernel. In practice
that means the terminal value is 1 (witness `k := 0`). WP-CF-2 is where that
constraint becomes a maintainer decision rather than an engineering step.

```yaml
plan:
  mathematical_goal: "Derive ReachesOne from certificate-shaped data rather than assuming it, for the claim shapes whose reachability is kernel-checkable."
  computational_evidence_goal: "An untrusted producer emits trajectory witnesses; Lean kernel-checks the step relations and the terminal reachability."
  formalization_goal: "A verifier soundness theorem checkTrajectory_sound : checkTrajectory x claim w = true -> ReachesOne x, proved without native_decide in the terminal-is-1 case."

  work_packets:
    - id: "WP-CF-1"
      objective: "Prove the terminal-is-1 instance: from a checkCertWitness-accepted trajectory whose terminal value is 1, conclude ReachesOne x, using checkCertWitness_decompose, transitionOk_implies_step_forall, trajectory_index and terminal_claim_transport, with no reachability hypothesis and no native_decide. Two witnesses are distinct here: the SOURCE's orbit equality is established at the certificate's witness index (length - 1) by rewriting, never by evaluating the orbit, while the CLAIMED terminal value 1 has its own zero-step reachability witness ReachesOne 1 at k := 0 (accelerated_orbit_zero 1)."
      type: proof
      dependencies: []
      allowed_files:
        - "Lean/CollatzResearch/Q5Integration.lean"
        - "Lean/CollatzResearch/Q5BoundedInputBridge.lean"
        - "Lean/CollatzResearch/CoverageTree.lean"
      validation:
        - "GitHub Lean CI green on the PR head"
        - "No new admitted declaration; admission budget unchanged"
        - "Regression: the new theorem is stated and used by a downstream example"
      risk: low
      trust_boundary_change: false

    - id: "WP-CF-2"
      objective: "Decide the evidence tier for reachability witnesses at k >= 1. The orbit equation is not kernel-reducible (measured: rfl fails, decide fails, native_decide works), so either (a) restrict the certificate contract to claims whose terminal value is 1 and keep every result kernel-checked, (b) accept native_decide for the orbit equation and state explicitly that this evidence is compiler-evaluated and rests on the native-decide axiom, or (c) hand-prove the specific orbit equations with Mathlib lemmas per instance. Record the chosen tier in docs/trust-model.md and in the module docstrings that rely on it."
      type: proof
      dependencies: ["WP-CF-1"]
      allowed_files:
        - "Lean/CollatzResearch/CoverageTree.lean"
        - "docs/trust-model.md"
        - "docs/lessons-learned-meta.md"
      validation:
        - "GitHub Lean CI green on the PR head"
        - "Admission budget unchanged"
        - "Regression covering .empty, .singleton 1, .singleton n (n != 1), .bounded K, and .interval excluded by construction"
        - "Every claim in the affected module docstrings states which tier its evidence uses"
      risk: medium
      trust_boundary_change: true

    - id: "WP-CF-3"
      objective: "Close the composition end: derive per-leaf availability for one concrete generated tree, so that hClaimReachesOne is discharged by checked evidence rather than assumed."
      type: proof
      dependencies: ["WP-CF-2"]
      allowed_files:
        - "Lean/CollatzResearch/BoundedInputCertificateTree.lean"
        - "Lean/CollatzResearch/Q5RoutingPartition.lean"
      validation:
        - "GitHub Lean CI green on the PR head"
        - "Admission budget unchanged"
        - "docs/theorem-status.md updated in the same change if a declaration's status changes"
      risk: medium
      trust_boundary_change: false

    - id: "WP-CF-4"
      objective: "Decide the disposition of coverage_tree_soundness_orbit: delete it (no dependent theorem in main), or redefine the alignment predicate, or add a well-formedness hypothesis. Document the decision and, if deleted, lower the CoverageTree.lean admission baseline from 1 to 0 in the same change."
      type: proof
      dependencies: []
      allowed_files:
        - "Lean/CollatzResearch/CoverageTree.lean"
        - "docs/lean-sorry-budget.json"
        - "docs/theorem-status.md"
      validation:
        - "GitHub Lean CI green on the PR head"
        - "Admission budget baseline lowered in the same change"
      risk: medium
      trust_boundary_change: false

    - id: "WP-CF-5"
      objective: "Decide the disposition of the legacy v1.0 path (Importer.lean parseV1Record / parseJsonl, Certificate.lean check_certificate_sound): retire it as superseded by the Q5 routing-partition architecture, or complete it including a Lean SHA-256 module, which does not exist in main today."
      type: proof
      dependencies: []
      allowed_files:
        - "Lean/CollatzResearch/Importer.lean"
        - "Lean/CollatzResearch/Certificate.lean"
        - "docs/lean-sorry-budget.json"
      validation:
        - "GitHub Lean CI green on the PR head"
        - "Admission budget baseline lowered in the same change if admissions are closed"
      risk: high
      trust_boundary_change: true

  critical_path: ["WP-CF-1", "WP-CF-2", "WP-CF-3"]

  expected_checkpoints:
    - "WP-CF-1: a Checked theorem turning an accepted trajectory into ReachesOne, with no reachability hypothesis and no native_decide"
    - "WP-CF-2: a recorded evidence-tier decision, reflected in the trust model and in the docstrings that depend on it"
    - "WP-CF-3: per-leaf availability for one concrete tree, with the companion theorem's hypothesis discharged rather than assumed"

  known_design_decisions:
    - "WP-CF-2: DECIDED 2026-11-04 (ADR 0009) - the evidence tier for reachability witnesses at k >= 1 is kernel-checkable, restricted to claims whose terminal value is 1; no reachability theorem evaluates an orbit equation, and native_decide stays admissible for data-side obligations only"
    - "WP-CF-4: coverage_tree_soundness_orbit's documented promotion path is refutable on current definitions; choose deletion, predicate redefinition, or an added hypothesis"
    - "WP-CF-5: DECIDED 2026-11-07 (ADR 0010) - the legacy v1.0 Lean descent-certificate path is retired; the proven witness infrastructure it carried (DescentWitness, DescentWitness.Valid and its ends_at/strict_descent/start_pos_odd/trajectory_odd lemmas) is relocated to Lean/CollatzResearch/DescentWitness.lean rather than deleted, so no proven descent lemma is lost"
    - "Whether the .interval claim shape is funded at all, given its infinite obligation"
```

## 9. Open decisions for the maintainer

**Decisions 1 and 3 are now made; two remain open.** Merging this specification
approved the document; it did not resolve any of the questions below. A work
packet that depends on an open decision must not begin until that decision is
made. Decision 1 (the evidence tier for reachability witnesses) was taken on
2026-11-04 and is recorded in
[ADR 0009](adr/0009-reachability-evidence-tier.md): the tier is kernel-checkable,
restricted to claims whose terminal value is 1, and no reachability theorem
evaluates an orbit equation. That decision unblocks WP-CF-2 and, through it,
WP-CF-3. Decision 3 (the legacy v1.0 path) was taken on 2026-11-07 and is recorded in
[ADR 0010](adr/0010-legacy-v1-descent-certificate-path.md): the Lean v1.0
bridge is retired, and the **proven** witness infrastructure it carried is
relocated to `Lean/CollatzResearch/DescentWitness.lean` rather than deleted.
Decisions 2 and 4 below remain open and still gate WP-CF-4.

These are architectural or mathematical choices, so per the repository's own
review-gate rules they are maintainer decisions rather than autonomous scope:

1. **Evidence tier for reachability witnesses** (WP-CF-2) - the substantive
   question. **DECIDED 2026-11-04 - see
   [ADR 0009](adr/0009-reachability-evidence-tier.md).** The tier is
   kernel-checkable, restricted to claims whose terminal value is 1; no
   reachability theorem evaluates an orbit equation; `native_decide` remains
   admissible for data-side obligations only, unchanged.
2. **`coverage_tree_soundness_orbit`** (WP-CF-4) - the documented route to
   closing its `sorry` does not hold (section 7.1). Delete, redefine, or add a
   hypothesis?
3. **The legacy v1.0 path** (WP-CF-5) - retire `Importer.lean` /
   `Certificate.lean` as superseded, or complete them (which requires a Lean
   SHA-256 module that does not exist)? **DECIDED 2026-11-07 - retire, with the
   proven witness infrastructure RELOCATED to
   `Lean/CollatzResearch/DescentWitness.lean` rather than deleted.** See
   [ADR 0010](adr/0010-legacy-v1-descent-certificate-path.md).
4. **`.interval` claims** - fund them per instance, or leave the claim type
   unused, as `FiniteOrbitClaim` already excludes it?

Decision briefs for decisions 2, 3 and 4 - the evidence, the options, and a
recommendation for each - are in
[docs/nt5-open-decision-briefs.md](nt5-open-decision-briefs.md). It is a
brief, not a decision: each of the three still needs the maintainer's call.

## 10. Non-goals

- Asserting global convergence or nontrivial cycle exclusion.
- Promoting any entry of `docs/theorem-status.md` beyond what the evidence
  supports.
- Weakening the trust boundary so a Python-supplied witness counts as proof
  without a kernel-checked soundness theorem.
- Adding a Lean `Decidable` instance for `ReachesOne`; it is unbounded.
- Claiming the unconditional form of any companion theorem.

## 11. How each claim above was checked

Structural claims were read from `main` at `3f28799`; no claim rests on prose
alone. The reducibility claims in section 4 were measured by compiling one
standalone file per proposition with `lake env lean` against the pinned
toolchain and recording the compiler exit code. Those probe files were written
outside the repository checkout, so the working tree is unmodified; the
repository's own rule that Lean CI is the sole validation gate is unaffected, and
every claim in this document is a statement about `main` as it stands, not a
validation of a change.

| Claim | How verified |
| --- | --- |
| two unclaimed rows | `git show origin/main:docs/theorem-status.md` lines 66-67 |
| routing proven, reachability assumed | `git show` of each theorem statement; `git grep` for `hLeaf`, `hCert`, `hClaimReachesOne` |
| only two unconditional reachability facts | enumeration of every `*-reaches_one` / `ReachesOne*` declaration in `Lean/` with its premises |
| claim shapes and their obligations | `CoverageTree.lean:347`, `:357`, `:434`, `:449` |
| `FiniteOrbitClaim` excludes `.interval` | `CoverageTree.lean:428-441` docstring and constructor set |
| no `routed_implies_claim` proof | `CoverageTree.lean:339` |
| verifier soundness theorem absent | `git grep -E 'checkTrajectory|verifier_sound|checkReachability'` over `Lean/` (no hits) |
| reducibility results in section 4 | one standalone file per proposition, compiled with `lake env lean`, exit code recorded |
| admitted-declaration inventory | `docs/lean-sorry-budget.json` (schema 3) plus `git show` of each `sorry` site |
| budget gate is bidirectional | `scripts/check_sorry_budget.py` comparison loop |
| `ValidTree ∧ IsComplete` does not imply `OrbitAlignedTree` | `CoverageTree.lean:83`, `:253`, `:259`, `:295`, `:667`, `:679` |
| `Digest.lean` absent | `git ls-tree` over `Lean/` |
| `coverage_tree_soundness_orbit` has no dependent theorem | `git grep` over `Lean/` |
