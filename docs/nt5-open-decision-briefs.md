# NT-5 open decisions: briefs for the maintainer

This brief supports the three NT-5 maintainer decisions that remain open in
`docs/convergence-frontier.md` § 9, after decision 1 was taken in
[ADR 0009](adr/0009-reachability-evidence-tier.md).

Decision 1 (the evidence tier for reachability witnesses) is **decided** and
its work packet (WP-CF-2) is in flight in PR #108. This document covers
decisions 2, 3 and 4.

It is a **decision brief, not a decision.** Each section states the question,
the evidence for it, the options, and what each option would commit the
repository to. Nothing here asserts a theorem, promotes a
`docs/theorem-status.md` row, or claims that any admitted declaration is
established.

---

## Decision 2 — the disposition of `coverage_tree_soundness_orbit` (WP-CF-4)

### The question

The theorem's own docstring names two promotion blockers. The first is a
formal proof of `OrbitAlignedTree t` from the existing `ValidTree t ∧
IsComplete t` hypotheses. The frontier document (§ 7.1) records that this
implication is **false on the current definitions**, not merely open, so
blocker 1 cannot be closed as written.

### The evidence

`coverage_tree_soundness_orbit` is declared in
`Lean/CollatzResearch/CoverageTree.lean` and concludes `SatOrbit t x l`
(residue-interval membership), **not** `OrbitLeafReachesOne t l`. The two
are not interchangeable, and `grep` finds no theorem in `main` that depends
on it — only prose references, including one in `Certificate.lean`.

The refutation has a concrete witness. A one-leaf tree whose leaf has
`leafProperty := "garbage"` satisfies:

- `verified` — the leaf is listed and both string fields are non-empty;
- `ValidTree` — `maxDepth > 0` and a leaf node is always valid
  (`ValidNode _ (.leaf _) = True`);
- `IsComplete` — the leaf is in `leaves` and `verified`;

yet fails `OrbitAlignedTree`, because `OrbitAlignedAux.leafA` requires
`WellFormed l`, and `WellFormed` is `False` whenever `leanInterval`
cannot parse the leaf property. This was checked by compiling a standalone
probe against the pinned toolchain outside the repository working tree; the
three structural facts above are proved constructively.

### The options

| Option | What it does | What it commits to |
|---|---|---|
| **(a) Delete** | Remove the declaration. | The repository stops carrying a theorem whose conclusion (`SatOrbit`) nothing uses and whose documented route to establishment is refuted. The `CoverageTree.lean` admission baseline drops from 1 to 0 in the same change, and `docs/theorem-status.md` loses the `coverage_tree_soundness_orbit` row. |
| **(b) Redefine the alignment predicate** | Change `OrbitAlignedAux` so that the implication is true — e.g. weaken `leafA` to require `verified` instead of `WellFormed`, or drop the leaf-level clause. | A new structural invariant is introduced, and every proof that used `OrbitAlignedTree` must be re-checked against it. This is a definitional change to the tree model, not a repair of a proof. |
| **(c) Add a hypothesis** | Keep the theorem, and add the well-formedness/alignment condition it actually needs to its statement. | The theorem survives with an honest hypothesis, but the conclusion `SatOrbit` still has no consumer, so the admission stays in the budget without buying a result. |

### The recommendation

**(a) Delete.** The theorem has no dependent theorem, its conclusion is not
interchangeable with the checked `coverage_tree_soundness_orbit_cert`, and
its documented promotion path is refuted rather than merely unproven. Deleting
it also lowers the admission baseline in the same change, which the
bidirectional budget gate requires (§ 7.2). Options (b) and (c) both spend
effort on a statement the repository does not use.

### What any of these options would need

Whichever is chosen, the change must touch `CoverageTree.lean`,
`docs/lean-sorry-budget.json` (lower the baseline in the same change) and
`docs/theorem-status.md` (drop the row if deleted), and must keep Lean CI
green on the PR head.

---

## Decision 3 — the disposition of the legacy v1.0 path (WP-CF-5)

### The question

Retire `Importer.lean` / `Certificate.lean` as superseded by the Q5
routing-partition architecture, or complete them — which requires a Lean
SHA-256 module that does not exist in `main` today.

### The evidence

The legacy path is three admitted declarations across two files:

| File | Admitted declaration | Notes |
|---|---|---|
| `Importer.lean` | `parseV1Record` | The v1.0 JSONL record parser body is a `sorry`. |
| `Importer.lean` | `parseJsonl` | The JSONL splitter body is a `sorry`. |
| `Certificate.lean` | `check_certificate_sound` | Three `sorry` holes for the parser-derived constraints `0 < r.start`, `Odd r.start`, `r.target < r.start`. |

They are **not** dead code in the sense of being unreferenced: the root
module `Lean/CollatzResearch.lean` imports both, and
`tests/test_checker_lean.py` imports `CollatzResearch.Certificate` to
evaluate `CollatzResearch.trajectory` against the Python checker. That
import is what the differential test needs today.

The blocking dependency is real: `check_certificate_sound`'s anti-circularity
argument rests on a SHA-256 digest of the proof-bearing fields, and only the
Python side computes it (`python/collatz_research/canonical.py`,
`compute_digest`). There is no `Digest.lean` in `main`. Completing the
Lean side therefore means writing a Lean SHA-256 implementation — a
significant, self-contained piece of work with its own correctness burden.

The Python side of the same format is alive and tested (`parser.py`,
`canonical.py`, `checker.py`, `certificates.py`), so retiring the **Lean**
v1.0 path does not retire the v1.0 format.

### The options

| Option | What it does | What it commits to |
|---|---|---|
| **(a) Retire** | Remove `Importer.lean` and `Certificate.lean`, drop their root imports, lower both admission baselines to 0 in the same change, and re-point `tests/test_checker_lean.py` at the module that actually defines `trajectory` (`Basic.lean`). | The Lean side stops claiming a v1.0 descent-certificate bridge it cannot discharge. The Python v1.0 tooling stays. The admission budget drops by three declarations. |
| **(b) Complete** | Implement the parsers and the SHA-256 digest in Lean and discharge the three `check_certificate_sound` holes. | A Lean SHA-256 module becomes a dependency of the trusted computing base — which is a larger trust-boundary change than the frontier packet's `trust_boundary_change: true` flag implies. |
| **(c) Keep as is** | Leave the three admissions in place with no change. | The budget keeps three admitted declarations for a path the current architecture bypasses, and the digest gap stays undocumented in the trust model. |

### The recommendation

**(a) Retire**, with the test re-pointing made explicit in the same change.
Two of the three admissions are parser plumbing, and the third depends on a
digest implementation that does not exist in Lean. Option (b) is a genuine
project — a Lean SHA-256 module is a substantial addition to the trusted
computing base and should be scoped as its own story rather than as the
tail of a disposition decision.

### What any of these options would need

The change must touch `Importer.lean`, `Certificate.lean`,
`docs/lean-sorry-budget.json`, the root import list, and
`tests/test_checker_lean.py`, and must keep both CI gates green (Lean CI
and Python CI).

---

## Decision 4 — whether `.interval` claims are funded

### The question

Fund `.interval` claims per instance, or leave the claim type unused, as
`FiniteOrbitClaim` already excludes it?

### The evidence

The two claim types already sit on opposite sides of this line, and this is
the current state rather than an open question about the architecture:

- `FiniteOrbitClaim` (Q4, orbit-aware routing) has three constructors —
  `.empty`, `.singleton n`, `.bounded K` — and **no** `.interval`
  constructor. The exclusion is structural.
- `LeafClaim` (Q3, residue-only routing) retains `.interval period lo hi`,
  and `parse_leaf_claim` decodes a legacy `"2:1-1"` property into it.

The obligation is what makes `.interval` expensive. For a `.interval`
claim, `LeafClaim.Holds x` is `lo ≤ x % period ∧ x % period ≤ hi`. The
`claim_reaches_one` obligation of `LeafCertificate` is
`∀ x, claim.Holds x → ReachesOne x`.

The infinite-obligation statement is about **well-formed** intervals as
carried by a `LeafCertificate`, and it is worth being exact about that:

- The public `LeafClaim` constructor permits malformed intervals —
  `.interval 0 0 0` or `.interval 2 2 1` are constructible directly — and
  such a claim denotes a finite or empty set, not an infinite one.
- A `LeafCertificate` cannot carry one: its `well_formed` field requires
  `LeafClaim.WellFormed`, which for `.interval period lo hi` is
  `period > 0 ∧ lo ≤ hi ∧ hi < period`.
- So for every `.interval` claim a `LeafCertificate` can actually carry,
  the residue set is non-empty and the class is infinite, and
  `claim_reaches_one` demands that **every** member of it reaches 1.

That is not a per-instance obligation in any bounded sense.

Two facts bound what can be funded:

1. ADR 0009 (decision 1) restricts the reachability evidence tier to claims
   whose `Holds` reduces to `y = 1`. An `.interval` claim does not reduce
   to `y = 1`, so it carries **no unconditional reachability witness** under
   the tier, exactly like `.singleton n` for `n != 1` and `.bounded K`.
2. The `.interval` shape is residue-only routing territory; the orbit-aware
   certificate type (`BoundedOrbitCertificate`) takes a
   `FiniteOrbitClaim`, so `.interval` cannot enter the orbit-aware path at
   all.

The current `LeafCertificate` type takes a `LeafClaim` and therefore
*permits* a `.interval` claim structurally, while the obligations it carries
make populating a well-formed one an unbounded commitment. That gap is the
actual decision.

### The options

| Option | What it does | What it commits to |
|---|---|---|
| **(a) Leave unused** | Keep `.interval` excluded from the orbit-aware path (already true) and state in the trust model and the affected docstrings that it is not funded. | The `.interval` constructor stays in `LeafClaim` for legacy decoding, and the repository states plainly that it carries no funded reachability obligation. No new obligation is created. |
| **(b) Fund per instance** | Populate well-formed `.interval` claims for specific residue classes. | Each funded `.interval` claim requires proving that an infinite residue class reaches 1. That is the same unbounded obligation as decision 1's rejected option (c), and it does not compose with a certificate pipeline. |
| **(c) Remove `.interval` from `LeafClaim`** | Delete the constructor. | Breaks legacy `"2:1-1"` property decoding, the `LeafClaimTests.lean` scenarios that exercise it, and the Python-side `lean_interval`/`leaf_in_interval` helpers that mirror it. A cross-language change for a shape with no funded user. |

### The recommendation

**(a) Leave unused**, and record it: state in the trust model that
`.interval` claims are not funded, and note in the `LeafClaim`
docstring that the `LeafCertificate` obligations make populating a
well-formed one an unbounded commitment. This matches what ADR 0009 already
implies for the other non-terminal-value shapes, and it costs no new
obligation.

Option (c) is the only one that removes the gap structurally, but it costs a
cross-language breaking change for a shape with no funded user — and option
(a) closes the same gap by making the obligation explicit rather than
implicit. Option (b) is the unbounded obligation in a different name.

### What any of these options would need

The change is documentation-level under (a): `docs/trust-model.md` and the
affected `CoverageTree.lean` docstrings, with a regression that pins
`.interval`'s exclusion from `FiniteOrbitClaim`. Under (c) it also touches
the Lean and Python claim types and their tests.

---

## How the evidence above was checked

| Claim | How verified |
| --- | --- |
| The three decisions are open; decision 1 is taken | `docs/convergence-frontier.md` § 9, read on this branch |
| ADR 0009 is the decision record for decision 1 | `docs/adr/0009-reachability-evidence-tier.md`, merged in PR #107 |
| `coverage_tree_soundness_orbit` has no dependent theorem | `grep` over `Lean/`, `python/`, `tests/`, `scripts/`, `docs/` for the bare name, excluding the `_cert` variant |
| Its conclusion is `SatOrbit`, not `OrbitLeafReachesOne` | The theorem statement in `CoverageTree.lean` |
| `ValidTree ∧ IsComplete` does not imply `OrbitAlignedTree` | A standalone probe compiled with `lake env lean` against the pinned toolchain, outside the repository working tree; the `ValidTree`/`IsComplete`/`verified` facts are proved constructively |
| `WellFormed` fails when `leanInterval` cannot parse the property | Same probe; the string-parsing step uses `native_decide` because `String.split` is opaque to kernel reduction |
| The legacy path's three admitted declarations | `docs/lean-sorry-budget.json`, plus the `sorry` sites in `Importer.lean` and `Certificate.lean` |
| The legacy path has no Lean SHA-256 module | `ls Lean/CollatzResearch/Digest.lean` (absent); the Python digest is in `canonical.py` |
| `tests/test_checker_lean.py` depends on `CollatzResearch.Certificate` | The generated Lean fixture's `import CollatzResearch.Certificate` |
| `FiniteOrbitClaim` excludes `.interval`; `LeafClaim` retains it | The inductive definitions and their constructor sets in `CoverageTree.lean` |
| The `.interval` obligation is infinite **for well-formed intervals** | `LeafClaim.Holds` and `LeafCertificate.claim_reaches_one` in `CoverageTree.lean`; malformed intervals are excluded by the certificate's `well_formed` field, which requires `LeafClaim.WellFormed` (`period > 0 ∧ lo ≤ hi ∧ hi < period`) |

---

## Appendix: the decision-2 probe, in full

The refutation of `ValidTree ∧ IsComplete → OrbitAlignedTree` is checked by
compiling this file against the pinned toolchain, **outside the repository
working tree** (so the working tree stays unmodified), and recording the
exit code:

```
cd <repo>
lake env lean /tmp/nt5-probe-decision2.lean   # exit code 0 = all examples compile
```

```lean
import CollatzResearch.CoverageTree

namespace Probe

open CollatzResearch

/-- A leaf whose `leafProperty` is not a parseable interval. -/
def garbageLeaf : CoverageLeaf :=
  { leafId := "l0", leafProperty := "garbage" }

/-- The single-leaf tree built on it. -/
def garbageTree : CoverageTree :=
  { root := .leaf garbageLeaf, leaves := [garbageLeaf], maxDepth := 1 }

/-- `verified` holds: the leaf is listed and both string fields are
    non-empty. Proved constructively. -/
example : verified garbageTree garbageLeaf := by
  simp [verified, garbageTree, garbageLeaf]

/-- `ValidTree` holds: maxDepth > 0 and a leaf node is always valid.
    Proved constructively. -/
example : ValidTree garbageTree := by
  simp [ValidTree, ValidNode, garbageTree]

/-- `IsComplete` holds: the leaf is in `leaves` and `verified`.
    Proved constructively. -/
example : IsComplete garbageTree := by
  refine IsCompleteAux.leafC garbageLeaf ?_ ?_
  · simp [garbageTree]
  · simp [verified, garbageTree, garbageLeaf]

/-- But `WellFormed` fails: `leanInterval` cannot parse "garbage". -/
example : ¬ WellFormed garbageLeaf := by
  native_decide

/-- Therefore `OrbitAlignedTree` fails for this tree. Proved
    constructively from the inductive structure. -/
example : ¬ OrbitAlignedTree garbageTree := by
  intro h
  have hnot : ¬ WellFormed garbageLeaf := by native_decide
  cases h with
  | leafA l hw => exact hnot hw

/-- The refutation, stated as one proposition: the documented implication
    `ValidTree ∧ IsComplete → OrbitAlignedTree` does not hold. -/
example : ¬ (ValidTree garbageTree ∧ IsComplete garbageTree →
              OrbitAlignedTree garbageTree) := by
  intro h
  have hv : ValidTree garbageTree := by
    simp [ValidTree, ValidNode, garbageTree]
  have hc : IsComplete garbageTree := by
    refine IsCompleteAux.leafC garbageLeaf ?_ ?_
    · simp [garbageTree]
    · simp [verified, garbageTree, garbageLeaf]
  have hnot : ¬ WellFormed garbageLeaf := by native_decide
  cases h ⟨hv, hc⟩ with
  | leafA l hw => exact hnot hw

end Probe
```

**Trust note.** The two propositions about string parsing use
`native_decide`, because `String.split` is opaque to kernel reduction. That
is a compiler-evaluated fact about a STRING, not about the reachability
semantics under test. Every proposition about `ValidTree`, `IsComplete`,
`verified` and `OrbitAlignedTree` is proved constructively from the
definitions.
