# Story 07c-4 — Structural-routing completeness for orbit-aware descent

## Claim level

**Formally established structural-routing result.** This story introduces no
`sorry`, `admit`, axiom, or opaque trust extension in `CoverageTree.lean`.
It makes no convergence claim. Promotion from `preparatory` to `formally
established` requires: (a) `descend_orbit_complete` proved with no `sorry`,
(b) Python BDD test-first gate executed per `Required execution sequence`,
(c) GitHub CI green on `lake build` (including the explicit Lean target),
(d) Codex review pass on the final diff, CI logs, and absence of any new
`sorry` / `admit` / axiom.

**Lean validation rule (project-wide):** Lean source changes are validated
by GitHub CI only — `lake build` is not run locally for this story. The
Python BDD tests are run locally as usual. The Lean executable specs in
`CoverageTreeOrbitTests.lean` are compile-checked by CI, not by a local
BDD gate.

## Objective

Prove that a complete, valid coverage tree's orbit-aware descent selects
each internal edge using the actual accelerated orbit of its input, and
returns a leaf whose membership, verification, exact `descendOrbit`
result, and `OrbitRoute` witness can all be recovered from the hypotheses.
The result mirrors the structural-routing proof already on master for
`coverage_tree_soundness`, but threads the orbit index through the
recursion so that the residue at depth `k` is `accelerated_orbit x k % m`
rather than `x % m`.

## Post-mortem on PR #23

PR #23 (`Story 07c-4 (test-first, preparatory): BDD executable specs for
orbit routing contract`, head `3922c34`, base `47ff858`) was closed without
merge on 2026-08-15T01:17:03Z. The closure was caused by a broader
infrastructure issue addressed outside the 07c-4 scope. The substantive
framing — test-first BDD gate, claim level `preparatory`, no proof rewrite
in the test-first commit — was not the reason for closure. This story
re-derives the contract fresh against current master (`dcd35f5`) rather
than carrying the closed PR's commit message forward verbatim.

## Required Lean interface

The 07c-3 inherited contract
(`docs/story-07c-3-proof-rewrite.md`) names these symbols. The current
master source uses slightly different surface names; this story adopts
the master source as authoritative and documents the bridge.

```lean
-- Already on master (Lean/CollatzResearch/CoverageTree.lean, lines 100–139).
-- Arg order matches the 07c-3 doc: (depth, node, x, k) where k is the
-- orbit index, incremented at each internal step.
def descendFromOrbit : Nat → CoverageNode → Nat → Nat → Option CoverageLeaf

def descendOrbit (t : CoverageTree) (x : Nat) (k : Nat) : Option CoverageLeaf :=
  descendFromOrbit t.maxDepth t.root x k

-- New in this story. Matches the 07c-3 spec exactly:
--   - OrbitRoute t x i n l: at internal node with modulus m at orbit
--     index i, the selected edge is labelled `accelerated_orbit x i % m`.
--   - Terminal node contains the returned leaf.
inductive OrbitRoute (t : CoverageTree) (x : Nat) :
    Nat → CoverageNode → CoverageLeaf → Prop

-- New in this story. Proven by mirroring `coverage_tree_soundness`
-- (CoverageTree.lean, lines 261–322): Nat induction on depth, `cases n`
-- on `CoverageNode`, residue `accelerated_orbit x k % m` in the IH step.
theorem descend_orbit_complete
    (t : CoverageTree) (hv : ValidTree t) (hc : IsComplete t)
    (x : Nat) (hx : 0 < x) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         OrbitRoute t x 0 t.root l
```

### Signature bridge (master vs. 07c-3 spec)

The 07c-3 spec asks for a 2-arg `descendOrbit (t : CoverageTree) (x : Nat)`
that delegates to `descendOrbitFrom 0 t.maxDepth t.root x`. Master defines
a 3-arg `descendOrbit (t : CoverageTree) (x : Nat) (k : Nat)` that
delegates to `descendFromOrbit t.maxDepth t.root x k`. The shapes are
equivalent: master exposes `k` as a parameter; the 07c-3 entry point is
the special case `k = 0`. This story adopts master's signature so the
existing `coverage_tree_soundness_orbit` statement (which already uses
`descendOrbit t x 0`) is not disturbed. BDD scenarios that read
`descendOrbit t x` from the 07c-3 doc use `descendOrbit t x 0` here.

### `SatOrbit` is out of scope

Per the 07c-3 spec, `SatOrbit` is not part of this story's contract. The
existing `coverage_tree_soundness_orbit` theorem (CoverageTree.lean
line 324) and its `sorry` (line 330) belong to a separate workstream
(provisional label `07c-5 / dynamics connection`) and are not modified
here.

## Test-first gate

The Python BDD tests are test-first and run locally. The Lean executable
specs and implementation are CI-validated; no local `lake build` is
attempted. There is no separate "Lean test-first commit" — Lean code
lands in the implementation commit, and CI is the gate.

### Python BDD tests

Add to `tests/test_coverage_tree.py` in the test-first commit, run
locally, and record the expected failures:

```python
def test_descend_orbit_routes_second_level_by_step_one_state():
    # Given a depth-two tree whose second modulus distinguishes x from T(x)
    # When descend_orbit(tree, x) runs (with k=0)
    # Then it returns the child indexed by accelerated_orbit(x, 1) % modulus
    ...

def test_descend_orbit_leaf_root_is_immediate():
    # Given a one-leaf tree and positive input
    # When descend_orbit runs
    # Then it returns the leaf without requiring an orbit step
    ...

def test_descend_orbit_rejects_negative_input():
    # Given input outside Lean Nat
    # When descend_orbit runs
    # Then it raises ValueError
    ...

def test_descend_orbit_agrees_with_independent_trace_oracle():
    # Given generated shallow complete trees and bounded positive inputs
    # When descend_orbit runs
    # Then it agrees with an iterative test-only route oracle
    ...
```

The test oracle must not call `descendOrbit`, `descend_orbit`, or their
shared recursion helper. The pytest run is expected to fail because the
Python `descend_orbit` entry point is not yet exported; record that
failure.

### Lean executable specifications (CI-validated)

The Lean executable specs serve as a CI-side contract and regression
check. They live in a new
`Lean/CollatzResearch/CoverageTreeOrbitTests.lean` (per the 07c-3
spec) and are compile-checked by `lake build` in CI. They are not run
locally — Lean validation is a CI-only activity for this project.

| Scenario | Given | When | Then |
| --- | --- | --- | --- |
| Base orbit | natural `x` | evaluate `accelerated_orbit x 0` | result is `x` |
| One step | `0`, `1`, even `8`, odd `5` | evaluate `accelerated_orbit x 1` | result unfolds to `acceleratedStep x`; exact values are `1`, `1`, `25`, `1` |
| Leaf root | valid one-leaf tree and positive `x` | run `descendOrbit t x 0` | return that leaf and construct a terminal `OrbitRoute` witness |
| Depth-one route | modulus-4 root with children | select input with residue `r` | select the child labelled `accelerated_orbit x 0 % 4` |
| Depth-two route | two-level complete tree | choose `x` where `x % m₀` differs from `acceleratedStep x % m₁` | select the second edge using the step-one orbit state, never raw `x` |
| Completeness | concrete valid complete depth-two tree and `0 < x` | apply `descend_orbit_complete` | obtain leaf membership, verification, exact `descendOrbit t x 0` result, and `OrbitRoute` |
| Zero boundary | valid complete tree | attempt main theorem at `x = 0` | no proof is available without `0 < x`; do not add a zero convergence statement |

The depth-two scenario is mandatory: it distinguishes orbit-aware routing
from the existing `descend`, which routes every level with `x % m`.

## Proof strategy

Mirror the proven `coverage_tree_soundness` proof (CoverageTree.lean
lines 261–322). That proof already solves the "induction on `CoverageNode`
does not generalize" problem by not inducting on `CoverageNode`. It
inducts on `depth : Nat` and then does plain `cases n` on the node:

```lean
suffices h : ∀ (depth : Nat),
    ∀ (n : CoverageNode), ValidNode depth n → IsCompleteAux t n →
    ∀ x, x > 0 →
      ∃ l, l ∈ t.leaves ∧ verified t l ∧ descendFrom depth n x = some l
intro depth
induction depth using Nat.rec with
| zero =>
  intro n hvn hic x hx
  cases n with
  | leaf l => ...
  | internal m children => exact False.elim hvn
| succ depth' ih =>
  intro n hvn hic x hx
  cases n with
  | leaf l => ...
  | internal m children =>
    -- residue computation: x % m (existing) vs accelerated_orbit x k % m (this story)
    have hx_mod : accelerated_orbit x k % m < m := Nat.mod_lt _ hm
    -- construct OrbitRoute witness alongside the IH step
```

The only structural change versus `coverage_tree_soundness` is:

1. The residue is `accelerated_orbit x k % m` (orbit-aware) rather than
   `x % m` (raw), with `k` threaded through the recursion.
2. The IH additionally produces an `OrbitRoute t x (k + 1) child l`
   witness at each internal step, threaded into the terminal
   `OrbitRoute t x k (.internal m children) l` constructor.
3. `descendOrbit t x 0` is the entry point; `k = 0` at the root.

The two escape hatches named in PR #23's commit message
(`CoverageNode.rec` with explicit motive; well-founded recursion on
`ValidTree t`) are valid alternatives but not necessary given the proven
Nat-induction + node-`cases` pattern already on master. This story
chooses the proven pattern.

## Required execution sequence

1. Branch off current master (`dcd35f5`):
   `git switch -c story-07c-4-restart-structural-routing`.
2. **Test-first commit (Python only).** Add the Python BDD tests to
   `tests/test_coverage_tree.py`. Run `uv run pytest tests/test_coverage_tree.py -q`
   locally and record the expected failure (missing `descend_orbit`).
   Commit labelled `test-first`. **Claim level on opening this commit:
   `preparatory`.**
3. **Implementation commit (Lean + Python).** Implement:
   - `OrbitRoute t x i n l` in `CoverageTree.lean`.
   - `descend_orbit_complete t hv hc x hx` in `CoverageTree.lean`.
   - The proof using the proven `coverage_tree_soundness` shape (Nat
     induction on depth, `cases n` on node, orbit-aware residue, IH
     threading the `OrbitRoute` witness).
   - The Lean executable spec in
     `Lean/CollatzResearch/CoverageTreeOrbitTests.lean` (per the 07c-3
     contract).
   - The Python `descend_orbit` entry point that makes the Python BDD
     tests from step 2 pass.
   Do **not** modify `coverage_tree_soundness_orbit`, `coverage_tree_soundness`,
   or any other existing theorem or definition outside the additions above.
4. Push the branch. **No local `lake build` is run.** GitHub CI runs
   `lake build` (including any explicit Lean target added per the 07c-3
   precedent in `.github/workflows/`). If CI is red, fix the Lean code
   and push a follow-up commit; do not weaken the executable specs or
   the proof.
5. Open PR. PR body must include: PR #23 closure reference, the proven
   proof-strategy section above verbatim, the Lean executable spec
   scenarios table, the local Python pytest log showing the test-first
   failure and the post-implementation pass, the CI logs from step 4,
   and a `git blame`-style diff summary on `CoverageTree.lean`.
6. Codex review must inspect the final diff, CI logs, and the absence of
   any new `sorry` / `admit` / axiom. On Codex pass, merge. **Claim
   level on merge: `formally established`.**

## Non-goals

- No `ReachesOne`, finite local descent, or global-convergence theorem.
- No inference from `leafProperty : String` to semantic validity.
- No bounded Python computation used as proof authority.
- No change to the existing structural `coverage_tree_soundness` theorem.
- No change to `coverage_tree_soundness_orbit` or its `sorry`. That is a
  separate workstream.
- No `SatOrbit`-shaped additions to `descend_orbit_complete`'s statement.

## Promotion criteria

| Claim level | Conditions |
| --- | --- |
| `preparatory` | Python test-first commit landed; local pytest failure recorded; PR opened at this commit; no `CoverageTree.lean` changes yet. |
| `formally established` | Implementation commit landed; `descend_orbit_complete` proved with no `sorry`; Lean executable specs compile-checked by CI; Python BDD tests pass locally; GitHub CI green on `lake build` (and any explicit Lean target); Codex review pass. |

## Follow-on

After `formally established`, M4 Finite coverage closes pending 07c-2
(dynamics connection) and 07c-3 (proof rewrite — separate workstream) at
`formally established`. The `coverage_tree_soundness_orbit` `sorry`
(line 330) is the natural next story (provisional: 07c-5), but is out of
scope here.
