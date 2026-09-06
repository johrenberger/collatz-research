# Story 07c-3 — Orbit-aware routing correctness

## Claim level

**Formally established structural-routing result.** This story introduces no
`sorry`, `admit`, axiom, or opaque trust extension. It makes no local-descent
or convergence claim.

## Objective

Prove that a complete, valid coverage tree selects each internal edge using
the actual accelerated orbit of its input. The result connects the tree's
routing mechanism to the dynamics, but deliberately does not infer semantic
meaning from a leaf's string metadata.

## Required Lean interface

```lean
def descendOrbitFrom :
  Nat → Nat → CoverageNode → Nat → Option CoverageLeaf
-- orbit index, remaining depth, node, initial input

def descendOrbit (t : CoverageTree) (x : Nat) : Option CoverageLeaf :=
  descendOrbitFrom 0 t.maxDepth t.root x

inductive OrbitRoute (t : CoverageTree) (x : Nat) :
  Nat → CoverageNode → CoverageLeaf → Prop
-- At an internal node with modulus m at index i, the selected edge is labelled
-- accelerated_orbit x i % m. A terminal node contains the returned leaf.

@[simp] theorem accelerated_orbit_zero (x : Nat) :
  accelerated_orbit x 0 = x := rfl

@[simp] theorem accelerated_orbit_succ (x i : Nat) :
  accelerated_orbit x (i + 1) =
    acceleratedStep (accelerated_orbit x i) := rfl

theorem descend_orbit_complete
  (t : CoverageTree) (hv : ValidTree t) (hc : IsComplete t)
  (x : Nat) (hx : 0 < x) :
  ∃ l, l ∈ t.leaves ∧ verified t l ∧
    descendOrbit t x = some l ∧ OrbitRoute t x 0 t.root l
```

`SatOrbit t x l := ∃ k, ...` is expressly out of scope. Its witness is not
tied to a tree-path index and therefore cannot establish routing correctness.

## BDD test-first gate

MiniMax must add these tests **before implementation**. The first commit must
fail only because `descendOrbit`, `OrbitRoute`, and the theorem do not yet
exist. The implementation commit makes the same tests pass; it must not weaken
their assertions.

### Lean executable specifications

Put these as `example` blocks in a new
`Lean/CollatzResearch/CoverageTreeOrbitTests.lean`, imported by its explicit
CI target.

| Scenario | Given | When | Then |
| --- | --- | --- | --- |
| Base orbit | natural `x` | evaluate `accelerated_orbit x 0` | result is `x` |
| One step | `0`, `1`, even `8`, odd `5` | evaluate `accelerated_orbit x 1` | result unfolds to `acceleratedStep x`; exact values are `1`, `1`, `25`, `1` |
| Leaf root | valid one-leaf tree and positive `x` | run `descendOrbit` | return that leaf and construct a terminal `OrbitRoute` witness |
| Depth-one route | modulus-4 root with children | select input with residue `r` | select the child labelled `accelerated_orbit x 0 % 4` |
| Depth-two route | two-level complete tree | choose `x` where `x % m₀` differs from `acceleratedStep x % m₁` | select the second edge using the step-one orbit state, never raw `x` |
| Completeness | concrete valid complete depth-two tree and `0 < x` | apply `descend_orbit_complete` | obtain leaf membership, verification, exact `descendOrbit` result, and `OrbitRoute` |
| Zero boundary | valid complete tree | attempt main theorem at `x = 0` | no proof is available without `0 < x`; do not add a zero convergence statement |

The depth-two scenario is mandatory: it distinguishes orbit-aware routing from
the existing `descend`, which routes every level with `x % m`.

### Python BDD tests

Add the following scenarios to `tests/test_coverage_tree.py` before adding the
production implementation.

```python
def test_descend_orbit_routes_second_level_by_step_one_state():
    # Given a depth-two tree whose second modulus distinguishes x from T(x)
    # When descend_orbit(tree, x) runs
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

The test oracle must not call `descendOrbit`, `descend_orbit`, or their shared
recursion helper.

## Required execution sequence

1. Commit the Lean and Python BDD tests labelled `test-first`.
2. Record the expected failures:

   ```text
   lake build CollatzResearch.CoverageTreeOrbitTests
   uv run pytest tests/test_coverage_tree.py -q
   ```

3. Implement the definitions, relation, lemmas, and theorem.
4. Re-run the same commands. Add the explicit Lean target to Ubuntu CI.
5. Codex review must inspect the test-first commit, final diff, CI logs, and
   the absence of any new admission or convergence claim.

## Non-goals

- No `ReachesOne`, finite local descent, or global-convergence theorem.
- No inference from `leafProperty : String` to semantic validity.
- No bounded Python computation used as proof authority.
- No change to the existing structural `coverage_tree_soundness` theorem.

## Follow-on semantic contract

A later story may introduce a typed, proof-bearing leaf contract:

```lean
def LeafApplies (l : CoverageLeaf) (z : Nat) : Prop := ...
def LeafCertificate (l : CoverageLeaf) : Prop :=
  ∀ z, LeafApplies l z → ∃ k, accelerated_orbit z k < z
```

If these certificates cover all positive inputs, they are substantive
local-descent research and can support a separate strong-induction convergence
theorem. They are not scaffolding.
