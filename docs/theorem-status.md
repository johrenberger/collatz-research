# Theorem status

| Identifier | Status | Lean location | Claim scope |
| --- | --- | --- | --- |
| `trajectory_zero` | Checked | `CollatzResearch.Basic` | Definitional base case |
| `trajectory_succ` | Checked | `CollatzResearch.Basic` | One-step unfolding |
| `standardStep_positive` | Pending | `CollatzResearch.Dynamics` | Standard step preserves positivity on positive domain (definition only; proof TODO) |
| `acceleratedStep_positive_of_odd` | Pending | `CollatzResearch.Dynamics` | Accelerated step preserves positivity on odd domain (definition only; proof TODO) |
| `standardTrajectory_zero` | Checked | `CollatzResearch.Equivalence` | Definitional base case |
| `standardTrajectory_succ` | Checked | `CollatzResearch.Equivalence` | One-step unfolding |
| `acceleratedStep_equiv_standardStep` | Pending | `CollatzResearch.Equivalence` | One accelerated step on odd domain = 1 + ν₂(3n+1) standard steps (definition only; proof TODO) |
| `acceleratedTrajectory_reaches_one_implies_standard` | Pending | `CollatzResearch.Equivalence` | Accelerated trajectory reaching 1 lifts to a finite standard trajectory reaching 1 (definition only; proof TODO) |
| `AffineMap.comp_assoc` | Checked | `CollatzResearch.Affine` | Composition of affine maps is associative |
| `AffineMap.comp_id_left` | Checked | `CollatzResearch.Affine` | `AffineMap.id` is a left identity for composition |
| `AffineMap.comp_id_right` | Checked | `CollatzResearch.Affine` | `AffineMap.id` is a right identity for composition |
| `AffineMap.comp_apply_eq` | Pending | `CollatzResearch.Affine` | Apply-level composition equality under explicit divisibility hypotheses (admitted `sorry`; pending Mathlib `Int.mul_div_cancel_left_of_dvd` lemma check) |
| `BranchWord.toAffine` | Defined (@[simp] auto-generated equations) | `CollatzResearch.Affine` | Empty / cons decomposition of the induced affine map (no custom-named lemmas; auto-generated `@[simp]` equations suffice) |
| `BranchWord.appliesTo` | Defined (predicate) | `CollatzResearch.Affine` | Symbolic validity: word applies to `n` iff positive odd + each step's valuation matches `ν₂(3nᵢ + 1)` |
| `BranchWord.execute` | Defined (function) | `CollatzResearch.Affine` | Operational executor: `execute (k :: rest) n = execute rest ((3*n+1)/2^k)` |
| `BranchWord.execute_eq_toAffine_apply` | Pending | `CollatzResearch.Affine` | Executing a branch word equals applying its induced affine map under `appliesTo` (empty case proved by `rfl`; cons case admitted `sorry` pending `comp_apply_eq`) |
| `Residue` | Defined (predicate) | `CollatzResearch.Residues` | `r < m` (canonical representative of a residue class) |
| `residue` | Defined (function) | `CollatzResearch.Residues` | `residue m n = n % m` |
| `residue_lt` | Checked | `CollatzResearch.Residues` | `residue m n < m` when `m > 0` |
| `residue_zero` | Checked | `CollatzResearch.Residues` | `residue m 0 = 0` (true for all `m`, including `m = 0`; no positivity hypothesis) |
| `Partition` | Defined (structure) | `CollatzResearch.Residues` | Completeness + disjointness + validity for a residue partition |
| `Partition.trivial` | Defined (function) | `CollatzResearch.Residues` | `[0, 1, ..., m-1]` |
| `Partition.trivial_mem` | Checked | `CollatzResearch.Residues` | `r ∈ [0, m) ↔ r < m` (via `List.mem_range`) |
| `Partition.trivial_nodup` | Checked | `CollatzResearch.Residues` | The trivial partition has no duplicates (via `List.nodup_range`) |
| `Partition.trivial_valid` | Checked | `CollatzResearch.Residues` | All elements of the trivial partition are `< m` |
| `Partition.trivial_complete` | Checked | `CollatzResearch.Residues` | The trivial partition covers all of `[0, m)` |
| `Partition.trivial_partition` | Defined (function) | `CollatzResearch.Residues` | The trivial partition as a valid `Partition m` |
| `DescentWitness.Valid` | Defined (predicate) | `CollatzResearch.Certificate` | A valid local-descent witness has positive-odd start, the declared accelerated-trajectory endpoint, and target strictly below start (P1 from PR #10 Codex review: odd-domain invariant matching Python's `accelerated_step`) |
| `DescentWitness.Valid.ends_at` | Checked | `CollatzResearch.Certificate` | A valid local-descent witness has the declared accelerated-trajectory endpoint |
| `DescentWitness.Valid.strict_descent` | Checked | `CollatzResearch.Certificate` | A valid local-descent witness has target strictly below start |
| `DescentWitness.Valid.start_pos_odd` | Checked | `CollatzResearch.Certificate` | A valid local-descent witness has a positive, odd start (matching Python's `accelerated_step`) |
| `acceleratedStep_odd_of_odd` | Checked | `CollatzResearch.Basic` | `acceleratedStep` preserves oddness on the odd domain (relocated from Certificate.lean and proved in PR #31 at `08319d5`; supersedes the old Certificate.lean entry) |
| `DescentWitness.trajectory_odd` | Checked | `CollatzResearch.Certificate` | Oddness is preserved along the accelerated trajectory (induction on `steps`, uses `acceleratedStep_odd_of_odd`) |
| `descend_orbit_complete` | Checked | `CollatzResearch.CoverageTree` | Structural orbit-aware routing completeness: for valid + complete `t` and `0 < x`, `descendOrbit t x 0` returns a leaf in `t.leaves`, verified, with `OrbitRoute t x 0 t.root l` witness. Each internal edge is selected by `accelerated_orbit x i % m`. Explicitly NOT `SatOrbit`, local descent, or global convergence. |
| Global convergence | Not started | — | No claim |
| Nontrivial cycle exclusion | Not started | — | No claim |

Update this table in the same change as any theorem addition. "Checked" means `lake build` succeeds against pinned dependencies. "Pending" means the definition is in place but the proof is incomplete (tracked as `sorry` in the Lean file).
