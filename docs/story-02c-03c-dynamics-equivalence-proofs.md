# Story 02c/03c — Dynamics + Equivalence proof completion

## Claim level

**Formally established.** This story closes all 4 outstanding `sorry` items in `Lean/CollatzResearch/Dynamics.lean` and `Lean/CollatzResearch/Equivalence.lean` from Story 02b/03b. No new `sorry`, `admit`, axiom, or opaque trust extension is introduced. No Mathlib contribution is required.

## Objective

Complete the formal proofs for:

1. `standardStep_positive` (Dynamics.lean) — standard step preserves positivity on positive domain
2. `acceleratedStep_positive_of_odd` (Dynamics.lean) — accelerated step preserves positivity on odd domain
3. `acceleratedStep_equiv_standardStep` (Equivalence.lean) — one accelerated step on odd domain = `1 + ν₂(3n+1)` standard steps
4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean) — accelerated trajectory reaching 1 lifts to a finite standard trajectory reaching 1

These are the four preconditions for promoting Story 07c-2 (Collatz/Syracuse dynamics connection) from `preparatory` to `formally established`.

## Why no Mathlib PR is needed

The blockers originally attributed to "Mathlib `omega` extension" are resolvable **locally**. From the existing `Dynamics.lean` header notes:

- `Odd.pos : Odd n → 0 < n` **already exists in Mathlib**. The blocker was `omega` not auto-dispatching it, not lemma absence. We call `h_odd.pos` directly.
- `n % 2 = 0 ∧ n > 0 → n ≥ 2` is provable inline with explicit `n ≠ 1` proof + `omega` (omega handles `n ≥ 1 ∧ n ≠ 1 → n ≥ 2`).
- The `if p = 2` vs `if 2 = p` issue in the factorization chain is a known tactic pattern; fixed by `by_cases hp : 2 = p`.
- The Equivalence.lean proofs use existing Mathlib lemmas (`Nat.factorization_*`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`).

**No upstream Mathlib contribution is required.** The 04b workstream (`Int.mul_div_cancel_left_of_dvd` + divisibility-combination lemma) for the Affine.lean sorries is also tracked separately and is not in this scope.

## Per-sorry resolution

### 1. `standardStep_positive` (Dynamics.lean)

**Statement**: `standardStep_positive (n : Nat) (h : Positive n) : Positive (standardStep n)`

**Proof approach**:
```lean
theorem standardStep_positive (n : Nat) (h : Positive n) : Positive (standardStep n) := by
  unfold Positive standardStep
  split_ifs with h_even
  · -- even branch: n / 2 > 0 needs n ≥ 2
    apply Nat.div_pos
    · -- prove n ≥ 2 from n > 0 ∧ n % 2 = 0
      have hn1 : n ≠ 1 := fun hn1 => h_even (by rw [hn1]; simp)
      omega  -- n ≥ 1 ∧ n ≠ 1 → n ≥ 2
    · norm_num
  · -- odd branch: 3n + 1 > 0 trivially
    exact Nat.succ_pos _
```

**Risk**: low. Both branches are elementary; the `n ≠ 1` workaround is the only subtlety.

**Validation**: `lake env lean Lean/CollatzResearch/Dynamics.lean` (capture `LAKE_EXIT=$?` + `.olean` per safe-code-editing skill §10.2); CI-side `lake build` for full verification.

### 2. `acceleratedStep_positive_of_odd` (Dynamics.lean)

**Statement**: `acceleratedStep_positive_of_odd (n : Nat) (h_odd : Odd n) : Positive (acceleratedStep n)`

**Proof approach**:
- Use `Odd.pos h_odd` directly to get `0 < n` (instead of relying on `omega` to auto-dispatch)
- Factorization chain via `Nat.div_pos_iff` + `Nat.factorization_le_iff_dvd` + `Prime.factorization` + `Finsupp.smul_single'`
- `by_cases hp : 2 = p` for the `if p = 2` vs `if 2 = p` issue documented in the file header
- `rw [if_pos hp]; rw [if_neg hp]` + `exact Nat.zero_le _` for the `¬p = 2` case

**Risk**: medium. Factorization rewriting is notation-sensitive; the `if p = 2` direction matters.

**Validation**: same as #1.

### 3. `acceleratedStep_equiv_standardStep` (Equivalence.lean)

**Statement**: `acceleratedStep_equiv_standardStep (n : Nat) (h : Odd n) : standardTrajectory n (1 + (3 * n + 1).factorization 2) = acceleratedStep n`

**Proof approach**: Induction on `k = (3*n+1).factorization 2`.
- **Base case** `k = 1`: `3n + 1 = 2 * m` with `m` odd; `C(n) = 3n + 1 = 2m`, `C²(n) = m = T(n) = (3n + 1) / 2¹`.
- **Inductive case** `k = m + 1`: `3n + 1 = 2^{m+1} * p` for odd `p`. By IH on `k' = m`, `C^{1+m}(n) = 2 * p`. Then `C^{2+m}(n) = C(2 * p) = p = T(n)`.

Uses Mathlib `Nat.factorization_*`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`.

**Risk**: medium. The factorization decomposition is the substantive mathematical step.

**Validation**: CI-side `lake build` after Dynamics.lean is closed.

### 4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean)

**Statement**: `acceleratedTrajectory_reaches_one_implies_standard (n m : Nat) (h_odd : Odd n) (h : trajectory n m = 1) : ∃ m', standardTrajectory n m' = 1`

**Proof approach**: Induction on `m`.
- **Base case** `m = 0`: `trajectory n 0 = n = 1` forces `n = 1`; `standardTrajectory 1 0 = 1`.
- **Inductive case** `m = k + 1`: by `acceleratedStep_equiv_standardStep`, `standardTrajectory (trajectory n k) (1 + ν₂(3*(trajectory n k) + 1)) = 1`. Take `m' = (1 + ν₂(3*(trajectory n k) + 1)) + (1 + ν₂(3n + 1) + ... + 1 + ν₂(...))` — the sum of `1 + ν₂(3 n_i + 1)` over `i = 0 .. k-1` plus the final segment.

**Risk**: medium. Depends on #3 being closed; the sum construction for `m'` requires `standardTrajectory` induction.

**Validation**: CI-side.

## 07c-2 promotion criteria (separate PR, follows 02c/03c)

Per the PR #17 framing that established the `preparatory` claim, promotion to `formally established` requires:

- **Restore `ReachesOne x` conclusion** in `coverage_tree_soundness` (currently absent per the current `CoverageTree.lean` header comment, which explicitly says: *"this theorem intentionally does not conclude `ReachesOne x`; that would require a proof connecting tree descent to the Collatz trajectory."*)
- **Prove** via the 4 closed lemmas from 02c/03c:
  - `acceleratedStep_equiv_standardStep` for the per-step standard equivalence
  - `acceleratedTrajectory_reaches_one_implies_standard` for the trajectory-level lift
- **No new `sorry`/`admit`/`axiom`** in the extension
- **Claim level**: `formally established`
- **Python BDD**: extend `tests/test_coverage_tree.py` with a `test_coverage_tree_soundness_implies_ReachesOne` runtime check (UNTRUSTED RUNTIME EVIDENCE per existing discipline — not a Lean-side substitution)

This work is deferred to a separate PR after 02c/03c lands. It is NOT in this story's scope.

## Execution sequence

1. ✅ Create branch `story-02c-03c-dynamics-equivalence-proofs` from `dcd35f5` (executed 2026-08-16)
2. ✅ Draft this spec doc (executed 2026-08-16)
3. ⏳ Close `standardStep_positive` (smallest, lowest risk)
4. ⏳ Close `acceleratedStep_positive_of_odd`
5. ⏳ Close `acceleratedStep_equiv_standardStep`
6. ⏳ Close `acceleratedTrajectory_reaches_one_implies_standard`
7. ⏳ Local validation: `lake env lean Lean/CollatzResearch/Dynamics.lean` + `Equivalence.lean` (capture `LAKE_EXIT=$?` + `.olean` per safe-code-editing skill §10.2)
8. ⏳ Commit sequence (one commit per sorry, signed-off)
9. ⏳ Push branch + open PR (one PR for all 4 sorries)
10. ⏳ Codex review + CI green
11. ⏳ Merge to `agent/bootstrap-research-monorepo`
12. ⏳ 07c-2 promotion PR (separate; depends on merged 02c/03c)
13. ⏳ M4 closes

## Non-goals

- **No Mathlib contribution** (PR or local fork change)
- **No new `sorry`/`admit`/`axiom`** in any closed lemma
- **No convergence proof** (the dynamics connection is structural, not a Collatz convergence theorem)
- **No global-descent claim** (the tree descent proof does not claim Collatz terminates for all positive integers)
- **No change to `CoverageTree.lean`** (07c-2 promotion is a separate PR)
- **No `coverage_tree_soundness_orbit` work** (separate workstream; `sorry` remains)
- **No `Affine.lean` work** (Story 04b)
- **No `Certificate.lean::acceleratedStep_odd_of_odd` work** (separate Mathlib-blocker workstream)

## Lean / Python split (per `MEMORY.md` "BDD Discipline — Justin, 2026-08-15")

- **Python BDD**: existing `tests/test_coverage_tree.py` already covers `accelerated_orbit` + `ReachesOne` (per PR #17). Re-run as regression: `uv run pytest tests/test_coverage_tree.py -q`. No new Python tests required unless the proof work changes behavior.
- **Lean validation**: CI-only. **No local `lake build`** for the test-first or implementation commit. Per-stop rule: stop after 2 patch failures on the same logical edit; read Mathlib source before the next patch.
- **Local fast feedback**: `lake env lean Lean/CollatzResearch/<Module>.lean` per safe-code-editing skill §10.2. Capture `LAKE_EXIT=$?` and confirm `.olean` exists. This runs syntax + types only; not a substitute for CI tactic verification.

## Status

**Started 2026-08-16.** Per-sorry resolution proven feasible without Mathlib PR (see "Why no Mathlib PR is needed"). Spec doc drafted; ready for implementation phases (steps 3–6).
