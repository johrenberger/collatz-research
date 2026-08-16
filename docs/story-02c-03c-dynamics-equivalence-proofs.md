# Story 02c/03c — Dynamics + Equivalence proof completion

## Claim level

**Preparatory / implementation plan.** This PR documents the implementation plan for closing the outstanding `sorry` items in `Dynamics.lean` and `Equivalence.lean` from Story 02b/03b. The plan itself is preparatory: the actual formalization — closing the admissions, achieving a green Lean CI build, and proving all claim prerequisites — is the work of the proof-bearing PR that follows. **This PR must not be merged at `formally established`; that claim is reserved for the proof-bearing PR.**

Reclassified from `formally established` per Codex review (PR #30, 2026-08-16T16:34:55Z), P0: the spec adds no Lean proofs and leaves all four target theorems as `sorry`; reserving "formally established" for the proof-bearing PR.

## Objective

Complete the formal proofs for:

1. `standardStep_positive` (Dynamics.lean) — standard step preserves positivity on positive domain
2. `acceleratedStep_positive_of_odd` (Dynamics.lean) — accelerated step preserves positivity on odd domain
3. `acceleratedStep_equiv_standardStep` (Equivalence.lean) — one accelerated step on odd domain = `1 + ν₂(3n+1)` standard steps
4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean) — accelerated trajectory reaching 1 lifts to a finite standard trajectory reaching 1
5. (To be added by proof-bearing PR) — one-step oddness preservation (distinct core lemma in `Equivalence.lean`; prerequisite for #3 and #4)

These are the **five** preconditions for promoting Story 07c-2 (Collatz/Syracuse dynamics connection) from `preparatory` to `formally established`.

## Why no Mathlib PR is needed

The blockers originally attributed to "Mathlib `omega` extension" are resolvable **locally**. From the existing `Dynamics.lean` header notes:

- `Odd.pos : Odd n → 0 < n` **already exists in Mathlib**. The blocker was `omega` not auto-dispatching it, not lemma absence. We call `h_odd.pos` directly.
- `n % 2 = 0 ∧ n > 0 → n ≥ 2` is provable inline with explicit `n ≠ 1` proof + `omega` (omega handles `n ≥ 1 ∧ n ≠ 1 → n ≥ 2`).
- The `if p = 2` vs `if 2 = p` issue in the factorization chain is a known tactic pattern; fixed by `by_cases hp : 2 = p`.
- The Equivalence.lean proofs use existing Mathlib lemmas (`Nat.factorization_*`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`).

**No upstream Mathlib contribution is required.** The 04b workstream (`Int.mul_div_cancel_left_of_dvd` + divisibility-combination lemma) for the Affine.lean sorries is also tracked separately and is not in this scope.

## Prerequisite: oddness invariant (Codex re-review P1, 2026-08-16T17:32:09Z)

`acceleratedStep_equiv_standardStep` (sorry #3) requires `Odd (trajectory n k)` (one-step oddness preservation across the orbit). The existing `Certificate.lean::acceleratedStep_odd_of_odd` is a `sorry`; importing it from `Equivalence.lean` would create a cycle.

**Architecture** (per Codex re-review P1, 2026-08-16T17:32:09Z): to avoid a duplicate declaration with `Certificate.lean::acceleratedStep_odd_of_odd` (same fully-qualified name `CollatzResearch.acceleratedStep_odd_of_odd` in two modules = compile error), the proof-bearing PR will introduce a **distinctly named core oddness lemma** in `Equivalence.lean`. Two architectural options, both avoiding duplicate declarations:

- **Option A (recommended)**: define the core lemma in `Equivalence.lean` under a sub-namespace (e.g., `CollatzResearch.EquivalenceCore.acceleratedStep_odd_of_odd`) or with a uniquely named helper (e.g., `oddness_step_preserved`). Full qualification differs from `Certificate.lean::acceleratedStep_odd_of_odd`. Certificate migration to consume the Equivalence lemma is deferred to a **separate follow-on workstream** (out of scope for 02c/03c).
- **Option B**: move the canonical declaration from `Certificate.lean` to `Equivalence.lean`; Certificate imports the Equivalence module. More invasive but cleaner long-term.

Either option gives a fully-qualified distinct identifier; no duplicate declaration. The proof-bearing PR selects one and adds the new declaration atomically with its implementation. **This preparatory doc specifies the requirement; the proof-bearing PR will add the declaration.**

**Resolution** (to be implemented by proof-bearing PR):

```lean
-- In Equivalence.lean (under namespace EquivalenceCore, or with renamed helper)
theorem acceleratedStep_odd_of_odd (n : Nat) (h : Odd n) : Odd (acceleratedStep n) := by
  -- 3n+1 is even; (3n+1)/2^k is odd since k = ν₂(3n+1) is the full 2-adic valuation
  have hn_pos : 0 < n := h.pos
  have h_even : 1 ≤ (3 * n + 1).factorization 2 := by
    -- Lemma 1: odd n → ν₂(3n+1) ≥ 1 (corrected from 2 ≤ per Codex re-review P1)
    exact ...  -- case analysis on n mod 2 + factorization_pos_iff_dvd
  -- ... (factorization decomposition proves oddness of the result)
```

Plus a trajectory-oddness induction lemma (corollary, no separate admission):

```lean
theorem trajectory_odd (n : Nat) (h_odd : Odd n) : ∀ k : Nat, Odd (trajectory n k) := by
  intro k
  induction k with
  | zero => exact h_odd
  | succ k' ih => exact EquivalenceCore.acceleratedStep_odd_of_odd (trajectory n k') ih
```

This adds a **5th sorry to close** (added by the proof-bearing PR) at the new distinct name in `Equivalence.lean`. The trajectory-level oddness is a corollary (no separate admission).

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

**Validation**: GitHub Lean CI is the sole Lean validation gate. No local `lake` commands per project BDD discipline (Codex review P1, 2026-08-16).

### 2. `acceleratedStep_positive_of_odd` (Dynamics.lean)

**Statement**: `acceleratedStep_positive_of_odd (n : Nat) (h_odd : Odd n) : Positive (acceleratedStep n)`

**Proof approach**:
- Use `Odd.pos h_odd` directly to get `0 < n` (instead of relying on `omega` to auto-dispatch)
- Factorization chain via `Nat.div_pos_iff` + `Nat.factorization_le_iff_dvd` + `Prime.factorization` + `Finsupp.smul_single'`
- `by_cases hp : 2 = p` for the `if p = 2` vs `if 2 = p` issue documented in the file header
- `rw [if_pos hp]; rw [if_neg hp]` + `exact Nat.zero_le _` for the `¬p = 2` case

**Risk**: medium. Factorization rewriting is notation-sensitive; the `if p = 2` direction matters.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

### 3. `acceleratedStep_equiv_standardStep` (Equivalence.lean)

**Statement**: `acceleratedStep_equiv_standardStep (n : Nat) (h : Odd n) : standardTrajectory n (1 + (3 * n + 1).factorization 2) = acceleratedStep n`

**Proof approach**: Direct case analysis on `k = (3*n+1).factorization 2` (with `k ≥ 1` since odd `n` forces `3n+1` even — Lemma 1).

**Lemma 1 (odd n → ν₂(3n+1) ≥ 1)**: For odd `n`, `3n+1` is even. Write `3n+1 = 2^k * m` with `m` odd; `k ≥ 1` (i.e., `1 ≤ k`). Proof: `n` odd → `3n+1` is even → 2-adic valuation ≥ 1. In Mathlib: `Odd n → (3*n+1) % 2 = 0` (case analysis on `n` mod 2), then `Nat.factorization_pos_iff_dvd` chains to show `1 ≤ (3*n+1).factorization 2`.

**Boundary case**: `n = 3` is the smallest odd `n` where `3n+1 = 10` and `ν₂(10) = 1` exactly. The bound `k ≥ 1` is **tight** here (cannot strengthen to `k ≥ 2`).

**Lemma 2 (factorization decomposition)**: `(3*n+1).factorization 2 = k` implies `3*n+1 = 2^k * m` with `m` odd. This is `Nat.factorization_mul` + `Prime.factorization` rewriting.

**Induction predicate**: `P(k) ≡ ∀ n : Nat, Odd n → (3*n+1).factorization 2 = k → standardTrajectory n (1 + k) = acceleratedStep n`.

**Base case** `k = 1`: `3n+1 = 2m` with `m` odd. `C(n) = 3n+1 = 2m` (odd case). `C²(n) = C(2m) = m` (even case). `T(n) = (3n+1)/2^1 = m`. So `C²(n) = T(n)` ✓.

**Inductive case** `k > 1`: `3n+1 = 2^k * m` with `m` odd. Trajectory: `n →^{1} 3n+1 →^{1} (3n+1)/2 →^{1} (3n+1)/2² → ... →^{1} m`. This is `k+1` standard steps. So `C^{k+1}(n) = m`. `T(n) = (3n+1)/2^k = m`. So `C^{k+1}(n) = T(n)` ✓.

**Mathlib lemmas used**: `Nat.factorization_mul`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`, `Nat.factorization_div`, `Nat.factorization_pos_iff_dvd`.

**Risk**: medium. The factorization decomposition is the substantive mathematical step.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

### 4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean)

**Statement**: `acceleratedTrajectory_reaches_one_implies_standard (n m : Nat) (h_odd : Odd n) (h : trajectory n m = 1) : ∃ m', standardTrajectory n m' = 1`

**Proof approach**: Induction on `m`. **Depends on sorry #3** (`acceleratedStep_equiv_standardStep`) **and sorry #5** (core oddness lemma + `trajectory_odd`).

- **Base case** `m = 0`: `trajectory n 0 = n = 1` forces `n = 1`; `standardTrajectory 1 0 = 1`.
- **Inductive case** `m = k + 1`: by `trajectory_odd` (sorry #5), `trajectory n k` is odd. Apply `acceleratedStep_equiv_standardStep` (sorry #3) to `trajectory n k` to get `standardTrajectory (trajectory n k) (1 + ν₂(3*(trajectory n k) + 1)) = acceleratedStep (trajectory n k) = 1`. Take `m' = (1 + ν₂(3*(trajectory n k) + 1)) + (1 + ν₂(3n + 1) + ... + 1 + ν₂(...))` — the sum of `1 + ν₂(3 n_i + 1)` over `i = 0 .. k-1` plus the final segment.

**Risk**: medium. Depends on #3 and #5 being closed; the sum construction for `m'` requires `standardTrajectory` induction.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

### 5. Core oddness preservation lemma (Equivalence.lean) — added by proof-bearing PR

**Statement**: `∀ n : Nat, Odd n → Odd (acceleratedStep n)`

**Location** (per Codex re-review P1, 2026-08-16T17:32:09Z): the lemma will be defined in `Equivalence.lean` under a **fully-qualified distinct** name to avoid duplicate-declaration with `Certificate.lean::acceleratedStep_odd_of_odd` (e.g., `CollatzResearch.EquivalenceCore.acceleratedStep_odd_of_odd` via sub-namespace, or a uniquely-named helper such as `oddness_step_preserved`). The proof-bearing PR chooses the name and atomically adds: declaration in `Equivalence.lean`, theorem-status row in `docs/theorem-status.md`, and (if Option B) `Certificate.lean` migration.

**Proof approach** (same regardless of name):
- `acceleratedStep n = (3n+1) / 2^k` where `k = (3*n+1).factorization 2`
- For odd `n`: `3n+1` is even, so `k ≥ 1` (Lemma 1)
- `(3n+1) / 2^k` is odd because `k` is the **full** 2-adic valuation (no factor of 2 remains)
- Uses Mathlib `Nat.factorization_div` + `Nat.factorization_pow` to show oddness of the quotient

**Mathlib lemmas used**: `Nat.factorization_div`, `Nat.factorization_pow`, `Prime.factorization`, `Nat.factorization_pos_iff_dvd`.

**Risk**: **medium** (per Codex re-review P2, 2026-08-16T17:32:09Z). The factorization chain is well-established in Mathlib in principle but is the **same** factorization chain currently admitted in `Certificate.lean`. Risk remains medium until the exact Mathlib chain passes GitHub Lean CI; revisits to medium/high as needed.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

## 07c-2 promotion criteria (separate PR, follows 02c/03c)

Per the PR #17 framing that established the `preparatory` claim, promotion to `formally established` requires:

- **Restore `ReachesOne x` conclusion** in `coverage_tree_soundness` (currently absent per the current `CoverageTree.lean` header comment, which explicitly says: *"this theorem intentionally does not conclude `ReachesOne x`; that would require a proof connecting tree descent to the Collatz trajectory."*)
- **Prove** via the 5 closed lemmas from 02c/03c:
  - `acceleratedStep_equiv_standardStep` for the per-step standard equivalence
  - `acceleratedTrajectory_reaches_one_implies_standard` for the trajectory-level lift
  - Core oddness lemma (distinct name TBD, sorry #5) for the oddness invariant
- **No new `sorry`/`admit`/`axiom`** in the extension
- **Claim level**: `formally established`
- **Python BDD**: extend `tests/test_coverage_tree.py` with a `test_coverage_tree_soundness_implies_ReachesOne` runtime check (UNTRUSTED RUNTIME EVIDENCE per existing discipline — not a Lean-side substitution)

This work is deferred to a separate PR after 02c/03c lands. It is NOT in this story's scope.

## Execution sequence

1. ✅ Create branch `story-02c-03c-dynamics-equivalence-proofs` from `dcd35f5` (executed 2026-08-16)
2. ✅ Draft this spec doc (executed 2026-08-16)
3. ✅ Spec PR opened (PR #30) + initial Codex review received (request changes, 2026-08-16T16:34:55Z)
4. ✅ Spec updated to address initial P0/P1/P2 (commit `6911c8c`, 2026-08-16)
5. ✅ Codex re-review received (request changes, 2026-08-16T17:32:09Z) — 4 new P1/P2 issues
6. ✅ Spec updated to address re-review P1/P2 (in progress, 2026-08-16)
7. ⏳ Push spec update to PR #30 + re-request Codex review
8. ⏳ Close `standardStep_positive` (smallest, lowest risk)
9. ⏳ Close `acceleratedStep_positive_of_odd`
10. ⏳ Add core oddness lemma (sorry #5, distinct name TBD) to `Equivalence.lean`
11. ⏳ Close `acceleratedStep_equiv_standardStep`
12. ⏳ Close `acceleratedTrajectory_reaches_one_implies_standard`
13. ⏳ Push branch + GitHub Lean CI validates the proof work (sole Lean validation gate)
14. ⏳ Commit sequence (one commit per sorry, signed-off)
15. ⏳ Open proof-bearing PR (one PR for all 5 sorries; supersedes PR #30)
16. ⏳ Codex review + CI green
17. ⏳ Merge to `agent/bootstrap-research-monorepo`
18. ⏳ Certificate migration follow-on workstream (per Codex re-review P1 architecture decision)
19. ⏳ 07c-2 promotion PR (separate; depends on merged 02c/03c + Certificate follow-on)
20. ⏳ M4 closes

## Non-goals

- **No Mathlib contribution** (PR or local fork change)
- **No new `sorry`/`admit`/`axiom`** in any closed lemma
- **No convergence proof** (the dynamics connection is structural, not a Collatz convergence theorem)
- **No global-descent claim** (the tree descent proof does not claim Collatz terminates for all positive integers)
- **No change to `CoverageTree.lean`** (07c-2 promotion is a separate PR)
- **No `coverage_tree_soundness_orbit` work** (separate workstream; `sorry` remains)
- **No `Affine.lean` work** (Story 04b)
- **No `Certificate.lean::acceleratedStep_odd_of_odd` migration in this PR** (deferred to follow-on workstream per Codex re-review P1 architectural decision; the existing `Certificate.lean` `sorry` remains open)

## Lean / Python split (per `MEMORY.md` "BDD Discipline — Justin, 2026-08-15")

- **Python BDD**: existing `tests/test_coverage_tree.py` already covers `accelerated_orbit` + `ReachesOne` (per PR #17). Re-run as regression: `uv run pytest tests/test_coverage_tree.py -q`. No new Python tests required unless the proof work changes behavior.
- **Lean validation**: **GitHub Lean CI is the sole Lean validation gate.** No local `lake` commands of any kind (no `lake build`, no `lake env lean`, no `.olean` inspection). All Lean verification happens in CI. Per-stop rule: stop after 2 patch failures on the same logical edit; read Mathlib source before the next patch.
- **Out of scope**: local fast feedback via `lake env lean`. Removed per Codex review P1 (2026-08-16): the project decision is now explicit — GitHub Lean CI only.

## Open gates (from Codex review + re-review)

### Initial review (2026-08-16T16:34:55Z)
- ✅ Accurate preparatory claim level (P0 resolved)
- ✅ Explicit oddness-closure dependency for the trajectory theorem (P1 — sorry #5 specified)
- ✅ GitHub-CI-only Lean validation (P1 — local Lake commands removed)
- ✅ Concrete factorization proof decomposition (P2 — Lemma 1 + Lemma 2 + induction predicate)

### Re-review (2026-08-16T17:32:09Z)
- ✅ Module-ownership conflict (P1 — distinct core lemma name; Certificate migration deferred)
- ✅ Lemma 1 valuation bound (P1 — `1 ≤ k` not `2 ≤ k`; `n = 3` boundary case noted)
- ✅ Sorry #5 future tense (P1 — preparatory doc uses future tense; proof-bearing PR adds declaration + status row atomically)
- ✅ Stray markup (P2 — `</content></invoke>` removed)
- ✅ Risk classification (P2 — oddness preservation reclassified medium, was low)

## Codex review corrections (both reviews)

### Initial review (2026-08-16T16:34:55Z)
- **P0**: reclassified `formally established` → `preparatory / implementation plan`
- **P1**: added oddness invariant prerequisite (sorry #5 in Equivalence.lean)
- **P1**: removed local Lean validation references; "GitHub Lean CI only" is the sole gate
- **P2**: specified factorization proof decomposition (Lemma 1, Lemma 2, induction predicate)

### Re-review (2026-08-16T17:32:09Z)
- **P1 (module ownership)**: distinct core lemma name in Equivalence.lean (sub-namespace `EquivalenceCore` or uniquely-named helper); `Certificate.lean::acceleratedStep_odd_of_odd` migration deferred to follow-on workstream
- **P1 (Lemma 1 bound)**: corrected `2 ≤ k` to `1 ≤ k`; boundary case `n = 3` (`ν₂(10) = 1`) noted
- **P1 (future tense)**: sorry #5 described in future tense; proof-bearing PR adds declaration + theorem-status row atomically
- **P2 (stray markup)**: stray `</content></invoke>` removed
- **P2 (risk)**: oddness preservation risk reclassified medium (was low); revisits to medium/high until Mathlib CI passes

## Status

**Started 2026-08-16.** Per-sorry resolution proven feasible without Mathlib PR (see "Why no Mathlib PR is needed"). Spec doc updated to address Codex reviews (initial P0/P1/P2 + re-review P1/P2 on 2026-08-16T17:32:09Z). Awaiting re-review.
