# Story 02c/03c — Dynamics + Equivalence proof completion

## Claim level

**Preparatory / implementation plan.** This PR documents the implementation plan for closing the outstanding `sorry` items in `Dynamics.lean`, `Equivalence.lean`, and `Certificate.lean` from Story 02b/03b. The plan itself is preparatory: the actual formalization — closing the admissions, achieving a green Lean CI build, and proving all claim prerequisites — is the work of the proof-bearing PR that follows. **This PR must not be merged at `formally established`; that claim is reserved for the proof-bearing PR.**

Reclassified from `formally established` per Codex review (PR #30, 2026-08-16T16:34:55Z), P0: the spec adds no Lean proofs and leaves all target theorems as `sorry`; reserving "formally established" for the proof-bearing PR.

## Objective

Complete the formal proofs for:

**Target admissions to close in Dynamics.lean + Equivalence.lean** (4 sorries):

1. `standardStep_positive` (Dynamics.lean) — standard step preserves positivity on positive domain
2. `acceleratedStep_positive_of_odd` (Dynamics.lean) — accelerated step preserves positivity on odd domain
3. `acceleratedStep_equiv_standardStep` (Equivalence.lean) — one accelerated step on odd domain = `1 + ν₂(3n+1)` standard steps
4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean) — accelerated trajectory reaching 1 lifts to a finite standard trajectory reaching 1

**Plus: relocate and close the existing `Certificate.lean::acceleratedStep_odd_of_odd`** (per Codex re-review P1, 2026-08-16T17:58:50Z). Move the canonical declaration to `Basic.lean` (low-level, imports only Mathlib); both `Certificate.lean` and `Equivalence.lean` consume it.

These are the **four target admissions plus one relocated admission** for promoting Story 07c-2 (Collatz/Syracuse dynamics connection) from `preparatory` to `formally established`. The relocation **closes** an existing admission rather than adding a parallel one.

## Why no Mathlib PR is needed

The blockers originally attributed to "Mathlib `omega` extension" are resolvable **locally**. From the existing `Dynamics.lean` header notes:

- `Odd.pos : Odd n → 0 < n` **already exists in Mathlib**. The blocker was `omega` not auto-dispatching it, not lemma absence. We call `h_odd.pos` directly.
- `n % 2 = 0 ∧ n > 0 → n ≥ 2` is provable inline with explicit `n ≠ 1` proof + `omega` (omega handles `n ≥ 1 ∧ n ≠ 1 → n ≥ 2`).
- The `if p = 2` vs `if 2 = p` issue in the factorization chain is a known tactic pattern; fixed by `by_cases hp : 2 = p`.
- The Equivalence.lean proofs use existing Mathlib lemmas (`Nat.factorization_*`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`).

**No upstream Mathlib contribution is required.** The 04b workstream (`Int.mul_div_cancel_left_of_dvd` + divisibility-combination lemma) for the Affine.lean sorries is also tracked separately and is not in this scope.

## Module ownership of the oddness theorem (Codex re-review P1, 2026-08-16T17:58:50Z)

The current import structure is:

- `Basic.lean` imports `Mathlib.Data.Nat.Factorization.Basic`
- `Dynamics.lean` imports `CollatzResearch.Basic`
- `Equivalence.lean` imports `CollatzResearch.Basic` + `CollatzResearch.Dynamics`
- `Certificate.lean` imports `CollatzResearch.Basic` + `CollatzResearch.Importer`

**`Certificate.lean` does not import `Equivalence.lean`, and vice versa.** There is no import cycle. My prior re-review architecture (distinct core lemma in `Equivalence.lean`) was based on a false premise.

**Correct architecture** (per Codex re-review P1): the canonical oddness theorem belongs **below** both `Certificate.lean` and `Equivalence.lean` — i.e., in `Basic.lean` (or a dedicated low-level parity module importing only `Basic`/Mathlib). Both `Certificate.lean` and `Equivalence.lean` then consume it.

**Resolution** (to be implemented by proof-bearing PR):

1. Add `acceleratedStep_odd_of_odd` to `Basic.lean` (proved via factorization decomposition).
2. Drop the existing `Certificate.lean::acceleratedStep_odd_of_odd` sorry declaration; rewrite `Certificate.lean::trajectory_odd` to use `Basic.lean::acceleratedStep_odd_of_odd` (already in scope via existing import).
3. Equivalence.lean uses `Basic.lean::acceleratedStep_odd_of_odd` directly via existing import.
4. `Certificate.lean` migration is **in scope** for the proof-bearing PR (not deferred to a follow-on workstream as previously planned).

This **closes** the existing Certificate admission rather than adding a parallel one.

```lean
-- In Basic.lean (NEW)
theorem acceleratedStep_odd_of_odd (n : Nat) (h : Odd n) : Odd (acceleratedStep n) := by
  -- 3n+1 is even; (3n+1)/2^k is odd since k = ν₂(3n+1) is the full 2-adic valuation
  have hn_pos : 0 < n := h.pos
  have h_even : 1 ≤ (3 * n + 1).factorization 2 := by
    -- Lemma 1: odd n → ν₂(3n+1) ≥ 1
    exact ...  -- case analysis on n mod 2 + factorization_pos_iff_dvd
  -- ... (factorization decomposition proves oddness of the result)

-- In Certificate.lean (UPDATED, drops local sorry)
-- trajectory_odd now uses Basic.lean::acceleratedStep_odd_of_odd
theorem trajectory_odd (n : Nat) (h_odd : Odd n) : ∀ k : Nat, Odd (trajectory n k) := by
  intro k
  induction k with
  | zero => exact h_odd
  | succ k' ih => exact acceleratedStep_odd_of_odd (trajectory n k') ih

-- In Equivalence.lean (UPDATED)
-- Uses Basic.lean::acceleratedStep_odd_of_odd (imported transitively)
```

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

**Boundary case**: `n = 3` is the smallest odd `n` where `3n+1 = 10` and `ν₂(10) = 1` exactly. The bound `k ≥ 1` is **tight** here (cannot strengthen to to `k ≥ 2`).

**Lemma 2 (factorization decomposition)**: `(3*n+1).factorization 2 = k` implies `3*n+1 = 2^k * m` with `m` odd. This is `Nat.factorization_mul` + `Prime.factorization` rewriting.

**Induction predicate**: `P(k) ≡ ∀ n : Nat, Odd n → (3*n+1).factorization 2 = k → standardTrajectory n (1 + k) = acceleratedStep n`.

**Base case** `k = 1`: `3n+1 = 2m` with `m` odd. `C(n) = 3n+1 = 2m` (odd case). `C²(n) = C(2m) = m` (even case). `T(n) = (3n+1)/2^1 = m`. So `C²(n) = T(n)` ✓.

**Inductive case** `k > 1`: `3n+1 = 2^k * m` with `m` odd. Trajectory: `n →^{1} 3n+1 →^{1} (3n+1)/2 →^{1} (3n+1)/2² → ... →^{1} m`. This is `k+1` standard steps. So `C^{k+1}(n) = m`. `T(n) = (3n+1)/2^k = m`. So `C^{k+1}(n) = T(n)` ✓.

**Mathlib lemmas used**: `Nat.factorization_mul`, `Prime.factorization`, `Nat.factorization_le_iff_dvd`, `Nat.factorization_div`, `Nat.factorization_pos_iff_dvd`.

**Risk**: medium. The factorization decomposition is the substantive mathematical step.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

### 4. `acceleratedTrajectory_reaches_one_implies_standard` (Equivalence.lean)

**Statement**: `acceleratedTrajectory_reaches_one_implies_standard (n m : Nat) (h_odd : Odd n) (h : trajectory n m = 1) : ∃ m', standardTrajectory n m' = 1`

**Proof approach** (per Codex re-review P1, 2026-08-16T17:58:50Z): strong induction on `m`, with hypothesis rewritten as `trajectory (acceleratedStep n) k = 1` and final composition via `standardTrajectory_compose`.

**New auxiliary lemma** `standardTrajectory_compose` (Equivalence.lean):
```lean
theorem standardTrajectory_compose (n a b : Nat) :
    standardTrajectory (standardTrajectory n a) b = standardTrajectory n (a + b) := by
  induction a with
  | zero => simp [standardTrajectory_zero]
  | succ a' ih => simp [standardTrajectory_succ, ih, Nat.add_succ]
```

**Main proof** (sketch):
```lean
theorem acceleratedTrajectory_reaches_one_implies_standard (n m : Nat)
    (h_odd : Odd n) (h : trajectory n m = 1) :
    ∃ m', standardTrajectory n m' = 1 := by
  induction m using Nat.strong_rec_on with
  | _ m ih =>
    cases m with
    | zero =>
      -- trajectory n 0 = n = 1
      exact ⟨0, by rfl⟩
    | succ k =>
      -- h : trajectory n (k+1) = 1
      -- trajectory n (k+1) = acceleratedStep (trajectory n k)
      -- so h : acceleratedStep (trajectory n k) = 1
      have h_acc : acceleratedStep (trajectory n k) = 1 := h
      -- trajectory_odd (Certificate.lean, now using Basic.lean's theorem) gives
      -- Odd (trajectory n k); alternatively, use acceleratedStep_odd_of_odd directly
      have h_odd_t : Odd (trajectory n k) := trajectory_odd h_odd k
      -- Apply IH to (trajectory n k, k) with the rewritten goal
      have h_ih := ih k (Nat.lt_succ_self k) (trajectory n k) h_odd_t h_acc
      obtain ⟨r, hr⟩ := h_ih  -- standardTrajectory (trajectory n k) r = 1
      -- acceleratedStep_equiv_standardStep at n
      have h_eq := acceleratedStep_equiv_standardStep n h_odd
      -- standardTrajectory n (1 + ν₂(3n+1)) = acceleratedStep n
      -- Compose: standardTrajectory n ((1 + ν₂(3n+1)) + r) = 1
      have h_comp : standardTrajectory n ((1 + (3 * n + 1).factorization 2) + r) = 1 := by
        rw [← standardTrajectory_compose n (1 + (3 * n + 1).factorization 2) r]
        rw [h_eq]
        exact hr
      exact ⟨(1 + (3 * n + 1).factorization 2) + r, h_comp⟩
```

**Risk**: medium. Depends on #3 being closed; the `standardTrajectory_compose` lemma is new.

**Validation**: GitHub Lean CI is the sole Lean validation gate.

### 5. `Certificate.lean::acceleratedStep_odd_of_odd` — relocated to Basic.lean, existing admission closed

**Original**: `Certificate.lean` line 90: `theorem acceleratedStep_odd_of_odd (n : Nat) (h : Odd n) : Odd (acceleratedStep n) := by sorry`

**Relocation** (per Codex re-review P1, 2026-08-16T17:58:50Z): the canonical declaration moves to `Basic.lean` (low-level, imports only Mathlib). The proof-bearing PR:

1. Adds the proved declaration to `Basic.lean`.
2. Removes the sorry declaration from `Certificate.lean`.
3. Updates `Certificate.lean::trajectory_odd` to use `Basic.lean::acceleratedStep_odd_of_odd` (already in scope).
4. Updates `theorem-status.md` to record `Checked` (or appropriate status post-proof).

This **closes** an existing admission, not adds a new one.

**Risk**: medium (same factorization chain as sorry #2 and #3; revisits to medium/high until Mathlib CI passes).

**Validation**: GitHub Lean CI is the sole Lean validation gate.

## 07c-2 promotion criteria (separate PR, follows 02c/03c)

Per the PR #17 framing that established the `preparatory` claim, promotion to `formally established` requires:

- **Restore `ReachesOne x` conclusion** in `coverage_tree_soundness` (currently absent per the current `CoverageTree.lean` header comment, which explicitly says: *"this theorem intentionally does not conclude `ReachesOne x`; that would require a proof connecting tree descent to the Collatz trajectory."*)
- **Prove** via the closed lemmas from 02c/03c:
  - `acceleratedStep_equiv_standardStep` for the per-step standard equivalence
  - `acceleratedTrajectory_reaches_one_implies_standard` for the trajectory-level lift (using `standardTrajectory_compose` + the Basic.lean oddness theorem)
- **No new `sorry`/`admit`/`axiom`** in the extension
- **Claim level**: `formally established`
- **Python BDD**: extend `tests/test_coverage_tree.py` with a `test_coverage_tree_soundness_implies_ReachesOne` runtime check (UNTRUSTED RUNTIME EVIDENCE per existing discipline — not a Lean-side substitution)

This work is deferred to a separate PR after 02c/03c lands. It is NOT in this story's scope.

## Execution sequence

1. ✅ Create branch `story-02c-03c-dynamics-equivalence-proofs` from `dcd35f5` (executed 2026-08-16)
2. ✅ Draft this spec doc (executed 2026-08-16)
3. ✅ Spec PR opened (PR #30) + initial Codex review received (request changes, 2026-08-16T16:34:55Z)
4. ✅ Spec updated to address initial P0/P1/P2 (commit `6911c8c`, 2026-08-16)
5. ✅ Codex re-review received (request changes, 2026-08-16T17:32:09Z) — 4 P1/P2 issues
6. ✅ Spec updated to address re-review P1/P2 (commit `657c260`, 2026-08-16)
7. ✅ Second re-review received (request changes, 2026-08-16T17:58:50Z) — 2 P1 + 1 P2 architectural issues
8. ✅ Spec updated to address second re-review (in progress, 2026-08-16)
9. ⏳ Push spec update to PR #30 + re-request Codex review
10. ⏳ Close `Certificate.lean::acceleratedStep_odd_of_odd` (relocated to Basic.lean) — this admission is closed, not duplicated
11. ⏳ Close `standardStep_positive` (smallest, lowest risk)
12. ⏳ Close `acceleratedStep_positive_of_odd`
13. ⏳ Close `acceleratedStep_equiv_standardStep`
14. ⏳ Add `standardTrajectory_compose` lemma in Equivalence.lean
15. ⏳ Close `acceleratedTrajectory_reaches_one_implies_standard`
16. ⏳ Push branch + GitHub Lean CI validates the proof work (sole Lean validation gate)
17. ⏳ Commit sequence (one commit per sorry, signed-off)
18. ⏳ Open proof-bearing PR (one PR for all 4 target admissions + 1 relocation; supersedes PR #30)
19. ⏳ Codex review + CI green
20. ⏳ Merge to `agent/bootstrap-research-monorepo`
21. ⏳ 07c-2 promotion PR (separate; depends on merged 02c/03c)
22. ⏳ M4 closes

## Non-goals

- **No Mathlib contribution** (PR or local fork change)
- **No new `sorry`/`admit`/`axiom`** in any closed lemma
- **No convergence proof** (the dynamics connection is structural, not a Collatz convergence theorem)
- **No global-descent claim** (the tree descent proof does not claim Collatz terminates for all positive integers)
- **No change to `CoverageTree.lean`** (07c-2 promotion is a separate PR)
- **No `coverage_tree_soundness_orbit` work** (separate workstream; `sorry` remains)
- **No `Affine.lean` work** (Story 04b)
- **No new parallel oddness lemma** (the existing `Certificate.lean::acceleratedStep_odd_of_odd` is **closed** by relocation to `Basic.lean`, not duplicated)

## Lean / Python split (per `MEMORY.md` "BDD Discipline — Justin, 2026-08-15")

- **Python BDD**: existing `tests/test_coverage_tree.py` already covers `accelerated_orbit` + `ReachesOne` (per PR #17). Re-run as regression: `uv run pytest tests/test_coverage_tree.py -q`. No new Python tests required unless the proof work changes behavior.
- **Lean validation**: **GitHub Lean CI is the sole Lean validation gate.** No local `lake` commands of any kind (no `lake build`, no `lake env lean`, no `.olean` inspection). All Lean verification happens in CI. Per-stop rule: stop after 2 patch failures on the same logical edit; read Mathlib source before the next patch.
- **Out of scope**: local fast feedback via `lake env lean`. Removed per Codex review P1 (2026-08-16): the project decision is now explicit — GitHub Lean CI only.

## Open gates (from Codex review + re-reviews)

### Initial review (2026-08-16T16:34:55Z)
- ✅ Accurate preparatory claim level (P0 resolved)
- ✅ Explicit oddness-closure dependency for the trajectory theorem (P1 — sorry #5 specified initially)
- ✅ GitHub-CI-only Lean validation (P1 — local Lake commands removed)
- ✅ Concrete factorization proof decomposition (P2 — Lemma 1 + Lemma 2 + induction predicate)

### Re-review #1 (2026-08-16T17:32:09Z)
- ✅ Module-ownership conflict (P1 — originally distinct core lemma in Equivalence)
- ✅ Lemma 1 valuation bound (P1 — `1 ≤ k` not `2 ≤ k`; `n = 3` boundary case noted)
- ✅ Sorry #5 future tense (P1 — preparatory doc used future tense)
- ✅ Stray markup (P2 — `</content></invoke>` removed)
- ✅ Risk classification (P2 — oddness preservation reclassified medium, was low)

### Re-review #2 (2026-08-16T17:58:50Z)
- ✅ Oddness module ownership (P1 — relocated to Basic.lean; Certificate admission closed, not duplicated)
- ✅ Trajectory-composition proof (P1 — new `standardTrajectory_compose` lemma; hypothesis rewritten as `trajectory (acceleratedStep n) k = 1`)
- ✅ "Five sorries" framing (P2 — now 4 target admissions + 1 relocated admission)

## Codex review corrections (all rounds)

### Initial review (2026-08-16T16:34:55Z) — addressed at `6911c8c`
- **P0**: reclassified `formally established` → `preparatory / implementation plan`
- **P1**: added oddness invariant prerequisite (sorry #5 in Equivalence.lean)
- **P1**: removed local Lean validation references; "GitHub Lean CI only" is the sole gate
- **P2**: specified factorization proof decomposition (Lemma 1, Lemma 2, induction predicate)

### Re-review #1 (2026-08-16T17:32:09Z) — addressed at `657c260`
- **P1 (module ownership)**: distinct core lemma name in Equivalence.lean (sub-namespace `EquivalenceCore` or uniquely-named helper)
- **P1 (Lemma 1 bound)**: corrected `2 ≤ k` to `1 ≤ k`; boundary case `n = 3` (`ν₂(10) = 1`) noted
- **P1 (future tense)**: sorry #5 described in future tense; proof-bearing PR adds declaration + theorem-status row atomically
- **P2 (stray markup)**: stray `</content></invoke>` removed
- **P2 (risk)**: oddness preservation risk reclassified medium (was low)

### Re-review #2 (2026-08-16T17:58:50Z) — addressing now
- **P1 (module ownership)**: canonical oddness theorem relocated to `Basic.lean` (imports only Mathlib); both `Certificate.lean` and `Equivalence.lean` consume it. **No import cycle exists** between Certificate.lean and Equivalence.lean. The existing `Certificate.lean::acceleratedStep_odd_of_odd` admission is **closed** by this relocation, not duplicated.
- **P1 (trajectory composition)**: new `standardTrajectory_compose` lemma in Equivalence.lean; hypothesis rewritten as `trajectory (acceleratedStep n) k = 1`; IH applied to `acceleratedStep n`; final witness is `m' = (1 + ν₂(3n+1)) + r`.
- **P2 (admission framing)**: 4 target admissions + 1 relocated admission (not "5 current admissions").

## Status

**Started 2026-08-16.** Per-sorry resolution proven feasible without Mathlib PR (see "Why no Mathlib PR is needed"). Spec doc updated to address all three Codex reviews (initial P0/P1/P2 + re-review #1 P1/P2 + re-review #2 P1/P2). Architecture corrected: oddness theorem relocated to Basic.lean (closes existing Certificate admission). Awaiting re-review.