/-
Q5 PR #4 — integration of the Lean verifier + bounded-input companion
theorem (Q5 v5 spec § 4.3.1a, § 4.3.2, § 4.4).

The Q5 4-PR split places:
- PR #61 (merged at `1fa90bd`): Q5 spec.
- PR #62 (merged at `5215fd1`): `BoundedInputCertificateWire` +
  `BoundedInputCertificateData` + `checkBoundedCertificate` Bool
  verifier. **In-memory wire model + structural validation.**
- PR #63 (merged at `18a948e`): Python external generator +
  hand-rolled JSON parser + parser-rejection tests.
  **Producer + parser-side boundary; producer is UNTRUSTED.**
- PR #4 (THIS FILE): integration.

## Trust boundary (Q5 v5 spec § 3)

```
Python serialized evidence → (PR #63 parser)
                            → BoundedInputCertificateWire
                            → decodeBoundedInputCertificateData (PR #62)
                            → BoundedInputCertificateData
                            → checkBoundedCertificate (PR #62)
                            → Bool verifier (PR #4 soundness — v2b)
                            → BoundedInputOrbitCertificate (this PR)
                            → coverage_tree_soundness_orbit_cert_bounded (this PR)
                            → ∀ x, 0 < x → x ≤ N → ReachesOne x
```

Producer + parser are UNTRUSTED. Only the Lean verifier + soundness
theorem + companion theorem enter the TCB.

## v2a scope (this commit — Q1 + P1 + P2 review fixes)

- `BoundedInputOrbitCertificate` structure (mirror of Q4 v3
  `BoundedOrbitCertificate` with explicit `N : Nat` input bound).
- `coverage_tree_soundness_orbit_cert_bounded` (parallel bounded
  companion theorem mirroring PR #58's unbounded
  `coverage_tree_soundness_orbit_cert`).
- `per_leaf_available_bounded_of_hCert` (hypothesis-eliminator form
  of the per-leaf availability pattern; renamed from v1's
  `per_leaf_available_bounded` per Codex P2 — the `_of_hCert` suffix
  makes the eliminator nature explicit at the call site).
- Conditional type-check example for `depthTwoTree` (renamed from v1's
  "closed-form example" per Codex P2 — the example does NOT construct
  a closed-form certificate; it only confirms the bounded companion
  theorem type-checks against a hypothetical per-leaf certificate
  dataset).
- Tests in `Q5IntegrationTests.lean` (updated to match the new
  `0 < x` API shape + new theorem names).

**Q1 P1 fix (Codex review on v1 `1209cdb`):** `orbit_hits_claim`
premise now includes `0 < x →` (matching PR #58's
`coverage_tree_soundness_orbit_cert` convention). The certificate's
input domain is `{1, ..., N}`, not `{0, ..., N}`. For `x = 0`, the
premise `0 < x` is `False`, so the certificate is silent.

## v2b scope (deferred — next commit in this PR)

- `checkBoundedCertificate_sound` (the verifier soundness theorem).
  Connects `checkBoundedCertificate = true` (plus an external
  `claim_reaches_one` hypothesis) to
  `BoundedInputOrbitCertificate`. Substantial proof — extracts per-
  witness check from `List.foldl`, applies the trajectory-indexing
  lemma to bridge `trajectory.last = claim.Holds` to
  `claim.Holds (accelerated_orbit x (trajectory.length - 1))`.
- `per_leaf_available_bounded_of_check` (constructive availability
  theorem per Codex Q5 verdict — takes `BoundedInputCertificateData`
  per verified leaf + the per-leaf `check = true` evidence + the
  per-leaf `claim_reaches_one` hypothesis, returns the per-leaf
  certificate constructively).

## Lessons applied (Q3 v4 + Q4 v3 + META)

- **Pattern 2.10** (conditional companion theorem pattern): explicit
  `hCert` hypothesis preserved on `coverage_tree_soundness_orbit_cert_bounded`.
- **Q4 lessons (`: Type` sort)**: `BoundedInputOrbitCertificate` is
  `: Type`-valued (data + proof fields). NO `Prop`-valued sort
  conflict.
- **META § 3.2** (per-leaf availability): `per_leaf_available_bounded_of_hCert`
  (hypothesis-eliminator form) is the v2a placeholder. The v2b
  constructive form `per_leaf_available_bounded_of_check` supersedes
  it once the verifier soundness theorem lands.
- **META § 3.3** (avoid universal acceptance): the conditional
  type-check example is scoped to `depthTwoTree` + bounded `N`; the
  universal-`∀ t` claim stays conditional on `hv + hc + hCert`.

Story Q5 / PR #4 v2a (Q1 + P1 + P2 review fixes: `0 < x` premise
on `orbit_hits_claim`, re-scoped docstrings, renamed
`per_leaf_available_bounded_of_hCert`, reworded `depthTwoTree`
example as conditional type-check). Verifier soundness theorem
deferred to v2b in a follow-up commit. -/

import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData

namespace CollatzResearch

/-! ## Bounded-input orbit-routing certificate (Q5 v5 spec § 4.3.2)

Mirror of Q4 v3 `BoundedOrbitCertificate` (PR #57) with an explicit
`N : Nat` bound on the input domain. The two structures coexist:

- `BoundedOrbitCertificate` (PR #57, master): formal type,
  hypothesis-bearing — the unconditional orbit-routing claim over
  all `x`.
- `BoundedInputOrbitCertificate` (Q5, NEW): constructible type with
  bounded quantifier — proves the orbit-routing claim for
  `1 ≤ x ≤ N`.

The bound `N` is the input domain cap: the certificate is meaningful
for inputs `x ∈ {1, ..., N}`. For `x ≤ 0` or `x > N`, the
certificate is silent (matches the Q5 v5 spec: bounded end-to-end,
no conversion to unbounded `BoundedOrbitCertificate`). -/

/-- Bounded-input orbit-routing certificate for a leaf `l` in tree
    `t`, with explicit `N : Nat` bound on the input domain.

    Two obligation fields, both `Prop`-valued (kernel-checked):
    1. `orbit_hits_claim : ∀ x, 0 < x → x ≤ N → descendOrbit t x 0 =
       some l → ∃ k, claim.Holds (accelerated_orbit x k)` — every
       positive input `x ≤ N` routed (orbit-aware) to `l` reaches a
       claim.Holds orbit state.
    2. `claim_reaches_one : ∀ y, claim.Holds y → ReachesOne y` —
       every claim-target state reaches 1.

    The `0 < x →` premise in `orbit_hits_claim` matches PR #58's
    `coverage_tree_soundness_orbit_cert` convention (Q1 P1 fix from
    Codex review on v1 `1209cdb`): the certificate's input domain
    is `{1, ..., N}`, not `{0, ..., N}`. For `x = 0`, the premise
    `0 < x` is `False`, so the certificate is silent (matches the
    Collatz convention — the conjecture is for positive integers).

    `: Type`-valued proof-carrying data bundle (NOT `: Prop`): the
    `claim : FiniteOrbitClaim` data field requires `Type`-valued
    sort per Q3 v4 lessons (Lean 4 elaboration rejects `Type`-valued
    fields in `: Prop` structures).

    Companion to `BoundedOrbitCertificate` (Q4 v3, PR #57). NO mutual
    exclusion — a leaf can carry both `BoundedOrbitCertificate t l`
    (Q4 v3, hypothesis-bearing) and `BoundedInputOrbitCertificate t
    l N` (Q5 NEW, bounded) as independent views of its semantic
    content. They conclude different leaf-level predicates (via the
    companion theorems) and certify the same routing relation
    (`descendOrbit`) under different input-domain scopes.

    Inserted after `BoundedOrbitCertificate` (Q4 v3, PR #57) so the
    two can be compared side-by-side.

    API-shape regression: `boundedInputOrbitCertShape` at the
    end of `Q5IntegrationTests.lean` (mirrors PR #57's
    `boundedCertificateClaim`). -/
structure BoundedInputOrbitCertificate (t : CoverageTree) (l : CoverageLeaf)
    (N : Nat) : Type where
  claim : FiniteOrbitClaim
  orbit_hits_claim :
    ∀ x, 0 < x → x ≤ N → descendOrbit t x 0 = some l →
      ∃ k, claim.Holds (accelerated_orbit x k)
  claim_reaches_one :
    ∀ y, claim.Holds y → ReachesOne y

/-! ## Bounded-input companion theorem (Q5 v5 spec § 4.4)

Parallel of PR #58's `coverage_tree_soundness_orbit_cert` with the
additional `N : Nat` bound on the input domain. The conclusion is
`ReachesOne x` (NOT `OrbitLeafReachesOne t l`, which is the
unbounded Q4 v3 form): for `1 ≤ x ≤ N`, `x` reaches 1.

The proof mirrors PR #58:
1. Apply `descend_orbit_complete` (PR #29) for orbit-aware routing.
2. Apply `BoundedInputOrbitCertificate.orbit_hits_claim` to get a
   `k` with `claim.Holds (accelerated_orbit x k)`.
3. Apply `BoundedInputOrbitCertificate.claim_reaches_one` to get
   `ReachesOne (accelerated_orbit x k)`.
4. Apply `orbit_predecessor_reaches_one` (PR #56) to close:
   `ReachesOne (accelerated_orbit x k) → ReachesOne x`.

The `hN : x ≤ N` hypothesis is the only addition to the PR #58
statement. The `hCert` hypothesis uses `BoundedInputOrbitCertificate`
(the bounded type) rather than `BoundedOrbitCertificate` (the
unbounded type) — explicit per META § 3.3 (avoid universal
acceptance). -/

/-- Bounded-input parallel of `coverage_tree_soundness_orbit_cert`
    (PR #58, Q4 v3). For each positive input `x ≤ N` routed to a
    leaf with a `BoundedInputOrbitCertificate`, `ReachesOne x`.

    The bound `N` is the input domain cap; for `x > N`, the theorem
    is silent (matches Q5 v5 spec § 4.5: bounded end-to-end).

    **Proof status: structurally proved** (mirrors PR #58 proof;
    uses `descend_orbit_complete` + `orbit_predecessor_reaches_one`
    + the bounded certificate's `orbit_hits_claim` /
    `claim_reaches_one`). -/
theorem coverage_tree_soundness_orbit_cert_bounded
    (t : CoverageTree)
    (N : Nat)
    (hv : ValidTree t) (hic : IsComplete t)
    (hCert : ∀ l ∈ t.leaves, verified t l →
      BoundedInputOrbitCertificate t l N)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    ∃ l, l ∈ t.leaves ∧ verified t l ∧
         descendOrbit t x 0 = some l ∧
         ReachesOne x := by
  obtain ⟨l, hl, hver, hdesc, hroute⟩ := descend_orbit_complete t hv hic x hx
  obtain cert := hCert l hl hver
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x hx hN hdesc
  exact ⟨l, hl, hver, hdesc,
    orbit_predecessor_reaches_one x k (accelerated_orbit x k) rfl
      (cert.claim_reaches_one (accelerated_orbit x k) hk)⟩

/-! ## Per-leaf availability pattern — hypothesis-eliminator form (Q5 v5 spec § 4.4)

`per_leaf_available_bounded_of_hCert` is the v2a hypothesis-eliminator
form of the per-leaf availability pattern. It takes the per-leaf
certificate hypothesis `hCert` (parallel to PR #58's `hCert` pattern)
and projects it to a specific leaf.

**This is NOT a constructive availability theorem** — it does not
construct the per-leaf certificate from verifier evidence. It is a
trivial wrapper that surfaces a hypothesis already in scope. The v2b
constructive form `per_leaf_available_bounded_of_check` supersedes
it once the verifier soundness theorem lands.

Renamed from v1's `per_leaf_available_bounded` per Codex P2 (P2
finding on v1 `1209cdb`) to avoid implying that the hypothesis form
is the canonical per-leaf availability pattern. The suffix
`_of_hCert` makes the eliminator nature explicit at the call site. -/

/-- Per-leaf availability pattern — HYPOTHESIS-ELIMINATOR form (v2a).
    For each verified leaf `l`, the per-leaf certificate
    (`BoundedInputOrbitCertificate t l N`) is available from the
    `hCert` hypothesis (parallel to PR #58's `hCert` pattern).

    Renamed from v1's `per_leaf_available_bounded` per Codex P2.
    This is NOT a constructive availability theorem — see the v2b
    `per_leaf_available_bounded_of_check` (deferred) for the
    constructive form. -/
def per_leaf_available_bounded_of_hCert
    (t : CoverageTree)
    (N : Nat)
    (hCert : ∀ l ∈ t.leaves, verified t l →
      BoundedInputOrbitCertificate t l N)
    (l : CoverageLeaf)
    (hl : l ∈ t.leaves)
    (hver : verified t l) :
    BoundedInputOrbitCertificate t l N :=
  hCert l hl hver

/-! ## Conditional type-check example for `depthTwoTree`

The concrete tree scope per Q5 v5 spec § 4.5. Composes the bounded
companion theorem with the per-leaf availability pattern.

**v1 framing was misleading** — the example does NOT construct a
closed-form certificate. It confirms that the bounded companion
theorem type-checks against `depthTwoTree` + a hypothetical
per-leaf certificate dataset (per Codex P2 on v1 `1209cdb`).

The v2b constructive form would require supplying
`BoundedInputCertificateData` per leaf + the per-leaf verifier
result + the per-leaf reachability hypothesis. That scenario is
not constructed here — the per-leaf `checkBoundedCertificate = true`
evidence is NOT closed in this example (the verifier would need to
actually run on `depthTwoTree` for `1 ≤ x ≤ N` to produce it).

**The example remains type-only.** It defends the bounded companion
theorem's signature against accidental changes — no semantic claim
about `depthTwoTree` is made. -/

/-- Conditional type-check example for `depthTwoTree` + bounded input
    domain. Confirms the bounded companion theorem closes for the
    concrete tree + a hypothetical per-leaf certificate dataset.

    Renamed from v1's "closed-form example" per Codex P2 — the
    example does NOT construct a closed-form certificate. It only
    confirms the bounded companion theorem type-checks.

    `hv : ValidTree depthTwoTree` and `hc : IsComplete depthTwoTree`
    are discharged via `native_decide` (the standard depthTwoTree
    structural invariants; see `CoverageTreeOrbitTests.lean` for
    the underlying defs).

    `hCert` is the per-leaf certificate dataset (hypothesis for v2a;
    will be replaced by a constructive construction via
    `per_leaf_available_bounded_of_check` in v2b once the per-leaf
    `checkBoundedCertificate = true` evidence is available for
    `depthTwoTree`).

    The conclusion: for each positive `x ≤ N`, `x` reaches 1.
    Bounded end-to-end per Q5 v5 spec. -/
example (N : Nat)
    (hv : ValidTree depthTwoTree := by native_decide)
    (hc : IsComplete depthTwoTree := by native_decide)
    (hCert : ∀ l ∈ depthTwoTree.leaves, verified depthTwoTree l →
      BoundedInputOrbitCertificate depthTwoTree l N)
    (x : Nat) (hx : 0 < x) (hN : x ≤ N) :
    ∃ l, l ∈ depthTwoTree.leaves ∧ verified depthTwoTree l ∧
         descendOrbit depthTwoTree x 0 = some l ∧
         ReachesOne x :=
  coverage_tree_soundness_orbit_cert_bounded depthTwoTree N hv hc hCert x hx hN

/-! ## v2b soundness helpers — Lemmas 1 & 2 (Q5 PR #4 v2b proof decomposition)

The Q5 PR #4 v2 soundness theorem (`checkBoundedCertificate_sound`,
deferred to v2b.4) needs a chain of helper lemmas per
`docs/story-q5-pr4-v2b-proof-decomposition.md`. Lemmas 1 and 2 are
the mechanical extractions that all later lemmas build on:

  * **Lemma 1** (`foldl_and_extract`): pure `List`/`Bool` reasoning
    that lifts `foldl ... true ts = true` to per-element truth.
    Fully polymorphic over the list element type — no commitment
    to `CertWitness`.
  * **Lemma 2** (`checkCertWitness_decompose`): biconditional
    between `checkCertWitness = true` and the 5-fold conjunction of
    named conjuncts (`anchorOk` ∧ `leafMatchOk` ∧ `routingOk` ∧
    `terminalClaimOk` ∧ `transitionOk`).

**Lessons applied (META § 3.3 — avoid universal acceptance):** both
lemmas stay conditional on explicit hypotheses; no `by sorry`, no
default acceptance.

**Lesson applied (Q3 v4 — :Type sort):** the 5 helper predicates are
`Bool`-valued (NOT `Prop`); they are predicates of the WITNESS, not
proofs. The decomposition is a *boolean* identity. -/

/-- Anchor check (witness predicate): the witness trajectory is
    non-empty AND its head matches the type-level input `x`.
    Returns `false` on empty trajectory (mirrors the early-reject
    in `checkCertWitness`). -/
def anchorOk (x : Nat) (w : CertWitness x) : Bool :=
  match w.trajectory with
  | [] => false
  | hd :: _ => hd == x

/-- Leaf match check (witness predicate): the witness's leaf
    `w.l` matches the expected leaf `l`. -/
def leafMatchOk (w : CertWitness x) (l : CoverageLeaf) : Bool :=
  sameCoverageLeaf w.l l

/-- Routing check (witness predicate): `descendOrbit t x 0` returns
    `some w.l` (the witness's leaf). -/
def routingOk (t : CoverageTree) (x : Nat) (w : CertWitness x) : Bool :=
  routesToWitnessLeaf t x w

/-- Terminal-claim check (witness predicate): the last trajectory
    value satisfies `claim.Holds`. Returns `false` on empty
    trajectory (mirrors the `getLast?` early-reject in
    `checkCertWitness`). -/
def terminalClaimOk (claim : FiniteOrbitClaim) (w : CertWitness x) : Bool :=
  match w.trajectory.getLast? with
  | some last => decide (claim.Holds last)
  | none => false

/-- Transition check (witness predicate): every consecutive pair
    `(w.trajectory[i], w.trajectory[i+1])` satisfies
    `snd = acceleratedStep fst`. Folded via `List.zip`. -/
def transitionOk (w : CertWitness x) : Bool :=
  List.foldl (fun acc pair => acc && pair.snd == acceleratedStep pair.fst)
            true (List.zip w.trajectory w.trajectory.tail)

/-- **Lemma 1 (foldl extraction).** If
    `List.foldl (fun acc x => acc ∧ p x) true ts = true`, then every
    `x ∈ ts` satisfies `p x = true`.

    Pure `List`/`Bool` reasoning. Standard induction on `ts`. The
    `true` seed + `&&` makes the extraction clean — there is no
    special case for the first element; `(true && p a) = p a` by
    `Bool.and` identity.

    **Fully polymorphic** over `α : Type u`. The application to
    `checkBoundedCertificate` (which folds over `Fin d.wire.N`
    inside `List.finRange d.wire.N`) happens in Lemma 5 — a
    one-line corollary of this lemma applied to the right
    predicate.

    Plan dependency: feeds Lemma 5 (soundness assembly) via the
    per-witness `checkCertWitness` extraction. -/
theorem foldl_and_extract {α : Type u} (ts : List α) (p : α → Bool)
    (h : List.foldl (fun acc x => acc ∧ p x) true ts = true)
    : ∀ x, x ∈ ts → p x = true := by
  induction ts with
  | nil =>
    intros _ hx
    -- `x ∈ []` is contradictory; eliminated.
    cases hx
  | cons a rest ih =>
    intros x hx
    cases hx with
    | inl hxa =>
      -- `x = a`: prove `p a = true` directly from `h`.
      subst hxa
      -- `(true && p a) = p a` by Bool identity (case-split on `p a`).
      have hp_eq : (true && p a) = p a := by
        cases hp : p a <;> simp [hp]
      rw [hp_eq] at h
      -- `h : (p a ∧ List.foldl (fun acc x => acc ∧ p x) (p a) rest) = true`
      rw [Bool.and_eq_true] at h
      exact h.1
    | inr hxr =>
      -- `x ∈ rest`: apply induction hypothesis to `h`.
      have hp_eq : (true && p a) = p a := by
        cases hp : p a <;> simp [hp]
      rw [hp_eq] at h
      rw [Bool.and_eq_true] at h
      -- `h.2 : List.foldl (fun acc x => acc ∧ p x) true rest = true`
      exact ih h.2 x hxr

/-- **Lemma 2 (witness-check decomposition).** `checkCertWitness`
    is true iff all 5 named conjuncts (anchor, leaf, routing,
    terminal claim, transition) hold.

    The biconditional follows by unfolding `checkCertWitness` and
    the 5 helpers, then observing that both sides reduce to the
    same boolean expression (modulo `Bool.and` associativity).

    The `match w.trajectory` patterns in `checkCertWitness` and
    `anchorOk` / `terminalClaimOk` coincide; the `match ... getLast?`
    patterns also coincide. After unfolding, both sides are
    syntactically equal boolean expressions, so the biconditional
    reduces to `True`.

    Plan dependency: feeds Lemma 3 (trajectory indexing — uses
    `anchorOk` + `transitionOk`) and Lemma 4 (terminal-claim
    transport — uses `terminalClaimOk`). Each conjunct is
    independently consumed by a different later lemma. -/
theorem checkCertWitness_decompose (x : Nat) (claim : FiniteOrbitClaim)
    (t : CoverageTree) (l : CoverageLeaf) (w : CertWitness x) :
    checkCertWitness x claim t l w = true ↔
    (anchorOk x w ∧ leafMatchOk w l ∧ routingOk t x w ∧
     terminalClaimOk claim w ∧ transitionOk w) := by
  -- Unfold both sides. After unfolding, both sides have the same
  -- `match w.trajectory` structure and the same nested
  -- `match ... getLast?` structure.
  unfold checkCertWitness anchorOk leafMatchOk routingOk
    terminalClaimOk transitionOk
  -- Case-split on the trajectory; both `checkCertWitness` and the
  -- helper `match`es share the same pattern.
  cases htr : w.trajectory with
  | nil =>
    -- Both sides reduce to `false`: `checkCertWitness []` is
    -- `false`; the RHS has `anchorOk [] = false` and
    -- `false ∧ ... = false`.
    simp [htr]
  | cons hd tl =>
    -- Both sides reduce to the same 5-fold conjunction; `simp`
    -- closes the biconditional via `Bool.and_eq_true` +
    -- `decide` equivalence.
    simp [htr, Bool.and_eq_true]

/-! ## v2b.2 — Lemma 3 (trajectory indexing)

The trajectory-indexing lemma bridges the witness's `List Nat`
trajectory to the `accelerated_orbit` index used by
`BoundedInputOrbitCertificate.orbit_hits_claim`.

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § 3, the proof
relies on:
  - `accelerated_orbit_zero` + `accelerated_orbit_succ` (PR #56) for
    `accelerated_orbit` unfolding,
  - `anchorOk_implies_get_zero` (bridging lemma, kernel-clean) for
    the base case.

**v2b.2 Codex P0 fix (2026-09-02):** the original Lemma 3 took
`hTrans : transitionOk w = true` and used a bridging lemma
`transitionOk_implies_step` that required 2 `sorry` placeholders
for Mathlib list indexing (`List.length_zip`, `List.get_zip`).
Per Codex review `PRR_kwDOTuMD788AAAABL71GQA`, the `sorry` budget
must not be raised; the admitted theorem/proof skeleton must be
removed.

**Restructured Lemma 3:** takes the per-pair `acceleratedStep`
check directly as a hypothesis (not via `transitionOk`). The
proof is now fully kernel-checked — no `sorry`, no `admit`, no
`axiom`. The trade-off: callers must provide the per-pair check
explicitly (which is morally equivalent to `transitionOk = true`
but skips the list-zip extraction).

**Bridging lemma:** `anchorOk_implies_get_zero` (kernel-clean)
gives `trajectory[0]! = x` from `anchorOk x w = true`.

**Risk (per plan).** The Lean 4 indexing notation `[i]!` may
need re-expression as `List.get` with explicit `i < length`
proofs depending on Lean 4 version compatibility.

Lesson applied (Q4 v3 Pattern 2.10): explicit hypothesis
preservation throughout — `trajectory_index` takes `hAnchor` and
`hTrans` as explicit arguments. -/

/-- Bridging lemma: `anchorOk x w = true` implies the witness
    trajectory is non-empty with `head = x`. Then
    `(w.trajectory)[0]! = x` follows by list definition.

    Kernel-clean (no `sorry`/`admit`/`axiom`). -/
lemma anchorOk_implies_get_zero (x : Nat) (w : CertWitness x)
    (hAnchor : anchorOk x w = true)
    : (w.trajectory)[0]! = x := by
  unfold anchorOk at hAnchor
  cases htr : w.trajectory with
  | nil =>
    -- `match [] with | [] => false | _ => _` = false; contradicts `hAnchor : true`.
    simp [htr] at hAnchor
  | cons hd tl =>
    -- `match (hd :: tl) with | [] => false | hd :: _ => hd == x` = (hd == x);
    -- `hAnchor : (hd == x) = true` unfolds to `hd = x` via `beq_iff_eq`.
    simp [htr, beq_iff_eq] at hAnchor
    rw [hAnchor]
    -- `(hd :: tl)[0]! = hd` by `List.get` definition for index 0.
    rfl

/-- **Lemma 3 (trajectory indexing, restructured v2b.2 Codex P0
    fix).** For a witness `w` with `anchorOk` true and a
    per-pair `acceleratedStep` check, the trajectory at index
    `k` equals `accelerated_orbit x k`.

    **Type change (v2b.2 Codex P0 fix):** previously took
    `hTrans : transitionOk w = true`; now takes the per-pair
    check directly:
    `hTrans : ∀ i, i + 1 < length → trajectory[i+1]! = acceleratedStep trajectory[i]!`
    This drops the dependency on `transitionOk_implies_step`
    (which had 2 `sorry`s for Mathlib list indexing). The proof
    is now fully kernel-checked.

    Proof by induction on `k`:
    - **Base** (`k = 0`): `accelerated_orbit_zero` gives
      `accelerated_orbit x 0 = x`; `anchorOk_implies_get_zero`
      closes `trajectory[0]! = x`.
    - **Step** (`k + 1`): `accelerated_orbit_succ` gives
      `accelerated_orbit x (k + 1) = acceleratedStep (accelerated_orbit x k)`;
      IH gives `trajectory[k]! = accelerated_orbit x k`;
      `hTrans` closes
      `trajectory[k + 1]! = acceleratedStep trajectory[k]!`.

    Plan dependency: feeds Lemma 4 (terminal-claim transport)
    which substitutes `trajectory[length - 1]` with
    `accelerated_orbit x (length - 1)`. -/
theorem trajectory_index (x : Nat) (w : CertWitness x) (k : Nat)
    (hkl : k < (w.trajectory).length)
    (hAnchor : anchorOk x w = true)
    (hTrans : ∀ i, i + 1 < (w.trajectory).length →
                 (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!))
    : (w.trajectory)[k]! = accelerated_orbit x k := by
  induction k with
  | zero =>
    rw [accelerated_orbit_zero]
    exact anchorOk_implies_get_zero x w hAnchor
  | succ k ih =>
    rw [accelerated_orbit_succ]
    -- IH: `(w.trajectory)[k]! = accelerated_orbit x k` (requires `k < length`).
    have hk : k < (w.trajectory).length := Nat.lt_of_succ_lt hkl
    rw [ih hk]
    -- Need: `(w.trajectory)[k + 1]! = acceleratedStep ((w.trajectory)[k]!)`.
    -- `hTrans` with `i := k` and `k + 1 < length := Nat.lt_succ_of_lt hk`.
    exact hTrans k (Nat.lt_succ_of_lt hk)

/-! ## v2b.3 — Lemma 4 (terminal-claim transport)

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § 4, Lemma 4
bridges the witness trajectory's terminal value to
`accelerated_orbit x (length - 1)`, which is what
`BoundedInputOrbitCertificate.orbit_hits_claim` requires for the
`claim.Holds` goal.

**Type.** Cleaned up from the v2b plan (which had a typo on
`.getLast`). The clean form uses `trajectory[length - 1]!`
(explicit index with `length - 1 < length` proof) rather than
`getLast` (which requires a non-emptiness default):

```lean
terminal_claim_transport : ∀ (x : Nat) (w : CertWitness x)
    (claim : FiniteOrbitClaim),
    claim.Holds ((w.trajectory)[(w.trajectory).length - 1]') →
    claim.Holds (accelerated_orbit x ((w.trajectory).length - 1))
```

The `'` notation requires `length - 1 < length`, established
from `anchorOk = true` (non-empty trajectory).

**Strategy.** Apply Lemma 3 with `k = length - 1` to get
`trajectory[length - 1]! = accelerated_orbit x (length - 1)`,
then substitute into the `claim.Holds` hypothesis. The
substitution goes through `Eq.mp` / `Eq.mpr` (Lean's `rw`
tactic handles this).

Lesson applied (Q4 v3 Pattern 2.10): explicit hypothesis
preservation — `terminal_claim_transport` takes `hAnchor`,
`hTrans` as explicit arguments (no `by sorry`). -/

/-- **Lemma 4 (terminal-claim transport, restructured v2b.2
    Codex P0 fix).** If `claim.Holds` holds at the trajectory's
    last element (index `length - 1`), then it also holds at
    `accelerated_orbit x (length - 1)`.

    **Type change (v2b.2 Codex P0 fix):** `hTrans` now takes the
    per-pair `acceleratedStep` check directly (matching the
    restructured Lemma 3 signature) instead of `transitionOk = true`.

    The proof is a direct application of Lemma 3 with
    `k = length - 1`, then rewriting the `claim.Holds`
    hypothesis. Fully kernel-checked.

    Plan dependency: was intended to feed Lemma 5 (soundness
    assembly), but Lemma 5 is removed per the v2b.2 Codex P0
    fix. Lemma 4 stays as a standalone kernel-checked lemma. -/
theorem terminal_claim_transport (x : Nat) (w : CertWitness x)
    (claim : FiniteOrbitClaim)
    (hAnchor : anchorOk x w = true)
    (hTrans : ∀ i, i + 1 < (w.trajectory).length →
                 (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!))
    (hLast : claim.Holds ((w.trajectory)[(w.trajectory).length - 1]'
             (Nat.pred_lt length_pos)))
    : claim.Holds (accelerated_orbit x ((w.trajectory).length - 1)) := by
  -- Establish `length > 0` from `anchorOk = true` (non-empty).
  have hne : 0 < (w.trajectory).length := by
    unfold anchorOk at hAnchor
    cases htr : w.trajectory with
    | nil =>
      -- `match [] with | [] => false | _ => _` is `false`; contradicts `hAnchor : true`.
      simp [htr] at hAnchor
    | cons hd tl =>
      -- `(hd :: tl).length = tl.length + 1 > 0`.
      rw [htr, List.length]
      exact Nat.succ_pos _
  -- `length - 1 < length` from `length > 0`.
  have hbound : (w.trajectory).length - 1 < (w.trajectory).length :=
      Nat.pred_lt hne
  -- Apply Lemma 3 (restructured) with `k = length - 1`.
  rw [trajectory_index x w ((w.trajectory).length - 1) hbound hAnchor hTrans]
  -- `hLast : claim.Holds (accelerated_orbit x (length - 1))` after rewrite.
  exact hLast

/-! ## v2b.4 — v2b.5 Lemmas 5-6 — REMOVED per Codex P0 (2026-09-02)

**REMOVAL NOTE** (Codex review `PRR_kwDOTuMD788AAAABL71GQA`,
2026-09-02T22:39:09Z):

> [P0] `docs/lean-sorry-budget.json` and
> `Lean/CollatzResearch/Q5Integration.lean:529,532,743,755,758,768`
> — this PR raises the admission budget to permit six new
> `sorry`s, including four in `checkBoundedCertificate_sound`. That
> turns the checker-to-certificate bridge into an untrusted axiom
> while making CI appear green. **Do not extend the budget for this
> path. Remove the admitted theorem/proof skeleton from the Lean
> module (retain the decomposition in the planning document if
> useful) and land only fully checked helper lemmas.** The
> soundness theorem and constructive availability theorem must
> remain absent until proved.

**Removed theorems:**
  - `checkBoundedCertificate_sound` (Lemma 5, 4 explicit sorries):
    the central soundness theorem connecting
    `checkBoundedCertificate = true` to
    `BoundedInputOrbitCertificate`. The decomposition strategy is
    retained in `docs/story-q5-pr4-v2b-proof-decomposition.md`
    § 5 but the implementation is removed.
  - `per_leaf_available_bounded_of_check` (Lemma 6): depended on
    Lemma 5 and inherited the same sorry-laden status.

**Why removed (not closed):** the v2b.2 Codex P0 fix restructured
Lemma 3 to drop the `transitionOk_implies_step` bridging lemma
(which had 2 sorries for `List.length_zip` and `List.get_zip`).
Lemma 5's 4 remaining sorries (nested `Bool.and_eq_true`
destructuring, `ix ∈ List.finRange`, terminal claim extraction)
require substantial Lean 4 Mathlib knowledge beyond the scope of
the current PR.

**Re-attempt gates** (for any future v2b work to re-introduce
Lemma 5):
  1. The 4 remaining sorries closed without budget increase.
  2. Architectural decision (per-leaf vs single-leaf, see below)
     made.
  3. Codex review re-opened on the new proofs.

**Architectural note (Codex P1, 2nd finding):** the per-leaf vs
single-leaf quantification mismatch must also be resolved before
Lemma 6 can be re-attempted. The `dataPerLeaf` family does not
match the existing `checkBoundedCertificate t l d` (which
validates all inputs against ONE FIXED leaf `l`). Future work
must either:
  - (a) scope the verifier/integration to single-leaf trees, OR
  - (b) redesign the wire/checker/certificate interface around
    an input-to-leaf routing partition.

**What remains kernel-checked** in this PR:
  - Lemma 1 (`foldl_and_extract`, fully polymorphic)
  - Lemma 2 (`checkCertWitness_decompose`, biconditional)
  - Lemma 3 (`trajectory_index`, restructured v2b.2 Codex P0 fix
    to take per-pair check directly)
  - Lemma 4 (`terminal_claim_transport`, restructured v2b.2
    Codex P0 fix)
  - 5 helper predicates (`anchorOk`, `leafMatchOk`, `routingOk`,
    `terminalClaimOk`, `transitionOk`)
  - `anchorOk_implies_get_zero` bridging lemma
  - `BoundedInputOrbitCertificate` structure + v2a companion
    theorem + v2a per-leaf availability
  - `depthTwoTree` conditional type-check example

The PR's "soundness theorem" claim is withdrawn. PR #64 remains
DRAFT until a future PR re-attempts Lemma 5 with closed proofs.

end CollatzResearch
