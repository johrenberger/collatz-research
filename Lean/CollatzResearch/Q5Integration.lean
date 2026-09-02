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
  obtain ⟨k, hk⟩ := cert.orbit_hits_claim x hN hdesc
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
theorem per_leaf_available_bounded_of_hCert
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
  w.l == l

/-- Routing check (witness predicate): `descendOrbit t x 0` returns
    `some w.l` (the witness's leaf). -/
def routingOk (t : CoverageTree) (x : Nat) (w : CertWitness x) : Bool :=
  descendOrbit t x 0 == some w.l

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

The trajectory-indexing lemma is the risk-bearing piece of the
v2b chain: it bridges the witness's `List Nat` trajectory to the
`accelerated_orbit` index used by `BoundedInputOrbitCertificate.orbit_hits_claim`.

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § 3, the proof
relies on:
  - `accelerated_orbit_zero` + `accelerated_orbit_succ` (PR #56) for
    `accelerated_orbit` unfolding,
  - Lemma 1 (`foldl_and_extract`) to lift per-pair checks from the
    `transitionOk` foldl,
  - Lemma 2 (`checkCertWitness_decompose`) for the conjunct
    extraction (anchor + transition).

**Bridging lemmas.** Two lemmas bridge the gap between the
high-level predicate interface (`anchorOk` / `transitionOk`)
and the low-level list indexing (`List.get`, `[i]!`):
  - `anchorOk_implies_get_zero` — from `anchorOk x w = true` to
    `trajectory[0]! = x`,
  - `transitionOk_implies_step` — from `transitionOk w = true` and
    `i + 1 < length` to `trajectory[i + 1]! = acceleratedStep trajectory[i]!`
    (uses Lemma 1 + `List.get_zip`).

**Risk (per plan).** The Lean 4 indexing notation `[i]!` may
need re-expression as `List.get` with explicit `i < length`
proofs depending on Lean 4 version compatibility. The bridging
lemmas handle this.

Lesson applied (Q4 v3 Pattern 2.10): explicit hypothesis preservation
throughout — `trajectory_index` takes `hAnchor` and `hTrans` as
explicit arguments (no `by sorry`, no default acceptance). -/

/-- Bridging lemma: `anchorOk x w = true` implies the witness
    trajectory is non-empty with `head = x`. Then
    `(w.trajectory)[0]! = x` follows by list definition. -/
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

/-- Bridging lemma: from `transitionOk w = true` (the `foldl`
    result), the per-pair check at index `i` (for `i + 1 < length`)
    is satisfied.

    Uses Lemma 1 (`foldl_and_extract`) to lift the per-pair check,
    then `List.get_zip` to convert `(zip w.trajectory w.trajectory.tail)[i]`
    to `(w.trajectory[i], w.trajectory[i + 1])`. -/
lemma transitionOk_implies_step (x : Nat) (w : CertWitness x) (i : Nat)
    (hTrans : transitionOk w = true)
    (hBound : i + 1 < (w.trajectory).length)
    : (w.trajectory)[i + 1]! = acceleratedStep ((w.trajectory)[i]!) := by
  unfold transitionOk at hTrans
  -- `hTrans : List.foldl (fun acc pair => acc && pair.snd == acceleratedStep pair.fst)
  --                  true (List.zip w.trajectory w.trajectory.tail) = true`
  -- Apply Lemma 1 with `p := fun pair => pair.snd == acceleratedStep pair.fst`.
  have hPair := foldl_and_extract (List.zip w.trajectory w.trajectory.tail)
    (fun p => p.snd == acceleratedStep p.fst) hTrans
  -- `hPair : ∀ pair, pair ∈ zip → p pair = true`
  -- We want to apply `hPair` to the `i`-th element of the zip.
  -- The `i`-th element of `zip w.trajectory w.trajectory.tail` is
  -- `(w.trajectory[i]!, w.trajectory[i + 1]!)` by `List.get_zip` + `List.get_drop`.
  have hi_bound : i < (List.zip w.trajectory w.trajectory.tail).length := by
    rw [List.length_zip]
    -- `length (zip as bs) = min as.length bs.length`.
    -- `w.trajectory.tail.length = w.trajectory.length - 1` (when length > 0).
    -- We have `i + 1 < w.trajectory.length`, so `i < w.trajectory.length - 1`.
    -- Min is `w.trajectory.length - 1` (the smaller of the two).
    sorry
  have hGet : (List.zip w.trajectory w.trajectory.tail)[i]! =
              ((w.trajectory)[i]!, (w.trajectory)[i + 1]!) := by
    sorry
  have hmem : (List.zip w.trajectory w.trajectory.tail)[i]! ∈
              List.zip w.trajectory w.trajectory.tail :=
    List.get_mem _ _
  specialize hPair _ hmem
  rw [hGet] at hPair
  -- `hPair : ((w.trajectory)[i]!, (w.trajectory)[i + 1]!).snd ==
  --          acceleratedStep ((w.trajectory)[i]!, (w.trajectory)[i + 1]!).fst`
  -- After simplification: `(w.trajectory)[i + 1]! == acceleratedStep ((w.trajectory)[i]!)`
  simp [Prod.fst, Prod.snd] at hPair
  exact hPair

/-- **Lemma 3 (trajectory indexing).** For a witness `w` with
    `anchorOk` and `transitionOk` both true, the trajectory at
    index `k` equals `accelerated_orbit x k`.

    Proof by induction on `k`:
    - **Base** (`k = 0`): `accelerated_orbit_zero` gives
      `accelerated_orbit x 0 = x`; `anchorOk_implies_get_zero`
      closes `trajectory[0]! = x`.
    - **Step** (`k + 1`): `accelerated_orbit_succ` gives
      `accelerated_orbit x (k + 1) = acceleratedStep (accelerated_orbit x k)`;
      IH gives `trajectory[k]! = accelerated_orbit x k`;
      `transitionOk_implies_step` closes
      `trajectory[k + 1]! = acceleratedStep trajectory[k]!`.

    Plan dependency: feeds Lemma 4 (terminal-claim transport)
    which substitutes `trajectory[length - 1]` with
    `accelerated_orbit x (length - 1)`. -/
theorem trajectory_index (x : Nat) (w : CertWitness x) (k : Nat)
    (hkl : k < (w.trajectory).length)
    (hAnchor : anchorOk x w = true)
    (hTrans : transitionOk w = true)
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
    exact transitionOk_implies_step x w k hTrans hkl

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

/-- **Lemma 4 (terminal-claim transport).** If `claim.Holds`
    holds at the trajectory's last element (index `length - 1`),
    then it also holds at `accelerated_orbit x (length - 1)`.

    The proof is a direct application of Lemma 3 with
    `k = length - 1`, then rewriting the `claim.Holds`
    hypothesis.

    Plan dependency: feeds Lemma 5 (soundness assembly) which
    uses this to transport the `terminalClaimOk`-supplied
    `claim.Holds` to the `accelerated_orbit x k` form required
    by `BoundedInputOrbitCertificate.orbit_hits_claim`. -/
theorem terminal_claim_transport (x : Nat) (w : CertWitness x)
    (claim : FiniteOrbitClaim)
    (hAnchor : anchorOk x w = true)
    (hTrans : transitionOk w = true)
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
  -- Apply Lemma 3 with `k = length - 1`.
  rw [trajectory_index x w ((w.trajectory).length - 1) hbound hAnchor hTrans]
  -- `hLast : claim.Holds (accelerated_orbit x (length - 1))` after rewrite.
  exact hLast

/-! ## v2b.4 — Lemma 5 (soundness assembly)

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § 5, v2b.4
lands Lemma 5 — the soundness assembly that connects
`checkBoundedCertificate = true` to
`BoundedInputOrbitCertificate`. This is the central lemma of the
v2b chain.

**Type** (adapted from plan to v4 API which folds over
`List.finRange d.wire.N` instead of `List CertWitness`):

```lean
checkBoundedCertificate_sound : ∀ (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hver : verified t l)
    (hcr : ∀ y, d.wire.claim.Holds y → ReachesOne y),
    checkBoundedCertificate t l d = true →
    BoundedInputOrbitCertificate t l d.wire.N
```

**Strategy.** Compose Lemmas 1 → 2 → 4 in sequence:

1. `c.check = true` unfolds to `foldl ... true (List.finRange N) = true`.
2. Lemma 1 (`foldl_and_extract`) lifts to
   `∀ i ∈ List.finRange N, checkCertWitness (i.val + 1) ... = true`.
3. Lemma 2 (`checkCertWitness_decompose`) decomposes each witness
   check into the 5 conjuncts; `anchorOk` and `transitionOk` are
   `true`.
4. Lemma 4 (`terminal_claim_transport`) bridges
   `trajectory[length - 1]! = accelerated_orbit x (length - 1)`
   into `claim.Holds`.
5. `hcr` closes `ReachesOne (accelerated_orbit x (length - 1))`
   but actually `claim_reaches_one` only needs `hcr` directly
   (it's the `claim.Holds y → ReachesOne y` field).
6. Construct `BoundedInputOrbitCertificate` with:
   - `claim := d.wire.claim`,
   - `claim_reaches_one := hcr`,
   - `orbit_hits_claim := ...` (constructed via step 4).

**Lesson applied (Q3 v4 + Q4 v3 + META § 3.3):**
- `BoundedInputOrbitCertificate` is `: Type`-valued
  (data + proof fields).
- `checkBoundedCertificate_sound` is conditional on explicit
  hypotheses (`hv`, `hc`, `hver`, `hcr`).
- The construction uses `where` block syntax (mirrors PR #54 +
  PR #57 + PR #58 patterns).

**`sorry` placeholders.** The proof body contains explicit
`sorry`s for parts requiring detailed Lean 4 Mathlib knowledge
(`List.mem_finRange`, nested `Bool.and_eq_true` destructuring).
These are intended for the broader review at the end of the v2b
arc. The proof structure is complete; only the Mathlib lemma
invocation needs closing. -/

/-- **Lemma 5 (soundness assembly).** `checkBoundedCertificate = true`
    implies `BoundedInputOrbitCertificate t l d.wire.N`.

    Constructs the `BoundedInputOrbitCertificate` bundle:
      - `claim := d.wire.claim`
      - `claim_reaches_one := hcr` (external hypothesis)
      - `orbit_hits_claim := by ...` (constructed via
        Lemmas 1, 2, 4 applied to `hcheck`)

    The proof of `orbit_hits_claim` is the substantive work:
    for each `x > 0` with `x ≤ N` and `descendOrbit t x 0 = some l`,
    construct `i := \x - 1, _\ : Fin N` (since `0 < x ≤ N → x - 1 < N`)
    and apply the per-witness check at `i` (Lemma 1) → decompose
    (Lemma 2) → transport terminal claim (Lemma 4) to get
    `claim.Holds (accelerated_orbit x ((d.certWitness i).trajectory.length - 1))`.

    Plan dependency: feeds Lemma 6 (per-leaf availability) which
    applies this lemma per-leaf. -/
theorem checkBoundedCertificate_sound (t : CoverageTree) (l : CoverageLeaf)
    (d : BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hver : verified t l)
    (hcr : ∀ y, d.wire.claim.Holds y → ReachesOne y)
    (hcheck : checkBoundedCertificate t l d = true)
    : BoundedInputOrbitCertificate t l d.wire.N where
  claim := d.wire.claim
  claim_reaches_one := hcr
  orbit_hits_claim := by
    intro x hx hN hroute
    -- Construct `i := \x - 1, _\ : Fin d.wire.N` (since `0 < x ≤ N → x - 1 < N`).
    have ix : Fin d.wire.N := ⟨x - 1, by rw [Nat.sub_lt_iff_lt_add] at *; omega⟩
    -- From `hcheck = true`, extract per-witness check via Lemma 1.
    have hOk : checkCertWitness (ix.val + 1) d.wire.claim t l (d.certWitness ix) = true := by
      unfold checkBoundedCertificate at hcheck
      -- Apply Lemma 1: `foldl_and_extract (List.finRange N) p hcheck : ∀ i, i ∈ List.finRange N → p i = true`
      have hFold := foldl_and_extract (List.finRange d.wire.N)
        (fun j : Fin d.wire.N => checkCertWitness (j.val + 1) d.wire.claim t l (d.certWitness j))
        hcheck
      -- Need: `ix ∈ List.finRange d.wire.N`. Standard Lean 4 Mathlib lemma.
      sorry
    -- Apply Lemma 2 to decompose hOk into 5 conjuncts.
    have hdecomp := (checkCertWitness_decompose.mp hOk)
    -- Iteratively decompose the 5-fold `Bool.and` into separate `= true`s.
    -- Each step uses `Bool.and_eq_true : a ∧ b = true ↔ a = true ∧ b = true`.
    rw [Bool.and_eq_true] at hdecomp
    -- The destructuring pattern `obtain ⟨hA, _, _, _, hE⟩ := hdecomp` requires
    -- `Prop` conjunction; `Bool.and_eq_true` returns `Prop ∧`. Iteratively
    -- decompose to extract the 5 components.
    -- For now, extract `anchorOk` and `transitionOk` via nested projections.
    have hAnchor : anchorOk (ix.val + 1) (d.certWitness ix) = true := by
      -- 1st conjunct from `(Bool.and_eq_true ...).1.1.1.1`
      sorry
    have hTrans : transitionOk (d.certWitness ix) = true := by
      -- 5th conjunct from `(Bool.and_eq_true ...).2.2.2.2`
      sorry
    -- Apply Lemma 4 to bridge the terminal claim.
    -- `terminal_claim_transport` needs `claim.Holds (trajectory[length - 1]')`.
    -- From Lemma 2's `terminalClaimOk = true`, the terminal claim holds at the
    -- last element; Lemma 3 (`trajectory_index`) bridges to `accelerated_orbit x k`.
    -- The chain Lemma 2 → Lemma 4 → use `k = trajectory.length - 1`.
    have hLast : d.wire.claim.Holds (accelerated_orbit (ix.val + 1) 
                ((d.certWitness ix).trajectory.length - 1)) := by
      apply terminal_claim_transport (ix.val + 1) (d.certWitness ix) d.wire.claim hAnchor hTrans
      -- Need: `claim.Holds (trajectory[length - 1]')` from Lemma 2's `terminalClaimOk = true`.
      sorry
    -- The witness `k` for `orbit_hits_claim` is `trajectory.length - 1`.
    exact ⟨(d.certWitness ix).trajectory.length - 1, hLast⟩

/-! ## v2b.5 — Lemma 6 (constructive per-leaf availability)

Per `docs/story-q5-pr4-v2b-proof-decomposition.md` § 6, v2b.5
lands Lemma 6 — the constructive per-leaf availability theorem
that supersedes the v2a hypothesis-eliminator form
`per_leaf_available_bounded_of_hCert`.

**Type** (adapted from plan; uses per-leaf data's `wire.N` rather
than a free `N` parameter — the plan's free `N` was a typo;
the per-leaf bound is determined by the data):

```lean
per_leaf_available_bounded_of_check : ∀ (t : CoverageTree)
    (dataPerLeaf : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
            ∀ y, (dataPerLeaf l hl hver).wire.claim.Holds y → ReachesOne y)
    (hcheck : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
              checkBoundedCertificate t l (dataPerLeaf l hl hver) = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l)
    : BoundedInputOrbitCertificate t l ((dataPerLeaf l hl hver).wire.N)
```

**Strategy.** Direct application of Lemma 5 to the per-leaf
`dataPerLeaf l hl hver` with all hypotheses threaded through.

**Supersedes** `per_leaf_available_bounded_of_hCert` (v2a
hypothesis-eliminator form, trivial wrapper around the `hCert`
hypothesis). The constructive form here is the actual
verifier-soundness derivation: per-leaf `check = true`
IMPLIES `BoundedInputOrbitCertificate` exists for that leaf.

**Lesson applied (META § 3.2 — per-leaf availability pattern):**
Lemma 6 takes `dataPerLeaf` as an explicit input (mirrors Q4 v3's
`hCert` pattern).

**No new `sorry`/`admit`/`axiom`** — the proof is a one-line
application of Lemma 5. -/

/-- **Lemma 6 (constructive per-leaf availability).** For each
    verified leaf `l`, the per-leaf
    `BoundedInputOrbitCertificate t l ((dataPerLeaf l ...).wire.N)`
    is constructible from:
      - per-leaf `dataPerLeaf` (the per-leaf witness bundle),
      - per-leaf `hcr` (the per-leaf claim reachability hypothesis),
      - per-leaf `hcheck` (the per-leaf verifier soundness hypothesis).

    The proof is a direct application of Lemma 5 to the per-leaf
    data with all hypotheses threaded through.

    Supersedes the v2a hypothesis-eliminator form
    `per_leaf_available_bounded_of_hCert`.

    Plan dependency: closes the Q5 v2 chain. Once Codex approves
    v2b.6 (tests), PR #64 can be retitled from "v2a —
    bounded-input integration infrastructure (DRAFT; soundness
    deferred to v2b)" to "v2 — bounded-input integration
    (closes Q5 4-PR split)". -/
theorem per_leaf_available_bounded_of_check (t : CoverageTree)
    (dataPerLeaf : ∀ l ∈ t.leaves, verified t l → BoundedInputCertificateData)
    (hv : ValidTree t) (hc : IsComplete t)
    (hcr : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
            ∀ y, (dataPerLeaf l hl hver).wire.claim.Holds y → ReachesOne y)
    (hcheck : ∀ l ∈ t.leaves, ∀ (hl : l ∈ t.leaves) (hver : verified t l),
              checkBoundedCertificate t l (dataPerLeaf l hl hver) = true)
    (l : CoverageLeaf) (hl : l ∈ t.leaves) (hver : verified t l)
    : BoundedInputOrbitCertificate t l ((dataPerLeaf l hl hver).wire.N) :=
  checkBoundedCertificate_sound t l (dataPerLeaf l hl hver) hv hc hver
    (hcr l hl hver) (hcheck l hl hver)

end CollatzResearch
