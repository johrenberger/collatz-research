# Lessons Learned — NT-5 reachability evidence tier (PRs #105 → #107 → #108 → #109 → #110)

**Status:** Arc in progress. Decision 1 (the evidence tier) taken in ADR 0009
(PR #107) and recorded in PR #108 (WP-CF-2). Decision briefs for decisions 2–4
landed in PR #109. The terminal-value-1 reachability instance (WP-CF-1) is in
PR #110. Decisions 2, 3 and 4 remain open maintainer calls.

**Scope:** 5 PRs, 2026-11-05 → 2026-11-07. One arc: one decision recorded,
two work packets executed, three decisions briefed.

**Outcome:**
- ✅ Decision 1 recorded: the reachability evidence tier is kernel-checkable,
  restricted to claims whose terminal value is 1; no reachability theorem
  evaluates an orbit equation; `native_decide` stays data-side only.
- ✅ WP-CF-2: the tier is now recorded in `docs/trust-model.md` and in every
  module docstring that relies on it, with a claim-shape regression.
- ✅ WP-CF-1: the tier's first kernel-checked consequence — an accepted
  witness with a terminal-value-1 claim yields `ReachesOne x` with no
  reachability hypothesis and no `native_decide`.
- ⏸ Decisions 2–4: briefed with evidence, options, and a recommendation each.
  **Not decided** — they are architectural or mathematical choices reserved to
  the maintainer.

---

## 1. Arc overview

### PR #105 — the convergence frontier (merged `515a8d5`)

Docs-only. Defines the frontier: where the proof effort actually stands, what
is missing (a verifier soundness theorem), and the four maintainer decisions
that gate the remaining work. Separates routing (kernel-checked) from
reachability (assumed) and shows what evidence tier would make reachability
closable at all.

### PR #107 — ADR 0009, decision 1 (merged `cd08863`)

The substantive decision. The tier question was forced by a measurement, not
a preference: an orbit equation at `k >= 1` is not kernel-reducible
(`rfl` fails, `decide` gets stuck, only `native_decide` closes it), while
the terminal-is-1 case IS kernel-checkable. The record resolves the question by
restricting the claim shape, not by weakening the checker.

### PR #108 — WP-CF-2, recording the tier (merged `5d2e938`)

Executes the decision: the tier in the trust model and in the module
docstrings that depend on it, plus `ReachabilityEvidenceTierTests.lean`
covering `.empty`, `.singleton 1`, `.singleton n` for `n != 1`,
`.bounded K`, and `.interval` excluded by construction. Four review rounds
(see §3.1).

### PR #109 — decision briefs for decisions 2–4 (open)

`docs/nt5-open-decision-briefs.md`: evidence, options, and a recommendation
per decision, deciding nothing. Three review rounds.

### PR #110 — WP-CF-1, the terminal-value-1 instance (open, draft)

`checkCertWitness_terminal_value_one_reaches_one` and its canonical
instance `checkCertWitness_singleton_one_reaches_one`. Makes the tier
consequential: until this, the tier was recorded but no theorem exercised it.

---

## 2. Architectural decisions

### The tier is a property of the CLAIM SHAPE, not of the checker

The decision that made the work tractable was recognising that the terminal
value `1` and the source's orbit equation are **different facts at
different indices**:

- The **source's** orbit equality `accelerated_orbit x k = 1` is established
  at the witness index the certificate supplies (`k = length - 1`) by
  rewriting, never by evaluating the orbit.
- The **claimed terminal value** `1` has its own zero-step reachability
  witness, `ReachesOne 1` at `k := 0`.

Conflating them is the single most expensive mistake of the arc (§3.2). It
was caught by an independent reviewer, not by the implementer.

### Restrict the shape rather than weaken the checker

The rejected alternative was to accept `native_decide` for the orbit equation
and say so in the trust model. That moves a reachability conclusion off the
kernel, contradicting the boundary this repository has held since ADR 0003.
The chosen alternative — restrict claims to terminal value 1 — narrows what
may be claimed while leaving the checker untouched.

### No conclusion without a witness

WP-CF-1's real content is not the new theorem; it is that the theorem has
**no reachability hypothesis**. The claim obligation
(`claim.Holds y → ReachesOne y`) is discharged by construction for the
terminal-value-1 shape rather than assumed. A companion theorem with that
hypothesis would have been nearly the same proof and would have added
nothing.

---

## 3. New patterns

### 3.1 Review rounds are cheap; the expensive thing is the wrong claim

PR #108 took four rounds and PR #109 took three, and every round but the last
was a documentation-accuracy finding, not a proof failure. What made them
cheap was that each round targeted one question with the previous round's
finding quoted verbatim.

What was NOT cheap: the first round's P1 was a semantic error in the tier
statement, and it had to be corrected in four files at once (the module
docstring plus three per-declaration docstrings). A semantic error in a
statement that is then copied N times costs N times more than it would in one
place.

**Reusable:** when a statement will be repeated, get it right once and state
it once, with pointers to the canonical location, rather than restating it
N times and hoping the copies agree.

### 3.2 Distinguish the witness at the source from the witness at the claim

The P1 that cost PR #108 a round: the tier docstrings conflated the source's
orbit witness (at the certificate's index) with the terminal value's own
zero-step witness, so they claimed the source's orbit equation was "closed at
`k := 0`".

Both facts are true; the sentence made them one fact. This is easy to miss
because `accelerated_orbit_zero 1` genuinely does close `ReachesOne 1` at
`k := 0`.

**Reusable:** in any certificate-to-orbit pipeline, name the index and the
subject for each witness. "The witness" is ambiguous; "`k = 6`, the
source's orbit equality" is not.

### 3.3 Source-line citations are fragile under docstring edits

Rounds 2 and 3 of PR #108 were both stale-citation findings. Adding docstring
lines to a Lean module shifts every declaration below it, which silently
invalidates every `file:line` citation to those declarations — including
citations in the ADR that the docstrings themselves implement.

Round 2 fixed nine citations; round 3 found a tenth, because the fix was
applied by hand to the citations that had been listed rather than to all
citations in the file.

**Reusable:** after any change that adds or removes lines above a cited
declaration, re-verify every citation in the file mechanically — extract the
cited line and print it, then compare — instead of fixing the ones a reviewer
happened to name.

### 3.4 A decision brief is the right deliverable for an open maintainer decision

Decisions 2–4 could not be decided autonomously: per the repository's own
review-gate rules, an architecture or mathematical choice is a maintainer
decision, and `docs/convergence-frontier.md` § 9 states that a work packet
depending on an open decision must not begin.

So the deliverable was a brief, not an implementation: the question, the
evidence (each claim with how it was checked), the options with what each
commits the repository to, and a recommendation. It is explicitly labelled a
brief and decides nothing, and the reviewer confirmed the brief stays a brief.

**Reusable:** when a decision is reserved to the maintainer, the useful
artifact is a decision-ready brief, and the brief's own review checklist is
"does this decide anything it should not?"

### 3.5 Verify a load-bearing inherited claim before building on it

The frontier document asserted that `coverage_tree_soundness_orbit`'s
documented promotion path is refutable (§ 7.1). That claim decided the
recommendation for decision 2, and it had never been compiled — it was an
argument, not a check.

It was re-derived as a standalone probe outside the repository working tree
(one-leaf tree with an unparseable `leafProperty`: `verified`,
`ValidTree` and `IsComplete` all hold, `OrbitAlignedTree` fails), and the
probe is reproduced in the brief so a reader can re-run it.

**Reusable:** a claim inherited from a planning document and used to justify a
recommendation deserves a compile check of its own.

### 3.6 Qualify a claim to the shape that carries it

The P1 on PR #109: the brief asserted that a `.interval` claim carries an
infinite reachability obligation. The raw constructor permits malformed
intervals (`.interval 0 0 0`, `.interval 2 2 1`) that denote finite or
empty sets. The infinite obligation is true of the intervals a
`LeafCertificate` can carry, because its `well_formed` field requires
`LeafClaim.WellFormed`.

**Reusable:** a claim about "a constructor" is a claim about every value of
that constructor, including malformed ones. State the qualifier — "a
well-formed `.interval` carried by a `LeafCertificate`" — and the claim is
true and survives review.

### 3.7 The proof composes existing machinery; the new part is one bridge

WP-CF-1 needed no new lemma beyond one index bridge. The chain
`checkCertWitness_decompose` → `transitionOk_implies_step_forall` →
`terminal_claim_transport` → `orbit_predecessor_reaches_one` was already
in the repository; the only genuinely new step was relating `getLast?` to
`getElem! (length - 1)`, and `Q5RoutingPartition.lean:186-194` already
contained that exact bridge.

**Reusable:** before writing a bridge lemma, check whether a sibling module
already proved it. The cost of a new lemma is not the proof; it is the
admission budget, the docstring, and the review surface.

### 3.8 Lean mechanics that cost time here

Concrete, reusable, and each one cost a build cycle:

- `cases ht : w.trajectory with` already substitutes the matched term in
  the goal, so a following `rw [ht]` fails with "did not find an
  occurrence". Use `List.length_pos_iff.mpr hne` for length positivity
  instead of destructuring.
- Rewriting a hypothesis needs the **forward** form:
  `rw [List.getLast?_eq_some_getLast hne] at hl` then
  `Option.some.inj hl`. The backward form does not match.
- The three-step bridge is `getElem!_pos` → `List.getLast_eq_getElem` →
  `getLast?_eq_some_getLast`; `Q5RoutingPartition.lean:186-194` has it
  working.
- `String.split` is opaque to kernel reduction, so a "this string does not
  parse" fact needs `native_decide` — fine for a *string* fact, but it must
  not be used for a reachability conclusion.

### 3.9 Lean CI is the validation gate; the local build is a smoke test

The repository's rule (meta doc, Pattern 2.12) is that GitHub Lean CI is the
sole validation gate, and this arc confirmed why. A full local `lake build`
of the root target exceeds an agent's wall-clock budget; the CI run took
2m31s–3m33s and checked every module plus the admission-budget and
admission-oracle gates.

**Reusable:** build the module you touched locally as a fast smoke test, let
CI adjudicate, and do not describe a local build as validation.

---

## 4. Trust boundary

**Unchanged throughout.** Recorded explicitly in ADR 0009 and repeated in
`docs/trust-model.md`:

- The Lean kernel remains the final checker for every `ReachesOne`
  conclusion.
- A reachability witness is admissible only when the certificate's terminal
  value is 1.
- No reachability theorem evaluates an orbit equation.
- `native_decide` remains admissible for data-side obligations only.

The acceptance hypothesis in WP-CF-1 (`checkCertWitness ... = true`) is a
**data-side** Boolean check. What WP-CF-1 adds is that its reachability
*consequence* is kernel-checked. The two are different claims and the
docstrings keep them apart.

---

## 5. Self-audit

- **No new `sorry`/`admit`/`axiom`/`native_decide`** in the new code.
  The admission budget (`docs/lean-sorry-budget.json`) is unchanged.
- **No row of `docs/theorem-status.md` was promoted.** PR #108 and PR #109
  added no rows at all; PR #110 adds rows for the two NEW declarations it
  introduces, which is what that table's own rule requires.
- **No convergence claim.** Nothing here asserts global convergence, cycle
  exclusion, or reachability beyond a bounded, accepted certificate.
- **Decisions 2–4 were not decided.** The brief records options and a
  recommendation; the decisions remain with the maintainer, and WP-CF-4 and
  WP-CF-5 remain blocked until they are made.
- **The review gate was load-bearing.** Every semantic error found in this
  arc (the witness conflation, the stale citations, the unqualified
  `.interval` claim) was found by the independent reviewer, not by
  self-review. Two of the three would have shipped as plausible-sounding
  documentation errors.

---

## 6. Open threads

- **Decisions 2, 3, 4** await the maintainer. PR #109 carries the briefs.
- **WP-CF-3** (per-leaf availability for one concrete tree) is unblocked by
  decision 1 and is the next packet on the critical path.
- The frontier document's WP-CF-1 wording still says "the kernel-checked
  witness k := 0 (accelerated_orbit_zero 1)", which is the same conflation
  §3.2 corrected in the docstrings. Worth reconciling in a follow-up so the
  plan text and the shipped theorem agree.
