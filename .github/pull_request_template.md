## Story and scope

- **Story / milestone:**
- **Claim level:** hypothesis / observed / checked certificate / formally established / release candidate
- **Does this complete the named story?** yes / no — if no, state the preparation scope:
- **Mathematical objects changed:** maps, domains, invariants, certificates, or ranking functions:

## Acceptance criteria

- [ ] Each criterion from the story is listed below with concrete evidence.
- [ ] This PR does not claim more than its checked evidence supports.
- [ ] Theorem-status and ADR documentation are updated where applicable.

| Criterion | Evidence / theorem / artifact |
|---|---|
|  |  |

## Formalization and trust boundary

- **Lean modules and theorem names changed:**
- **Exact domain and boundary behavior:** include `0`, `1`, positive even, and positive odd cases where relevant.
- **Domain-preservation/invariant lemmas required:**
- **New or changed trusted components:** parser, checker, serialization, axioms, opaque declarations, trusted evaluation, or none.
- **Admitted declarations (`sorry` / `admit`):** count and exact names.
- [ ] No admitted declarations or unapproved axioms occur in release modules.
- [ ] If work is preparatory, title, scope, and `docs/theorem-status.md` label all relevant declarations as pending.

## Validation evidence

Record observed output for the PR head; do not substitute planned commands or a prior commit's CI result.

| Class | Command | Observed result |
|---|---|---|
| Format / lint |  |  |
| Python unit/property tests |  |  |
| Differential tests |  |  |
| Integration / certificate tests |  |  |
| Lean build / targeted proofs |  |  |
| Reproduction / manifest check |  |  |

- **Ubuntu CI run URLs and conclusions:**
- **Pinned toolchains and dependency lock changes:**
- **Seeds, configs, fixture/certificate digests:**

## Reviewer focus

- [ ] Preconditions suffice for every theorem and invoked lemma.
- [ ] Iterated maps preserve their claimed domain/invariants.
- [ ] Python/SMT/generators are treated as untrusted producers.
- [ ] Certificate parsing/versioning/canonicalization fails closed.
- [ ] Tests verify full fixture semantics, not only endpoints.
- [ ] Generated artifacts, caches, and secrets are excluded.

## Independent Codex review gate

- **Reviewed head SHA:**
- **Review round:** 1 / 2 / 3
- **Review state:** awaiting Codex / changes requested / approved / escalated
- **Codex review URL(s):**
- **Blocking findings (P0/P1) and disposition:**

<!--
The reviewed SHA must equal this PR's current head. A push invalidates a prior
approval and starts a new review round. Do not request human merge approval
while this section is awaiting review, has unresolved P0/P1 findings, or is
escalated. See docs/codex-pr-review-gate.md.
-->

## Known limitations and follow-up

- **Known gaps / negative results:**
- **Follow-up story or issue:**
- **Merge recommendation:** complete story / merge only as preparatory work / do not merge
