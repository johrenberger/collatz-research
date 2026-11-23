---
name: formal-math-extractor
description: "L2/L5 auto-extraction. Scans the formal-math skills library for repeated sub-sequences, matches against known canonical patterns, and (on --apply) creates the canonical FAOP file and rewrites the call sites. The Stage 5 tool that makes REVIEW_ROUND.v1, GIT_HEAD.v1, NARROW_VALIDATE.v1, and CHECKPOINT_AND_LOG.v1 repeatable rather than hand-coded."
---

# Formal Math Engineering — Extractor (L2/L5 auto-extraction)

> Companion skill owning the extraction tool. Implements FAOP Laws L2 (sub-workflow extraction) and L5 (canonical reuse) as a runnable analyzer + applier, not as hand-written extractions.

This is the tool that turns the L2/L5 hooks in `formal-math-optimizer` from "we'll get to it" into "the tool found three candidates and applied one." The Stage 4 +O targets table in the controller promised `GIT_HEAD.v1`, `NARROW_VALIDATE.v1`, and `CHECKPOINT_AND_LOG.v1`. This skill makes those promises executable.

## What the Tool Does

```text
formal-math-extractor scan
   -> reads all /data/.openclaw/skills/formal-math-*/SKILL.md
   -> extracts procedure blocks (bash code blocks, "Required Commands" sections, "Capture Steps" sections)
   -> fingerprints each block
   -> matches against the known pattern catalog
   -> groups identical fingerprints across skills
   -> clusters near-identical fingerprints as drift candidates
   -> prints a structured report

formal-math-extractor apply <PATTERN_ID>
   -> creates the canonical FAOP skill file at /data/.openclaw/skills/formal-math-extracted-<id>/SKILL.md
   -> rewrites each call site to reference the canonical
   -> verifies the result by re-running scan

formal-math-extractor apply-all-known
   -> applies every pattern in the catalog that has 2+ matching sites
   -> dry-run by default; pass --commit to write

formal-math-extractor verify-no-drift <PATTERN_ID>
   -> after apply, asserts no inlined reconstruction of the pattern remains
```

The scan report distinguishes discovered blocks, canonical definitions, inlined matches, and actionable candidates. A canonical definition is informational and is never an inlined call site or an apply recommendation. `apply` reports a unified proposed diff in dry-run mode and validates every site before any write; stale, ambiguous, or unsupported sites refuse the whole operation. Fixture tests live beside the tool. Do not run `apply --commit` against installed/shared skills as part of S1; use temporary fixture trees for commit-path tests.

## The Known-Pattern Catalog (built-in)

The tool ships with patterns the user has already named in the Stage 4 +O targets table:

| Pattern ID | Description | Required commands |
|---|---|---|
| `GIT_HEAD.v1` | Read branch, HEAD SHA, current status, remotes | `git rev-parse`, `git status`, `git branch` |
| `NARROW_VALIDATE.v1` | Run narrow validation gates (format-check, lint, test) | `make format-check`, `make lint`, `make test` |
| `CHECKPOINT_AND_LOG.v1` | Append to dispatch_log and update working_state | (logic, not bash) |
| `REVIEW_ROUND.v1` | Open PR + fetch context + dispatch review | (already extracted in `formal-math-pr-review`) |

A new pattern is added by appending a row to the catalog. Patterns are matched on **required-command presence** (all required commands must appear in the block) and **minimum site count** (default 2).

## Static-Analysis Algorithm

### 1. Block extraction

```python
def extract_procedure_blocks(content):
    blocks = []
    # (a) bash / text / sh code blocks
    for match in re.finditer(r'```(?:bash|text|sh)?\n(.*?)\n```', content, re.DOTALL):
        blocks.append(('code_block', match.group(1).strip()))
    # (b) "Required Commands" / "Required Steps" / "Capture Steps" sections
    for match in re.finditer(
        r'## (?:Required|Capture) (?:Commands|Steps|Sections?)\s*\n(.*?)(?=\n## |\n---|\Z)',
        content, re.DOTALL,
    ):
        blocks.append(('section', match.group(1).strip()))
    return blocks
```

### 2. Fingerprinting

```python
def normalize_lines(text):
    out = []
    for line in text.split('\n'):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        out.append(line.rstrip(';').lower())
    return tuple(sorted(set(out)))   # set() for permutation-robust matching
```

The fingerprint is an **order-independent, deduplicated, lowercased** tuple of lines. Two blocks with the same commands in different order get the same fingerprint — that is exactly the drift L5 detects.

### 3. Identical-repetition detection

```python
fp_to_sites = defaultdict(list)
for site in scan_results:
    fp_to_sites[site['fingerprint']].append(site)

candidates = [
    {'fingerprint': fp, 'sites': sites, 'skill_count': len(set(s['skill'] for s in sites))}
    for fp, sites in fp_to_sites.items()
    if len(set(s['skill'] for s in sites)) >= 2
]
```

### 4. Drift detection (near-miss)

Jaccard similarity over the line sets:

```python
def jaccard(s1, s2):
    set1, set2 = set(s1), set(s2)
    if not set1 and not set2:
        return 1.0
    return len(set1 & set2) / len(set1 | set2)

drift = [
    {'a': site_a, 'b': site_b, 'similarity': jaccard(a.fp, b.fp)}
    for a, b in pairs(scan_results, different_skills=True)
    if 0.6 <= jaccard(a.fp, b.fp) < 1.0
]
```

Drift is **reported, not auto-applied**. A human decides whether to canonicalize the drift or accept the variation.

### 5. Pattern matching

```python
KNOWN_PATTERNS = {
    "GIT_HEAD.v1": {
        "description": "Read branch, HEAD SHA, current status, remotes",
        "required": ["git rev-parse", "git status", "git branch"],
        "min_sites": 2,
    },
    "NARROW_VALIDATE.v1": {
        "description": "Run narrow validation gates (format-check, lint, test)",
        "required": ["make format-check", "make lint", "make test"],
        "min_sites": 2,
    },
}

for pattern_id, spec in KNOWN_PATTERNS.items():
    for site in scan_results:
        if all(req in site['block'].lower() for req in spec['required']):
            site['matched_patterns'].append(pattern_id)
```

## Apply Algorithm

For a known pattern, the apply step:

```text
1. create the canonical FAOP file
   -> /data/.openclaw/skills/formal-math-extracted-<id>/SKILL.md
   -> contains the canonical procedure block + a `## How to call` section
2. for each call site:
   a. locate the inlined block in the source skill (offset from scan)
   b. replace the bash block with a one-line reference:
        # Canonical: <id> — see formal-math-extracted-<id>
        call(<id>)
   c. write the modified file back
3. re-run scan; assert that <id> still matches and that the inlined reconstruction count is now 0
```

The rewrite is **idempotent**: re-running apply on a pattern whose sites are already rewritten is a no-op (the inlined block is no longer present to match).

## Drift Policy (L2)

When two sites have similar but not identical fingerprints, the tool reports the drift. The human-facing output is:

```yaml
drift:
  - similarity: 0.80
    a: { skill: formal-math-discovery, lines: ["git rev-parse head", "git status", "git branch --show-current"] }
    b: { skill: formal-math-baseline, lines: ["git rev-parse head", "git status", "git branch --show-current", "git remote -v"] }
    recommended_canonical: GIT_HEAD.v1    # if the variation is "one site has an extra line"
```

The human can then either:

- accept the drift (some sites legitimately need the extra command)
- canonicalize the drift by extending the known pattern's required set
- split into two patterns (e.g., `GIT_HEAD_REMOTE.v1` for the site that needs `git remote -v`)

## Runtime-Trace Analysis (optional)

If `--runtime` is passed, the tool also queries `dispatch_log` and groups `primitive` sequences by `parent_state`. Sequences that appear in 2+ stories are flagged. This catches patterns that exist in *behavior* but aren't written as bash blocks in the skills.

Currently the runtime data is sparse (this is a fresh install) so static analysis is the primary mode.

## The Refusal Path

If the tool cannot find 2+ sites for a known pattern, `apply` is refused with:

```yaml
refused:
  pattern: GIT_HEAD.v1
  reason: "insufficient_sites"
  found: 1
  required_min: 2
  sites:
    - skill: formal-math-discovery
```

This prevents the tool from creating a "canonical" form for a pattern that has only one use site — the L2 law says "registered FAOP for every selected s where s occurs at least twice" (per FAOP Definition 5).

## What This Skill Does Not Do (Stage 6+ scope)

- **No automatic SPECIFICATION_DEFECT detection.** A drift that turns out to be a real semantic difference is a SPECIFICATION_DEFECT, not an L2 extraction candidate. The tool reports drift; a human classifies it.
- **No SkillBase-style auto-registration with type signatures.** The extracted FAOPs are registered as plain skills; their input/output schemas are documented but not type-checked at compile time.
- **No semantic equivalence proof.** The tool proves *syntactic* identity; the human is responsible for proving *semantic* equivalence when the rewrite happens.

## Transition

This skill does not itself transition states. It is invoked by the operator (or by a future automated `stage5-tick` automation) when extractions are desired.

## Co-Signed Invariant (controller invariant #21)

> **#21 No new inlined reconstruction of a canonical FAOP (declared in `formal-math-extractor`'s pattern catalog) is committed. The tool's `verify_no_drift` MUST pass before any `STORY_COMPLETE` for a story that touched the canonical's domain. A story that fails the check routes to `HUMAN_GATE` for human classification of the drift.**
