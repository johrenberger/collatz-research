#!/usr/bin/env python3
"""
formal-math-extractor: L2/L5 auto-extraction tool.

Scans the formal-math skills library, matches procedure blocks against the
known-pattern catalog, and (on --apply) creates the canonical FAOP skill file
and rewrites the inlined call sites.

Usage:
    python3 extract.py scan
    python3 extract.py apply <PATTERN_ID> [--commit]
    python3 extract.py apply-all-known [--commit]
    python3 extract.py verify-no-drift <PATTERN_ID>
    python3 extract.py --runtime    # also include dispatch_log sequence analysis
"""

import argparse
import difflib
import json
import os
import re
import sqlite3
import sys
from collections import defaultdict
from pathlib import Path

SKILLS_DIR = "/data/.openclaw/skills"
DB_PATH = "/data/.openclaw/state/openclaw.sqlite"

# --------------------------------------------------------------------------------------
# Known-pattern catalog
# --------------------------------------------------------------------------------------

KNOWN_PATTERNS = {
    "GIT_HEAD.v1": {
        "description": "Read branch, HEAD SHA, current status, remotes",
        "required": ["git rev-parse", "git status", "git branch"],
        "min_sites": 2,
        "tolerance_extra": 0,
        "canonical_body": "git status\ngit branch --show-current\ngit rev-parse HEAD\ngit remote -v\n",
    },
    "NARROW_VALIDATE.v1": {
        "description": "Run narrow validation gates (format-check, lint, test)",
        "required": ["make format-check", "make lint", "make test"],
        "min_sites": 2,
        "tolerance_extra": 0,
        "canonical_body": "make format-check\nmake lint\nmake test\n",
    },
    "FULL_VALIDATE.v1": {
        "description": "Run full validation gates (format-check, lint, test, lean, cert-test, ci)",
        "required": ["make format-check", "make lint", "make test", "make lean", "make cert-test", "make ci"],
        "min_sites": 1,
        "tolerance_extra": 0,
        "canonical_body": "make format-check\nmake lint\nmake test\nmake lean\nmake cert-test\nmake ci\n",
    },
}


# --------------------------------------------------------------------------------------
# Block extraction
# --------------------------------------------------------------------------------------

CODE_BLOCK_RE = re.compile(r'```(?:bash|text|sh)?\n(.*?)\n```', re.DOTALL)
SECTION_RE = re.compile(
    r'## (?:Required|Capture) (?:Commands|Steps|Sections?)\s*\n(.*?)(?=\n## |\n---|\Z)',
    re.DOTALL,
)


def extract_procedure_blocks(content):
    """Return a list of (source_type, text, start_offset) for every procedure block."""
    blocks = []
    for match in CODE_BLOCK_RE.finditer(content):
        text = match.group(1).strip()
        if text:
            blocks.append(("code_block", text, match.start()))
    for match in SECTION_RE.finditer(content):
        text = match.group(1).strip()
        if text:
            blocks.append(("section", text, match.start()))
    return blocks


def normalize_lines(text):
    """Lowercase, strip, deduplicate, sort. Robust to permutation and comment noise."""
    out = []
    for line in text.split("\n"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        # Strip trailing semicolons and backticks
        line = line.rstrip(";").rstrip("`").strip()
        if line:
            out.append(line.lower())
    return tuple(sorted(set(out)))


# --------------------------------------------------------------------------------------
# Scanning
# --------------------------------------------------------------------------------------

def scan_skills(skills_dir=SKILLS_DIR, skill_glob="formal-math-*"):

    results = []
    for skill_dir in sorted(Path(skills_dir).glob(skill_glob)):
        skill_path = skill_dir / "SKILL.md"
        if not skill_path.exists():
            continue
        skill_name = skill_dir.name
        try:
            content = skill_path.read_text()
        except Exception as e:
            print(f"warn: could not read {skill_path}: {e}", file=sys.stderr)
            continue
        for source_type, text, offset in extract_procedure_blocks(content):
            fp = normalize_lines(text)
            if not fp:
                continue
            results.append(
                {
                    "skill": skill_name,
                    "skill_path": str(skill_path),
                    "source_type": source_type,
                    "offset": offset,
                    "block": text,
                    "fingerprint": fp,
                    "line_count": len(fp),
                }
            )
    return results


def jaccard(s1, s2):
    set1, set2 = set(s1), set(s2)
    if not set1 and not set2:
        return 1.0
    return len(set1 & set2) / len(set1 | set2)


def find_drift(scan_results, threshold=0.6):
    drift = []
    for i, a in enumerate(scan_results):
        for b in scan_results[i + 1 :]:
            if a["skill"] == b["skill"]:
                continue
            sim = jaccard(a["fingerprint"], b["fingerprint"])
            if threshold <= sim < 1.0:
                drift.append({"a": a, "b": b, "similarity": sim})
    return sorted(drift, key=lambda x: -x["similarity"])


def match_known_patterns(scan_results):
    """Match procedure blocks against known canonical patterns.

    Strictness rules to avoid prose false positives:
    - the site MUST be a `code_block` (not a section); section-level matches are
      skipped because they catch narrative text as well as commands
    - the site's lines MUST be a subset of the canonical's lines plus at most
      `tolerance_extra` extra lines (catches full-gate vs narrow-gate drift);
      a site with too many extras is a *different* procedure, not the canonical
    """
    matched = defaultdict(list)
    for r in scan_results:
        if r["source_type"] != "code_block":
            continue
        block_lines = set(l.strip().lower() for l in r["block"].split("\n") if l.strip())
        for pattern_id, spec in KNOWN_PATTERNS.items():
            canonical_lines = set(
                l.strip().lower() for l in spec["canonical_body"].split("\n") if l.strip()
            )
            required = set(req.lower() for req in spec["required"])
            # All required commands must be present
            if not required.issubset(block_lines):
                continue
            # Tolerance: site may add up to N extras beyond the canonical set.
            # NARROW_VALIDATE.v1 must NOT swallow the FULL_VALIDATE form
            # (which has make lean, make cert-test, make ci on top).
            tolerance = spec.get("tolerance_extra", 0)
            extras = block_lines - canonical_lines
            # Remove required from extras before counting
            extras -= required
            if len(extras) > tolerance:
                continue
            matched[pattern_id].append(r)
    return dict(matched)


def classify_pattern_sites(pattern_id, sites):
    """Separate catalog definitions from inlined sites and actionable work."""
    canonical_skill = f"formal-math-extracted-{slugify(pattern_id)}"
    inlined = [s for s in sites if s["skill"] != canonical_skill]
    spec = KNOWN_PATTERNS[pattern_id]
    skills = {s["skill"] for s in inlined}
    return {
        "discovered": sites,
        "canonical_definitions": [s for s in sites if s["skill"] == canonical_skill],
        "inlined": inlined,
        "actionable": inlined if len(skills) >= spec["min_sites"] else [],
    }


def find_runtime_patterns(db_path=DB_PATH):
    """Group dispatch_log rows by parent_state and extract primitive sequences."""
    if not os.path.exists(db_path):
        return {}
    try:
        con = sqlite3.connect(db_path)
        cur = con.cursor()
        rows = cur.execute(
            """
            SELECT story_id, parent_state, primitive, started_at
            FROM dispatch_log
            WHERE parent_state IS NOT NULL
            ORDER BY story_id, started_at
            """
        ).fetchall()
    except sqlite3.OperationalError:
        return {}

    by_story_state = defaultdict(list)
    for story_id, parent_state, primitive, started_at in rows:
        by_story_state[(story_id, parent_state)].append(primitive)

    pattern_count = defaultdict(int)
    for (story_id, parent_state), primitives in by_story_state.items():
        # Use 2-grams as a coarse pattern
        for i in range(len(primitives) - 1):
            pattern = (primitives[i], primitives[i + 1])
            pattern_count[pattern] += 1

    return {
        "by_2gram": [
            {"pattern": list(k), "occurrences": v}
            for k, v in sorted(pattern_count.items(), key=lambda x: -x[1])
            if v >= 2
        ][:20]
    }


# --------------------------------------------------------------------------------------
# Report
# --------------------------------------------------------------------------------------

def print_scan_report(scan_results, known_matches, drift, runtime=None):
    print("=" * 70)
    print("L2/L5 Auto-Extraction Report")
    print("=" * 70)
    print()
    skill_count = len(set(r["skill"] for r in scan_results))
    print(f"Scanned {skill_count} skills, found {len(scan_results)} procedure blocks.")
    print()

    print("--- Known-Pattern Matches ---")
    if not known_matches:
        print("  (no known-pattern matches in the strict code-block sense)")
    for pattern_id, sites in sorted(known_matches.items()):
        classified = classify_pattern_sites(pattern_id, sites)
        inlined = classified["inlined"]
        skills = sorted(set(s["skill"] for s in inlined))
        spec = KNOWN_PATTERNS[pattern_id]
        status = "READY" if classified["actionable"] else "BELOW-MIN"
        print(
            f"  {pattern_id}  [{status}]  discovered={len(sites)}, "
            f"canonical_definitions={len(classified['canonical_definitions'])}, "
            f"inlined={len(inlined)} across {len(skills)} skill(s): {', '.join(skills) or '(none)'}"
        )
        for s in sites:
            print(f"      - {s['skill']} (offset={s['offset']}, lines={s['line_count']}, type={s['source_type']})")
    print()

    # Aspirational patterns: in the catalog but with no genuine sites today
    aspirational = [pid for pid in KNOWN_PATTERNS
                    if not classify_pattern_sites(pid, known_matches.get(pid, []))["inlined"]]
    if aspirational:
        print("--- Catalog Patterns Without Inlined Sites (informational only) ---")
        for pid in aspirational:
            spec = KNOWN_PATTERNS[pid]
            canonical = classify_pattern_sites(pid, known_matches.get(pid, []))["canonical_definitions"]
            state = "canonical definition exists; no inlined call sites" if canonical else "catalog target; no inlined call sites"
            print(f"  {pid}  {spec['description']}.  {state}.")
        print()

    print("--- Drift Groups (near-identical, similarity 0.6-1.0) ---")
    if not drift:
        print("  (no drift detected)")
    else:
        for d in drift[:15]:
            a, b = d["a"], d["b"]
            print(
                f"  sim={d['similarity']:.2f}  {a['skill']} <-> {b['skill']}"
            )
            print(f"      A: {a['fingerprint']}")
            print(f"      B: {b['fingerprint']}")
    print()

    if runtime:
        print("--- Runtime 2-gram Patterns (dispatch_log, occurrences >= 2) ---")
        if not runtime.get("by_2gram"):
            print("  (no runtime patterns yet)")
        else:
            for p in runtime["by_2gram"]:
                print(f"  {p['pattern']}  x{p['occurrences']}")
        print()

    print("--- Apply Recommendations ---")
    any_recommendation = False
    for pattern_id, sites in sorted(known_matches.items()):
        classified = classify_pattern_sites(pattern_id, sites)
        if classified["actionable"]:
            print(
                f"  python3 extract.py apply {pattern_id}        # "
                f"{len(classified['actionable'])} inlined site(s) ready"
            )
            any_recommendation = True
    if not any_recommendation:
        print("  (no patterns ready to apply)")


# --------------------------------------------------------------------------------------
# Apply
# --------------------------------------------------------------------------------------

CANONICAL_TEMPLATE = """---
name: formal-math-extracted-{slug}
description: "Canonical FAOP extracted via L2/L5 from the formal-math skills library. Replaces inlined reconstructions at the call sites listed in `formal-math-extractor`'s catalog."
---

# Formal Math Engineering — Extracted `{id}`

> L2/L5 auto-extracted by `formal-math-extractor`. The procedure below is the single canonical form. All inlined reconstructions at the listed call sites have been replaced with `call({id})`.

## Procedure

```bash
{body}
```

## Inputs / Outputs

```yaml
inputs:
  - (declared by the call site; this FAOP is reusable)
outputs:
  - (declared by the call site)
```

## Effect Label

`deterministic` (default — override per call site if needed).

## c_max

```yaml
c_max:
  tokens: 0
  wallclock_seconds: 60
```

## Call Sites (rewritten)

The following skills previously inlined this procedure; they now reference `{id}`:

{call_sites}
"""


def slugify(pattern_id):
    return pattern_id.lower().replace(".", "-")


def apply_pattern(pattern_id, scan_results, known_matches, commit=False, skills_dir=SKILLS_DIR):
    if pattern_id not in KNOWN_PATTERNS:
        print(f"FAIL: unknown pattern '{pattern_id}'", file=sys.stderr)
        return False
    spec = KNOWN_PATTERNS[pattern_id]
    classified = classify_pattern_sites(pattern_id, known_matches.get(pattern_id, []))
    sites = classified["actionable"]
    skills = sorted(set(s["skill"] for s in sites))
    if len(skills) < spec["min_sites"]:
        print(
            f"REFUSED: {pattern_id} has {len(skills)} site(s); need >= {spec['min_sites']}",
            file=sys.stderr,
        )
        return False

    slug = slugify(pattern_id)
    target_dir = Path(skills_dir) / f"formal-math-extracted-{slug}"
    target_file = target_dir / "SKILL.md"

    call_site_listing = "\n".join(f"- `{s['skill']}`" for s in sites)
    canonical_body = CANONICAL_TEMPLATE.format(
        id=pattern_id,
        slug=slug,
        body=spec["canonical_body"],
        call_sites=call_site_listing,
    )

    print(f"[apply] pattern: {pattern_id}")
    print(f"[apply] sites:   {len(sites)} across {len(skills)} skills")
    print(f"[apply] target:  {target_file}")
    print()

    # Preflight every site before creating or changing any file. Re-location is
    # content-based as well as offset-based so stale/ambiguous scans fail closed.
    spans_by_path = defaultdict(list)
    for site in sites:
        skill_path = Path(site["skill_path"])
        try:
            content = skill_path.read_text()
        except OSError as e:
            print(f"REFUSED: cannot read {skill_path}: {e}", file=sys.stderr)
            return False
        blocks = extract_procedure_blocks(content)
        matches = [(t, txt, off) for t, txt, off in blocks
                   if t == site["source_type"] and off == site["offset"]
                   and normalize_lines(txt) == site["fingerprint"]]
        if len(matches) != 1 or site["source_type"] != "code_block":
            print(f"REFUSED: stale or ambiguous site {skill_path} at offset {site['offset']}", file=sys.stderr)
            return False
        _, _, offset = matches[0]
        start = offset
        if not content.startswith("```", start) or content.find("\n```", start) < 0:
            print(f"REFUSED: malformed code fence in {skill_path} at offset {offset}", file=sys.stderr)
            return False
        end = content.find("\n```", start) + len("\n```")
        replacement = (f"```bash\n# Canonical: {pattern_id} — see formal-math-extracted-{slug}\n"
                       f"call({pattern_id})\n```")
        spans_by_path[skill_path].append((start, end, replacement))

    rewrites = {}
    for path, spans in spans_by_path.items():
        if len({(start, end) for start, end, _ in spans}) != len(spans):
            print(f"REFUSED: duplicate/overlapping candidate sites in {path}", file=sys.stderr)
            return False
        content = path.read_text()
        for start, end, replacement in sorted(spans, reverse=True):
            content = content[:start] + replacement + content[end:]
        rewrites[path] = content

    if target_file.exists():
        print(f"REFUSED: canonical target already exists: {target_file}", file=sys.stderr)
        return False
    originals_text = {path: path.read_text() for path in rewrites}
    if not commit:
        print("DRY-RUN: no files written. Preflight succeeded; proposed diff follows. Pass --commit to write.")
        print("".join(difflib.unified_diff([], canonical_body.splitlines(keepends=True),
                                           fromfile="/dev/null", tofile=str(target_file))), end="")
        for path, updated in sorted(rewrites.items()):
            original = originals_text[path]
            print("".join(difflib.unified_diff(original.splitlines(keepends=True),
                                               updated.splitlines(keepends=True),
                                               fromfile=str(path), tofile=str(path) + " (rewritten)")), end="")
        return True

    # Stage all bytes before replacing targets; on any write failure, restore
    # the original files and remove a newly-created canonical directory.
    originals = {path: path.read_bytes() for path in rewrites}
    created = []
    try:
        target_dir.mkdir(parents=True, exist_ok=False)
        created.append(target_dir)
        target_file.write_text(canonical_body)
        for path, updated in sorted(rewrites.items()):
            path.write_text(updated)
            print(f"  rewrote {path}")
    except OSError as e:
        for path, original in originals.items():
            path.write_bytes(original)
        for path in created:
            if path.exists():
                for child in path.iterdir():
                    child.unlink()
                path.rmdir()
        print(f"REFUSED: apply failed and staged files were restored: {e}", file=sys.stderr)
        return False

    print()
    print("[apply] done. Re-run 'verify-no-drift' to confirm.")
    return True


# --------------------------------------------------------------------------------------
# Verify no drift
# --------------------------------------------------------------------------------------

def verify_no_drift(pattern_id, scan_results):
    spec = KNOWN_PATTERNS.get(pattern_id)
    if not spec:
        print(f"FAIL: unknown pattern '{pattern_id}'", file=sys.stderr)
        return False
    # An "inlined reconstruction" is a code-block site (NOT a section) that
    # still matches the pattern's required commands AND is not preceded by a
    # `# Canonical: <pattern_id>` comment. The canonical skill itself is
    # excluded by the rewrite marker; section-level matches are excluded
    # because they catch narrative text.
    remaining = []
    for r in scan_results:
        if r["source_type"] != "code_block":
            continue
        # Exempt the canonical skill itself (it must contain the procedure)
        if r["skill"].startswith("formal-math-extracted-"):
            continue
        if f"# canonical: {pattern_id.lower()}" in r["block"].lower():
            continue
        # Same strict matching as the matcher
        block_lines = set(l.strip().lower() for l in r["block"].split("\n") if l.strip())
        required = set(req.lower() for req in spec["required"])
        if not required.issubset(block_lines):
            continue
        canonical_lines = set(
            l.strip().lower() for l in spec["canonical_body"].split("\n") if l.strip()
        )
        tolerance = spec.get("tolerance_extra", 0)
        extras = block_lines - canonical_lines - required
        if len(extras) > tolerance:
            continue
        remaining.append(r)
    if remaining:
        print(f"FAIL: inlined reconstructions of {pattern_id} remain:")
        for r in remaining:
            print(f"  - {r['skill']} (offset {r['offset']}, source_type={r['source_type']})")
        return False
    print(f"OK: no inlined reconstructions of {pattern_id} remain.")
    return True


# --------------------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="L2/L5 auto-extraction tool")
    parser.add_argument("command", choices=["scan", "apply", "apply-all-known", "verify-no-drift"])
    parser.add_argument("pattern", nargs="?")
    parser.add_argument("--commit", action="store_true", help="Actually write files (default: dry-run)")
    parser.add_argument("--runtime", action="store_true", help="Include dispatch_log runtime analysis")
    args = parser.parse_args()

    scan_results = scan_skills()
    known_matches = match_known_patterns(scan_results)
    drift = find_drift(scan_results)
    runtime = find_runtime_patterns() if args.runtime else None

    if args.command == "scan":
        print_scan_report(scan_results, known_matches, drift, runtime)
        return 0

    if args.command in ("apply", "apply-all-known"):
        if args.command == "apply":
            if not args.pattern:
                print("FAIL: apply requires a pattern id", file=sys.stderr)
                return 2
            ok = apply_pattern(args.pattern, scan_results, known_matches, commit=args.commit)
            return 0 if ok else 1
        # apply-all-known
        any_applied = False
        for pattern_id in sorted(known_matches.keys()):
            ok = apply_pattern(pattern_id, scan_results, known_matches, commit=args.commit)
            any_applied = any_applied or ok
        if not any_applied:
            print("No patterns ready to apply.")
        return 0

    if args.command == "verify-no-drift":
        if not args.pattern:
            print("FAIL: verify-no-drift requires a pattern id", file=sys.stderr)
            return 2
        ok = verify_no_drift(args.pattern, scan_results)
        return 0 if ok else 1

    return 2


if __name__ == "__main__":
    sys.exit(main())
