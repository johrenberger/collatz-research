import contextlib
import importlib.util
import io
import tempfile
import unittest
from pathlib import Path

MODULE_PATH = Path(__file__).parents[1] / "extract.py"
SPEC = importlib.util.spec_from_file_location("extract", MODULE_PATH)
extract = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(extract)


NARROW = "make format-check\nmake lint\nmake test"


def site(skill, block=NARROW, offset=0):
    return {
        "skill": skill,
        "skill_path": f"/tmp/{skill}/SKILL.md",
        "source_type": "code_block",
        "offset": offset,
        "block": block,
        "fingerprint": extract.normalize_lines(block),
        "line_count": len(extract.normalize_lines(block)),
    }


class PatternClassificationTests(unittest.TestCase):
    def test_zero_and_one_inlined_sites_are_not_actionable(self):
        self.assertFalse(extract.classify_pattern_sites("NARROW_VALIDATE.v1", [])["actionable"])
        one = extract.classify_pattern_sites("NARROW_VALIDATE.v1", [site("one")])
        self.assertEqual(one["inlined"], [site("one")])
        self.assertFalse(one["actionable"])

    def test_multiple_sites_across_skills_are_actionable(self):
        sites = [site("one"), site("two")]
        classified = extract.classify_pattern_sites("NARROW_VALIDATE.v1", sites)
        self.assertEqual(classified["actionable"], sites)

    def test_existing_full_validate_canonical_is_not_an_inlined_candidate(self):
        canonical_name = "formal-math-extracted-full_validate-v1"
        canonical = site(
            canonical_name, extract.KNOWN_PATTERNS["FULL_VALIDATE.v1"]["canonical_body"]
        )
        classified = extract.classify_pattern_sites("FULL_VALIDATE.v1", [canonical])
        self.assertEqual(classified["canonical_definitions"], [canonical])
        self.assertEqual(classified["inlined"], [])
        self.assertEqual(classified["actionable"], [])

    def test_same_file_duplicate_sites_are_actionable_when_offsets_differ(self):
        a, b = site("same"), site("same", offset=100)
        self.assertEqual(
            extract.classify_pattern_sites("FULL_VALIDATE.v1", [a, b])["actionable"],
            [a, b],
        )


class MatchingTests(unittest.TestCase):
    def test_prose_and_sections_do_not_match(self):
        rows = [
            site(
                "prose", "The commands make format-check, make lint, and make test are recommended."
            )
        ]
        rows[0]["source_type"] = "section"
        self.assertNotIn("NARROW_VALIDATE.v1", extract.match_known_patterns(rows))

    def test_extra_comments_do_not_create_false_positive(self):
        row = site("comment", "# run all checks\n" + NARROW)
        self.assertNotIn("NARROW_VALIDATE.v1", extract.match_known_patterns([row]))

    def test_overlapping_narrow_and_full_patterns_only_matches_full(self):
        full = extract.KNOWN_PATTERNS["FULL_VALIDATE.v1"]["canonical_body"]
        matches = extract.match_known_patterns([site("full", full)])
        self.assertIn("FULL_VALIDATE.v1", matches)
        self.assertNotIn("NARROW_VALIDATE.v1", matches)


class ApplySafetyTests(unittest.TestCase):
    def _fixture(self, blocks):
        temp = tempfile.TemporaryDirectory()
        root = Path(temp.name)
        sites = []
        for name, content in blocks.items():
            folder = root / f"formal-math-{name}"
            folder.mkdir()
            path = folder / "SKILL.md"
            path.write_text(content)
            sites.extend(extract.scan_skills(root, f"formal-math-{name}"))
        return temp, root, sites, extract.match_known_patterns(sites)

    def test_dry_run_is_read_only(self):
        block = "Before\n\n```bash\n" + NARROW + "\n```\nAfter\n"
        temp, root, sites, matches = self._fixture({"one": block, "two": block})
        with temp:
            before = {p: p.read_bytes() for p in root.rglob("*") if p.is_file()}
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertTrue(
                    extract.apply_pattern("NARROW_VALIDATE.v1", sites, matches, skills_dir=root)
                )
            self.assertEqual(before, {p: p.read_bytes() for p in before})
            self.assertFalse((root / "formal-math-extracted-narrow_validate-v1").exists())
            self.assertIn("--- ", output.getvalue())
            self.assertIn("call(NARROW_VALIDATE.v1)", output.getvalue())

    def test_commit_rewrites_all_sites_and_creates_canonical(self):
        block = "Before\n\n```bash\n" + NARROW + "\n```\nAfter\n"
        temp, root, sites, matches = self._fixture({"one": block, "two": block})
        with temp:
            self.assertTrue(
                extract.apply_pattern(
                    "NARROW_VALIDATE.v1", sites, matches, commit=True, skills_dir=root
                )
            )
            for name in ("one", "two"):
                text = (root / f"formal-math-{name}" / "SKILL.md").read_text()
                self.assertIn("call(NARROW_VALIDATE.v1)", text)
                self.assertIn("After", text)
            canonical = root / "formal-math-extracted-narrow_validate-v1" / "SKILL.md"
            self.assertTrue(canonical.exists())

    def test_stale_offset_refuses_before_any_write(self):
        block = "Before\n\n```bash\n" + NARROW + "\n```\nAfter\n"
        temp, root, sites, matches = self._fixture({"one": block, "two": block})
        with temp:
            sites[0]["offset"] += 1
            before = {p: p.read_bytes() for p in root.rglob("*") if p.is_file()}
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertFalse(
                    extract.apply_pattern(
                        "NARROW_VALIDATE.v1", sites, matches, commit=True, skills_dir=root
                    )
                )
            self.assertEqual(before, {p: p.read_bytes() for p in before})
            self.assertFalse((root / "formal-math-extracted-narrow_validate-v1").exists())

    def test_duplicate_sites_in_one_file_are_rewritten(self):
        block = "```bash\n" + NARROW + "\n```"
        content = "First\n" + block + "\nMiddle\n" + block + "\nLast\n"
        temp, root, sites, matches = self._fixture(
            {
                "one": content,
                "two": "Second site\n```bash\n" + NARROW + "\n```\n",
            }
        )
        with temp:
            self.assertTrue(
                extract.apply_pattern(
                    "NARROW_VALIDATE.v1", sites, matches, commit=True, skills_dir=root
                )
            )
            text = (root / "formal-math-one" / "SKILL.md").read_text()
            self.assertEqual(text.count("call(NARROW_VALIDATE.v1)"), 2)


if __name__ == "__main__":
    unittest.main()
