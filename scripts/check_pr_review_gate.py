#!/usr/bin/env python3
"""Require a posted GitHub review before a reviewed head counts as approved.

The review gate counts a pull request as approved only when the mandated
independent reviewer posted a review on the pull request for the exact head
SHA under review. A durable receipt alone is not evidence: it is invisible to
anyone reading the pull request, and it cannot be checked by a third party.

This script is the mechanical half of that rule. It reads the reviews
attached to a pull request and reports whether one of them is bound to the
expected head, carries the mandated review body, and states the expected
verdict.

Usage:
    python3 scripts/check_pr_review_gate.py \
        --repository OWNER/REPO --pr 125 --head-sha SHA --review-key KEY \
        [--expect-verdict approved] [--model openai/gpt-6.1-terra] \
        [--reviews-json reviews.json]

Exit status is 0 when the gate evidence is present and 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pr_review_evidence import fetch_reviews, verify_posted_review  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--pr", type=int, required=True)
    parser.add_argument("--head-sha", required=True)
    parser.add_argument("--review-key", default="")
    parser.add_argument("--expect-verdict", default="approved")
    parser.add_argument("--model", default="")
    parser.add_argument("--reviews-json", help="read reviews from a file instead of GitHub")
    args = parser.parse_args()

    if args.reviews_json:
        with open(args.reviews_json, encoding="utf-8") as handle:
            reviews = json.load(handle)
        if not isinstance(reviews, list):
            raise ValueError("reviews payload must be a list")
    else:
        reviews = fetch_reviews(args.repository, args.pr)

    accepted, rejected = verify_posted_review(
        reviews,
        args.head_sha,
        args.review_key,
        args.expect_verdict,
        args.model or None,
    )
    result = {
        "ok": bool(accepted),
        "repository": args.repository,
        "pr_number": args.pr,
        "head_sha": args.head_sha,
        "review_key": args.review_key,
        "expected_verdict": args.expect_verdict,
        "accepted": accepted,
        "rejected": rejected,
    }
    print(json.dumps(result, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        raise SystemExit(2) from exc
