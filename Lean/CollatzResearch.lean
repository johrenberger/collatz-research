import CollatzResearch.Affine
import CollatzResearch.Basic
import CollatzResearch.Certificate
import CollatzResearch.Dynamics
import CollatzResearch.Equivalence
import CollatzResearch.Residues

-- Story: extend default `lake build` coverage to the Q5 + bounded-input
-- infrastructure. These modules were previously only exercised by
-- conditional Lean CI jobs ("when present"); making them root imports
-- ensures `make ci` and `lake build` validate them every run.
--
-- Story #1b (PR #80) attempted to bring the 3 remaining orphans up to
-- Lean 4 v4.33.0 + current Mathlib, but the cascade exceeded the
-- controller's "same strategy × 2 failed → BLOCK" budget (RCS >> 12)
-- and was formally escalated. See
-- `.openclaw/diagnostics/story-q5-root-import-coverage/escalation-001.md`
-- for the full diagnostic. **Story #1c** is the follow-up rewrite work
-- packet (partial rewrite of `BoundedInputCertificateParser.lean` against
-- current Mathlib + Lean 4 v4.33.0 idioms). Until that lands, these
-- 3 modules stay on the conditional-CI path. The parser-fixup commits
-- from PR #80 are kept as defensive hygiene (they help conditional CI
-- even without root-import).
import CollatzResearch.Importer
import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.Q5Integration
import CollatzResearch.Q5RoutingPartition
import CollatzResearch.Q5BoundedInputBridge
import CollatzResearch.BoundedInputCertificateTree
import CollatzResearch.Q5VerifierTests
import CollatzResearch.Q5IntegrationTests
import CollatzResearch.Q5RoutingPartitionTests
import CollatzResearch.LeafClaimTests
import CollatzResearch.FiniteOrbitClaimTests
import CollatzResearch.CoverageTreeOrbitTests
import CollatzResearch.DynamicsHelpersTests
