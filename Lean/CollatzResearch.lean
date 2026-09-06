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
import CollatzResearch.Importer
import CollatzResearch.CoverageTree
import CollatzResearch.BoundedInputCertificateData
import CollatzResearch.BoundedInputCertificateParser
import CollatzResearch.Q5Integration
import CollatzResearch.Q5RoutingPartition
import CollatzResearch.Q5VerifierTests
import CollatzResearch.Q5IntegrationTests
import CollatzResearch.Q5RoutingPartitionTests
import CollatzResearch.LeafClaimTests
import CollatzResearch.FiniteOrbitClaimTests
import CollatzResearch.CoverageTreeOrbitTests
import CollatzResearch.DynamicsHelpersTests
import CollatzResearch.EquivalenceHelpersTests
import CollatzResearch.BoundedInputCertificateParserTests
