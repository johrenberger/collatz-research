Warning: truncated output (original token count: 10545)
Total output lines: 1039

#!/usr/bin/env python3
"""Audit the transitive axiom dependencies of exported Lean results.

Story R01 ("Transitive axiom audit and corrected claim tiers",
`docs/collatz-next-stories.md`) asks for a machine-readable record of
what every exported reachability result actually depends on, and a CI
gate that fails when a result's trusted base changes.

The gate is transitive by construction. `#print axioms` reports the
full dependency closure of a declaration, so a wrapper around a
native-evaluated proof is detected even when the wrapper's own tactic
is kernel-only. That is the failure mode the ADR 0009 tier cannot
see: the tier reasons about which premises a reachability theorem may
assume, not about which axioms the result ultimately rests on.

Usage:

    python3 scripts/check_theorem_axioms.py            # verify (CI gate)
    python3 scripts/check_theorem_axioms.py --update   # re-record the manifest

The script has no pytest dependency, so the Lean CI job can run it
directly, the way it already runs `scripts/check_sorry_budget.py`.

Manifest schema (`docs/theorem-axiom-manifest.json`) version 1:

    {
      "schema_version": 1,
      "toolchain": "leanprover/lean4:v4.33.0",
      "approved_axioms": ["Classical.choice", "Quot.sound", "propext"],
      "results": [
        {
          "name": "CollatzResearch.someTheorem",
          "simple_name": "someTheorem",
          "module": "CollatzResearch.SomeModule",
          "location": "Lean/CollatzResearch/SomeModule.lean:123",
          "tier": "conditional_generic_theorem",
          "approved_axioms": ["Classical.choice", "Quot.sound", "propext"],
          "native_axiom_owners": {},
          "native_axiom_names": []
        }
      ]
    }

`tier` is one of:

    conditional_generic_theorem  kernel-clean, statement carries hypotheses
    kernel_proof                 kernel-clean, unconditional
    compiler_dependent_instance  depends on compiler-evaluated evidence

`native_axiom_owners` maps the declaration that owns each generated
native axiom to the number of axioms it owns. The owner, not the
generated name, is the stable identity: Lean names a `native_decide`
axiom after the declaration that used it and appends a counter that
renumbers whenever the surrounding file changes. `native_axiom_names`
records the exact generated names for the pinned toolchain, as the
audit requires, but the gate compares owners so an unrelated edit
does not fail the build.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).parents[1]
MANIFEST = ROOT / "docs" / "theorem-axiom-manifest.json"
LEDGER = ROOT / "docs" / "theorem-status.md"
TOOLCHAIN = ROOT / "lean-toolchain"
SCHEMA_VERSION = 1

LEAN_ROOT = ROOT / "Lean"

# The Lean program that counts the proposition-valued binders of each
# measured result. Only the elaborated environment knows whether a
# binder is a proposition.
PROBE_PROGRAM = ROOT / "scripts" / "prop_binder_probe.lean"

# The probe file marks the start of its command so generated sources can emit
# one independently budgeted binder-probe command per declaration.
PROBE_RULE_MARKER = "-- PROBE-RULE"

# The binder self-test fixtures. Each measures one theorem through the probe
# and states whether the theorem carries a hypothesis.
#
# The first is the case a source-text scan cannot see. A binder of the form
# [h : Fact p] is an instance-implicit proposition, and the instance is a
# proof of p. Instance synthesis cannot conjure such a proof, so the caller
# supplies it and the theorem carries a hypothesis.
#
# The second is the counter-case: the instance is globally available, so
# synthesis satisfies it without extra assumptions and the theorem carries no
# hypothesis at all.
BINDER_SELFTEST_CASES: list[tuple[str, str, str, bool]] = [
    (
        "instance-implicit proposition premise",
        "theorem binderSelftestInstanceProp (p : Prop) [h : Fact p] : p := h.out",
        "binderSelftestInstanceProp",
        True,
    ),
    (
        "globally available instance premise",
        "class BinderSelftestGlobalProp (p : Prop) : Prop where\n"
        "  ok : True\n"
        "\n"
        "instance binderSelftestGlobalPropInst (p : Prop) "
        "    : BinderSelftestGlobalProp p where\n"
        "  ok := trivial\n"
        "\n"
        "theorem binderSelftestGlobalInstance (p : Prop) "
        "    [h : BinderSelftestGlobalProp p] : True := trivial",
        "binderSelftestGlobalInstance",
        False,
    ),
    (
        "specialized global instance premise",
        "instance binderSelftestSpecializedFactZero : Fact (0 = 0) where\n"
        "  out := rfl\n"
        "\n"
        "theorem binderSelftestSpecializedInstance (n : Nat) "
        "[h : Fact (n = 0)] : True := trivial",
        "binderSelftestSpecializedInstance",
        True,
    ),
]

# A binder-count row printed by the probe:
# `PROP|<name>|<propBinders>|<instanceImplicitPropBinders>|<unsynthesizedInstancePropBinders>`.
PROP_BINDER_RE = re.compile(
    r"^PROP\|(?P<name>[^|]+)\|(?P<prop>\d+)\|(?P<inst>\d+)\|(?P<unsynth>\d+)$",
    re.MULTILINE,
)

# The root namespace. Ledger rows name results relative to it
# ("AffineMap.comp_assoc"); Lean names them fully.
ROOT_NAMESPACE = "CollatzResearch"

# The standard Lean axiom set. A result whose whole trusted base is a
# subset of this set is checked by the Lean kernel alone.
APPROVED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# An admitted declaration. Never admissible in a release result.
ADMISSION_AXIOMS = frozenset({"sorryAx"})

# Compiler-evaluated evidence. Lean's `native_decide` generates one
# axiom per invocation, named after the declaration that used it; the
# `Lean.ofReduce*` axioms are the underlying primitive. Both make a
# result compiler-dependent, so both are detected by pattern rather
# than by name.
NATIVE_AXIOM_RE = re.compile(r"(native_decide\.ax_|ofReduceBool|ofReduceNat)")

# The axiom a native `native_decide` invocation generates is owned by
# the declaration that used it. The owner is the part of the axiom name
# before the `._native.native_decide.` marker.
NATIVE_OWNER_RE = re.compile(r"^(?P<owner>.+?)\._native\.native_decide\.ax_\d+(?:_\d+)?$")

# The measurement program imports CollatzResearch, which pulls in
# Mathlib, and it now also loads the Lean DSL for the binder analysis.
# Loading that import graph takes considerably longer than the
# measurement itself: on a host with a small page cache the oleans are
# re-read while they are loaded. The bound is therefore set well above
# the measurement.
#
# The bound is also a ceiling on the whole audit, and the Lean CI job
# allows two hours for the build and the audit together. The bound is
# kept below that job budget so that a measurement that hangs fails the
# audit with a readable message instead of being cancelled with the job,
# which would report no reason at all.
DEFAULT_TIMEOUT = 3600

# A top-level Lean declaration. The name may be dotted, which is how
# `AffineMap.comp_assoc` and friends are declared.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)

# Namespace blocks. A declaration's qualified name is its own name
# under the enclosing namespaces.
NAMESPACE_RE = re.compile(r"^namespace\s+(?P<name>[A-Za-z_][A-Za-z0-9_.]*)")
END_RE = re.compile(r"^end\s+(?P<name>[A-Za-z_][A-Za-z0-9_.]*)")

# `#print axioms` output.
DEPENDS_RE = re.compile(
    r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]",
    re.MULTILINE | re.DOTALL,
)
NO_DEPENDS_RE = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms", re.MULTILINE)

# A declaration whose type mentions one of these tokens is an exported
# result that the manifest must record, whether or not the ledger lists
# it individually:
#
#   ReachesOne                  the reachability conclusion itself
#   BoundedInputOrbitCertificate  the per-leaf certificate that the R01
#                             acceptance criteria name as a capture target
#   twoLeafRoutingPartition     the fixture whose own well-formedness
#                             fields are discharged by `native_decide`
RESULT_TYPE_TOKENS = (
    "ReachesOne",
    "BoundedInputOrbitCertificate",
    "twoLeafRoutingPartition",
)

# The two-leaf fixture. It is the transitive source of the
# compiler-evaluated dependency that every instance mentioning it
# inherits, so it is recorded in its own right.
FIXTURE_NAME = f"{ROOT_NAMESPACE}.twoLeafRoutingPartition"

# The self-test fixtures. Each is a standalone Lean file with no
# repository imports, so it elaborates without the library build.
SELFTEST_CASES: list[tuple[str, str, str, str]] = [
    (
        "known clean proof",
        "theorem selftestClean : (2 : Nat) + 2 = 4 := by decide\n",
        "kernel_clean",
        "selftestClean",
    ),
    (
        "admitted proof",
        "theorem selftestAdmitted : (2 : Nat) + 2 = 4 := by\n  sorry\n",
        "admitted",
        "selftestAdmitted",
    ),
    (
        "direct native proof",
        "theorem selftestNative : (2 : Nat) + 2 = 4 := by\n  native_decide\n",
        "native",
        "selftestNative",
    ),
    (
        "indirect wrapper around a native proof",
        "theorem selftestNativeBase : (2 : Nat) + 2 = 4 := by\n"
        "  native_decide\n"
        "\n"
        "theorem selftestWrapper : (2 : Nat) + 2 = 4 := by\n"
        "  exact selftestNativeBase\n",
        "native",
        "selftestWrapper",
    ),
]


def native_axioms(axioms: list[str]) -> list[str]:
    """Return the compiler-evaluated axioms among `axioms`."""
    return [axiom for axiom in axioms if NATIVE_AXIOM_RE.search(axiom)]


def native_owner(axiom: str) -> str:
    """Return the declaration that owns a generated native axiom.

    Generated names look like
    `CollatzResearch.someDecl._native.native_decide.ax_1`; the owner is
    the declaration whose proof used `native_decide`. An axiom that
    does not match the generated shape keeps its full name, so an
    unexpected native axiom stays visible as its own owner.
    """
    match = NATIVE_OWNER_RE.match(axiom)
    return match.group("owner") if match else axiom


def native_owners(axioms: list[str]) -> dict[str, int]:
    """Map each owner of a native axiom to the number of axioms it owns."""
    owners: dict[str, int] = {}
    for axiom in native_axioms(axioms):
        owner = native_owner(axiom)
        owners[owner] = owners.get(owner, 0) + 1
    return owners


def approved_axioms_of(axioms: list[str]) -> set[str]:
    """Return the non-native, non-admission axioms of a dependency closure."""
    return {
        axiom
        for axiom in axioms
        if axiom not in ADMISSION_AXIOMS and not NATIVE_AXIOM_RE.search(axiom)
    }


def parse_axiom_report(stdout: str) -> dict[str, list[str]]:
    """Parse the output of `#print axioms` into name -> axiom list."""
    found: dict[str, list[str]] = {}
    for match in DEPENDS_RE.finditer(stdout):
        body = match.group("axioms").replace("\n", " ")
        found[match.group("name")] = [item.strip() for item in body.split(",") if item.strip()]
    for match in NO_DEPENDS_RE.finditer(stdout):
        found.setdefault(match.group("name"), [])
    return found


def classify(axioms: list[str]) -> str:
    """Classify a dependency closure as kernel-clean, admitted, or native.

    "admitted" wins over "native": an admission is a defect in every
    category, and a result that depends on `sorryAx` proves nothing.
    """
    if any(axiom in ADMISSION_AXIOMS for axiom in axioms):
        return "admitted"
    if native_axioms(axioms):
        return "native"
    return "kernel_clean"


def tier_of(axioms: list[str], conditional: bool) -> str:
    """Classify a result into the tier recorded in the m…4545 tokens truncated…arse_prop_binder_report(proc.stdout)
    unresolved = [name for name in names if name not in measured]
    # A broken measurement must never be recorded as a manifest. If the
    # Lean program reported nothing, or if more names failed to resolve
    # than resolved, the measurement is incomplete and the recorded
    # manifest is left untouched.
    if names and not measured:
        raise RuntimeError(
            "the measurement program reported no dependency closure; "
            "the manifest is left unchanged"
        )
    if len(unresolved) > len(measured):
        raise RuntimeError(
            f"{len(unresolved)} of {len(names)} names did not resolve, so the "
            "measurement is incomplete; the manifest is left unchanged"
        )
    return measured, unresolved, conditions


def build_manifest() -> tuple[dict, list[str]]:
    """Measure every discovered result and build the manifest."""
    declarations = discover()
    if not declarations:
        raise RuntimeError("no exported reachability results were discovered")
    names = [decl["name"] for decl in declarations]
    measured, unresolved, conditions = measure(names)
    results = []
    for decl in declarations:
        if decl["name"] not in measured:
            continue
        axioms = measured[decl["name"]]
        if decl["name"] not in conditions:
            raise RuntimeError(f"no binder analysis was reported for {decl['name']}")
        prop_binders, inst_prop_binders, unsynthesized = conditions[decl["name"]]
        conditional = is_conditional(prop_binders, inst_prop_binders, unsynthesized)
        results.append(
            {
                "name": decl["name"],
                "simple_name": decl["simple_name"],
                "module": decl["module"],
                "location": decl["location"],
                "tier": tier_of(axioms, conditional),
                "approved_axioms": sorted(approved_axioms_of(axioms)),
                "native_axiom_owners": dict(sorted(native_owners(axioms).items())),
                "native_axiom_names": sorted(native_axioms(axioms)),
            }
        )
    results.sort(key=lambda entry: entry["name"])
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "toolchain": TOOLCHAIN.read_text(encoding="utf-8").strip(),
        "approved_axioms": sorted(APPROVED_AXIOMS),
        "results": results,
    }
    return manifest, unresolved


def run_binder_selftest() -> list[str]:
    """Exercise the binder classification on an instance-implicit premise.

    A premise written as an instance-implicit binder is invisible to a
    source-text scan, and it is not automatically harmless either: synthesis
    cannot conjure the proof that [Fact p] demands. The self-test measures
    both shapes through the probe and checks the classification the audit
    would record for them.
    """
    template = PROBE_PROGRAM.read_text(encoding="utf-8")
    head, rule = template.split(PROBE_RULE_MARKER, 1)
    failures: list[str] = []
    for label, fixture, probe_name, expected in BINDER_SELFTEST_CASES:
        source = (
            "import Mathlib.Logic.Basic\n"
            + head
            + fixture
            + "\n\n"
            + rule.lstrip("\n")
            + f'\n#probePropBinder "{probe_name}"\n'
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "AxiomBinderSelftest.lean"
            path.write_text(source, encoding="utf-8")
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", str(path)],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    timeout=DEFAULT_TIMEOUT,
                )
            except subprocess.TimeoutExpired:
                failures.append(f"{label}: the fixture did not finish in time")
                continue
        if proc.returncode != 0:
            failures.append(
                f"{label}: the fixture failed to elaborate: {proc.stderr.strip()[:400]}"
            )
            continue
        counts = parse_prop_binder_report(proc.stdout)
        if probe_name not in counts:
            failures.append(f"{label}: the probe reported no binder counts")
            continue
        prop_binders, inst_prop_binders, unsynthesized = counts[probe_name]
        conditional = is_conditional(prop_binders, inst_prop_binders, unsynthesized)
        if conditional != expected:
            failures.append(
                f"{label}: the premise was classified "
                f"{'conditional' if conditional else 'unconditional'}, "
                f"expected {'conditional' if expected else 'unconditional'} "
                f"(prop={prop_binders}, instance={inst_prop_binders}, "
                f"unsynthesized={unsynthesized})"
            )
    return failures


def run_selftest() -> list[str]:
    """Exercise the release gate on the four fixture shapes.

    The fixtures are not merely classified; each one is pushed through
    the same `evaluate` function the CI gate uses, so the self-test
    covers the gate itself and not a parallel implementation of it.
    """
    failures: list[str] = []
    for label, source, expected, probe_name in SELFTEST_CASES:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "AxiomSelftest.lean"
            # The fixture must ask Lean for the closure; without the
            # command there is nothing to parse.
            path.write_text(source + f"#print axioms {probe_name}\n", encoding="utf-8")
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", str(path)],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    timeout=DEFAULT_TIMEOUT,
                )
            except subprocess.TimeoutExpired:
                failures.append(f"{label}: the fixture did not finish within {DEFAULT_TIMEOUT}s")
                continue
        if proc.returncode != 0:
            failures.append(f"{label}: fixture failed to elaborate: {proc.stderr.strip()[:500]}")
            continue
        measured = parse_axiom_report(proc.stdout)
        if probe_name not in measured:
            failures.append(f"{label}: no dependency closure was reported for {probe_name}")
            continue
        axioms = measured[probe_name]
        verdict = classify(axioms)
        if verdict != expected:
            failures.append(
                f"{label}: classified as {verdict!r}, expected {expected!r} (axioms: {axioms})"
            )
            continue
        # Push the fixture through the release gate itself, recorded the way
        # a correct manifest entry records it: with the approved axioms the
        # fixture actually has. The gate must then accept the clean result
        # and reject the admitted and compiler-dependent ones.
        entry = {
            "name": probe_name,
            "tier": "conditional_generic_theorem",
            "approved_axioms": sorted(approved_axioms_of(axioms)),
            "native_axiom_owners": {},
        }
        gate_failures = evaluate(entry, axioms)
        if expected == "kernel_clean" and gate_failures:
            failures.append(f"{label}: the release gate rejected a clean result: {gate_failures}")
        if expected == "kernel_clean":
            # A stale record must fail too: that is how a changed trusted
            # base is caught between recordings.
            stale = dict(entry)
            stale["approved_axioms"] = sorted(APPROVED_AXIOMS)
            if not any("do not match" in f for f in evaluate(stale, axioms)):
                failures.append(f"{label}: the release gate did not detect a stale record")
        if expected == "admitted" and not any("sorryAx" in f for f in gate_failures):
            failures.append(f"{label}: the release gate did not reject an admitted result")
        if expected == "native" and not any("compiler-evaluated" in f for f in gate_failures):
            failures.append(f"{label}: the release gate did not reject a compiler-dependent result")
    return failures


def verify(manifest: dict) -> list[str]:
    """Check the recorded manifest against a fresh measurement."""
    results = manifest["results"]
    measured, unresolved, conditions = measure([entry["name"] for entry in results])
    failures: list[str] = []
    for name in unresolved:
        failures.append(f"{name}: no dependency closure was reported")
    for entry in results:
        if entry["name"] not in measured:
            continue
        failures.extend(evaluate(entry, measured[entry["name"]]))
        # The tier is derived from the measurement, not asserted. A
        # result whose hypothesis is a binder rather than an arrow is
        # conditional even when the source text shows no arrow, so the
        # recorded tier is re-derived and compared here.
        if entry["name"] not in conditions:
            failures.append(f"{entry['name']}: no binder analysis was reported")
            continue
        prop_binders, inst_prop_binders, unsynthesized = conditions[entry["name"]]
        expected = tier_of(
            measured[entry["name"]],
            is_conditional(prop_binders, inst_prop_binders, unsynthesized),
        )
        if entry["tier"] != expected:
            failures.append(
                f"{entry['name']}: recorded tier {entry['tier']!r} does not match the "
                f"measured tier {expected!r}"
            )

    recorded = {entry["name"] for entry in results}
    for decl in discover():
        if decl["name"] not in recorded:
            failures.append(
                f"unrecorded exported reachability result: {decl['name']} ({decl['location']})"
            )
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit transitive axiom dependencies.")
    parser.add_argument(
        "--update",
        action="store_true",
        help="re-measure every exported result and rewrite the manifest",
    )
    args = parser.parse_args(argv)

    if shutil.which("lake") is None:
        print("the axiom audit needs `lake` on PATH", file=sys.stderr)
        return 2

    try:
        if args.update:
            manifest, unresolved = build_manifest()
            MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
            tiers: dict[str, int] = {}
            for entry in manifest["results"]:
                tiers[entry["tier"]] = tiers.get(entry["tier"], 0) + 1
            summary = ", ".join(f"{tier}={count}" for tier, count in sorted(tiers.items()))
            print(f"wrote {MANIFEST.relative_to(ROOT)} ({summary})")
            for name in unresolved:
                print(f"note: {name} did not resolve to a constant", file=sys.stderr)
            failures = run_selftest()
            failures.extend(run_binder_selftest())
            if failures:
                print("\n".join(failures), file=sys.stderr)
                return 1
            return 0

        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        version = manifest.get("schema_version")
        if version != SCHEMA_VERSION:
            print(
                f"unsupported axiom manifest schema {version!r} (expected {SCHEMA_VERSION})",
                file=sys.stderr,
            )
            return 2
        failures = verify(manifest)
        failures.extend(run_selftest())
        failures.extend(run_binder_selftest())
        if failures:
            print("\n".join(failures), file=sys.stderr)
            return 1
        print(
            f"axiom audit passed ({len(manifest['results'])} recorded results, "
            f"{len(SELFTEST_CASES)} self-test cases)"
        )
        return 0
    except RuntimeError as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
