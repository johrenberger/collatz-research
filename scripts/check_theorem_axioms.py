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

DEFAULT_TIMEOUT = 900

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
    """Classify a result into the tier recorded in the manifest."""
    if native_axioms(axioms):
        return "compiler_dependent_instance"
    if conditional:
        return "conditional_generic_theorem"
    return "kernel_proof"


def evaluate(entry: dict, axioms: list[str]) -> list[str]:
    """Check one manifest entry against its measured dependencies.

    Returns a list of failure messages; an empty list means the entry
    matches its recorded trusted base.
    """
    name = entry["name"]
    tier = entry["tier"]
    failures: list[str] = []

    if any(axiom in ADMISSION_AXIOMS for axiom in axioms):
        return [
            f"{name}: depends on an admitted declaration (sorryAx); "
            "an admitted result proves nothing"
        ]

    measured_approved = approved_axioms_of(axioms)
    recorded_approved = set(entry.get("approved_axioms", []))
    measured_native = native_owners(axioms)
    recorded_native = {
        owner: int(count) for owner, count in entry.get("native_axiom_owners", {}).items()
    }

    # The allowlist is global, not per-result. A result that rests on an
    # axiom outside the approved standard set is a finding in its own
    # right, whether or not the manifest has been re-recorded to match.
    unapproved = sorted(measured_approved - APPROVED_AXIOMS)
    if unapproved:
        failures.append(
            f"{name}: depends on axioms outside the approved standard axiom set: {unapproved}"
        )

    if measured_approved != recorded_approved:
        failures.append(
            f"{name}: approved axioms {sorted(recorded_approved)} do not match "
            f"measured {sorted(measured_approved)}"
        )

    if tier == "compiler_dependent_instance":
        # A compiler-dependent result may rest on compiler-evaluated
        # evidence, but only the evidence that was reviewed and
        # recorded. More or less evidence than recorded means the
        # record is stale.
        if measured_native != recorded_native:
            failures.append(
                f"{name}: recorded native dependencies {recorded_native} do not "
                f"match measured {measured_native}"
            )
        if not measured_native:
            failures.append(
                f"{name}: classified as compiler-dependent but measures no native "
                "dependency; the classification is stale"
            )
        return failures

    # Kernel-facing tiers: the trusted base must be the approved axiom
    # set and nothing else. A wrapper around a native-evaluated proof
    # inherits that dependency, so it fails here.
    if measured_native:
        failures.append(
            f"{name}: kernel-facing result depends on compiler-evaluated evidence "
            f"{sorted(measured_native)}"
        )
    return failures


def strip_comments(text: str) -> str:
    """Remove Lean line comments from `text`."""
    return "\n".join(line.split("--")[0] for line in text.splitlines())


def ends_type(text: str) -> bool:
    """True when `text` ends a declaration's type and starts its proof."""
    stripped = strip_comments(text)
    if ":=" in stripped:
        return True
    return re.search(r"\bby\b", stripped) is not None


def starts_body(text: str) -> bool:
    """True when a line begins a declaration body rather than its type."""
    return text.strip().startswith("|")


def is_namespace_boundary(text: str) -> bool:
    """True when a line opens or closes a namespace."""
    return NAMESPACE_RE.match(text) is not None or END_RE.match(text) is not None


def scan_declarations() -> list[dict]:
    """Return every top-level Lean declaration with its type and location.

    The type is the text between the declaration's name and the `:=`
    or `by` that starts its proof, so a mention of `ReachesOne` in the
    type can be told apart from a mention in the proof term.
    """
    results: list[dict] = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        module = "CollatzResearch." + path.stem
        lines = path.read_text(encoding="utf-8").splitlines()
        stack: list[str] = []
        index = 0
        while index < len(lines):
            line = lines[index]
            namespace_match = NAMESPACE_RE.match(line)
            if namespace_match:
                stack.append(namespace_match.group("name"))
                index += 1
                continue
            end_match = END_RE.match(line)
            if end_match:
                if stack and stack[-1] == end_match.group("name"):
                    stack.pop()
                index += 1
                continue
            match = DECL_RE.match(line)
            if not match:
                index += 1
                continue
            kind = match.group(1)
            name = match.group("name")
            start = index
            type_lines = [lines[index]]
            cursor = index + 1
            if kind not in ("structure", "inductive", "class"):
                # A structure or inductive declaration is its header; its
                # fields are not part of its type.
                while cursor < len(lines):
                    line = lines[cursor]
                    # A namespace boundary ends the type. The boundary
                    # itself is left for the caller, so the namespace
                    # stack stays correct.
                    if is_namespace_boundary(line):
                        break
                    # A pattern arm starts the body.
                    if starts_body(line):
                        break
                    type_lines.append(line)
                    cursor += 1
                    if ends_type(line):
                        break
                    if cursor - start > 60:
                        break
            qualified = ".".join([*stack, name])
            results.append(
                {
                    "name": qualified,
                    "simple_name": name,
                    "kind": kind,
                    "module": module,
                    "location": f"{rel}:{start + 1}",
                    "type": strip_comments("\n".join(type_lines)),
                }
            )
            index = cursor
    return results


def ledger_rows() -> list[tuple[str, str, str | None]]:
    """Return the (identifier, module, namespace) triples the ledger records.

    The ledger writes a result's identifier relative to its module, so
    `IsFiniteClaim` in module `CollatzResearch.FiniteOrbitClaim` is the
    constant `CollatzResearch.FiniteOrbitClaim.IsFiniteClaim`. Some rows
    name a module rather than a declaration (`Q5Stage4Tests`); those do
    not resolve to a constant and are dropped when the manifest is built.
    """
    rows: list[tuple[str, str]] = []
    tick = chr(96)
    row_re = re.compile(tick + r"([^" + tick + r"]+)" + tick)
    for line in LEDGER.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        cells = line.split("|")
        if len(cells) < 4:
            continue
        identifier = row_re.match(cells[1].strip())
        module = row_re.match(cells[3].strip())
        if not (identifier and module):
            continue
        # The module cell also records the namespace the result lives in,
        # as in (in `namespace FiniteOrbitClaim`).
        namespace = None
        for token in re.findall(tick + r"([^" + tick + r"]+)" + tick, cells[3]):
            if token.startswith("namespace "):
                namespace = token[len("namespace ") :]
        rows.append((identifier.group(1), module.group(1), namespace))
    return rows


def resolve_ledger_name(
    identifier: str, module: str, namespace: str | None, known: set[str]
) -> str | None:
    """Resolve a ledger row to a fully qualified Lean constant.

    The identifier is written relative to its module, a declaration whose
    name is already dotted (`AffineMap.comp_assoc`) is written relative
    to the root namespace, and a result inside a nested namespace is
    written relative to that namespace. Every spelling that could apply
    is tried, and the one that names a real declaration wins.
    """
    candidates = [f"{ROOT_NAMESPACE}.{identifier}"]
    if namespace:
        candidates.append(f"{ROOT_NAMESPACE}.{namespace}.{identifier}")
    if module.startswith(ROOT_NAMESPACE + "."):
        candidates.append(f"{module}.{identifier}")
    for candidate in candidates:
        if candidate in known:
            return candidate
    return None


def discover() -> list[dict]:
    """Return every exported reachability result the manifest must record.

    Three sources are unioned:

    - the exported-result ledger;
    - every declaration whose type mentions `ReachesOne`, the
      per-leaf certificate, or the two-leaf fixture;
    - the two-leaf fixture itself.

    The second and third sources close gaps the ledger cannot. A
    reachability theorem that was never written down still has to be
    classified, and so does a per-leaf certificate constructor whose
    type does not mention `ReachesOne` at all. The fixture rule
    matters most: the fixture discharges its own well-formedness fields
    by `native_decide`, so anything that mentions it inherits that
    dependency even when its own proof body is kernel-only.
    """
    declarations = scan_declarations()
    by_name = {decl["name"]: decl for decl in declarations}
    wanted: dict[str, dict] = {}

    for identifier, module, namespace in ledger_rows():
        name = resolve_ledger_name(identifier, module, namespace, set(by_name))
        if name is not None:
            wanted[name] = by_name[name]

    for decl in declarations:
        if any(token in decl["type"] for token in RESULT_TYPE_TOKENS):
            wanted[decl["name"]] = decl

    # The fixture is recorded in its own right: it is the transitive
    # source of the compiler-evaluated dependency its instances inherit.
    fixture = by_name.get(FIXTURE_NAME)
    if fixture is not None:
        wanted[FIXTURE_NAME] = fixture

    return list(wanted.values())


def measure(names: list[str]) -> tuple[dict[str, list[str]], list[str]]:
    """Measure the dependency closure of each name with `#print axioms`.

    Returns the measured closures and the names that did not resolve.
    A name that does not resolve produces a Lean error but does not
    stop the remaining commands, so the report is parsed per name.
    """
    source = "import CollatzResearch\n\n"
    source += "".join(f"#print axioms {name}\n" for name in names)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "AxiomAudit.lean"
        path.write_text(source, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=DEFAULT_TIMEOUT,
        )
    measured = parse_axiom_report(proc.stdout)
    unresolved = [name for name in names if name not in measured]
    return measured, unresolved


def build_manifest() -> tuple[dict, list[str]]:
    """Measure every discovered result and build the manifest."""
    declarations = discover()
    if not declarations:
        raise RuntimeError("no exported reachability results were discovered")
    names = [decl["name"] for decl in declarations]
    measured, unresolved = measure(names)
    results = []
    for decl in declarations:
        if decl["name"] not in measured:
            continue
        axioms = measured[decl["name"]]
        conditional = "→" in decl["type"] or "->" in decl["type"]
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
            proc = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=DEFAULT_TIMEOUT,
            )
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
    measured, unresolved = measure([entry["name"] for entry in results])
    failures: list[str] = []
    for name in unresolved:
        failures.append(f"{name}: no dependency closure was reported")
    for entry in results:
        if entry["name"] not in measured:
            continue
        failures.extend(evaluate(entry, measured[entry["name"]]))

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
