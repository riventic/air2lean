#!/usr/bin/env python3
"""External contract assumption report for generated Lean (E01, docs/external-models.md).

Reads the `-- air2lean-models:` marker of each generated file. A binding is `verified` only
when its trust is a proved obligation, the generated file kernel checks, and `#print axioms`
of its evidence reports only Lean's standard axioms. Every other used contract is listed as
an assumption with its reason. Without `--check` nothing is kernel checked, so every
contract stays an assumption. Run under `lake env` so `lean` finds the imported modules.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODELS_MARKER = "-- air2lean-models: "
NAMESPACE_RE = re.compile(r"^namespace (\S+)$", re.MULTILINE)
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def parse_generated(text: str) -> tuple[dict, str]:
    """The binding report and the namespace of one generated file."""
    marker = next((line for line in text.splitlines() if line.startswith(MODELS_MARKER)), None)
    if marker is None:
        raise ValueError("no air2lean-models marker: the file binds no external contracts")
    report = json.loads(marker[len(MODELS_MARKER):])
    if report.get("schema") != 1 or not isinstance(report.get("bindings"), list):
        raise ValueError("unsupported air2lean-models report")
    namespace = NAMESPACE_RE.search(text)
    if namespace is None:
        raise ValueError("generated file has no namespace")
    return report, namespace.group(1)


def evidence_names(namespace: str, count: int) -> list[str]:
    return [f"{namespace}.air2lean_model_{index}_evidence" for index in range(count)]


def parse_axioms(output: str) -> dict[str, list[str]]:
    axioms = {name: [] for name in NO_AXIOMS_RE.findall(output)}
    for name, listed in AXIOMS_RE.findall(output):
        axioms[name] = [axiom.strip() for axiom in listed.split(",") if axiom.strip()]
    return axioms


def kernel_axioms(text: str, names: list[str], lean: str) -> tuple[dict[str, list[str]] | None, str]:
    """Kernel check `text` and print the axioms of `names`; None if the file fails."""
    probe = text + "\n" + "".join(f"#print axioms {name}\n" for name in names)
    with tempfile.TemporaryDirectory(prefix="air2lean-contracts-") as tmp:
        path = Path(tmp) / "Probe.lean"
        path.write_text(probe)
        result = subprocess.run([lean, str(path)], text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode != 0:
        return None, output
    return parse_axioms(output), output


def classify(binding: dict, axioms: list[str] | None, checked: bool) -> tuple[str, str]:
    if binding.get("trust") != "proved-obligation":
        return "assumption", "assumed binding: the evidence is an explicit axiom"
    if not checked:
        return "assumption", "proof obligation not kernel checked (run with --check)"
    if axioms is None:
        return "assumption", "generated file failed kernel checking or evidence axioms unavailable"
    extra = sorted(set(axioms) - STANDARD_AXIOMS)
    if extra:
        return "assumption", "evidence depends on non-standard axioms: " + ", ".join(extra)
    return "verified", "kernel-checked implementation theorem using only standard axioms"


def report(paths: list[Path], check: bool, lean: str = "lean") -> dict:
    contracts = []
    for path in paths:
        text = path.read_text()
        models, namespace = parse_generated(text)
        names = evidence_names(namespace, len(models["bindings"]))
        found: dict[str, list[str]] | None = None
        if check:
            found, _ = kernel_axioms(text, names, lean)
        for binding, name in zip(models["bindings"], names):
            axioms = None if found is None else found.get(name)
            status, reason = classify(binding, axioms, check)
            contracts.append({
                "file": str(path), "symbol": binding["symbol"], "evidence": name,
                "contract": binding["contract"], "implementation": binding["implementation"],
                "trust": binding["trust"], "proof": binding.get("proof"),
                "termination": binding["termination"], "errors": binding["errors"],
                "effects": binding["effects"], "footprint": binding.get("footprint"),
                "axioms": axioms, "status": status, "reason": reason})
    return {"schema": 1, "contracts": contracts,
            "assumptions": [c["symbol"] for c in contracts if c["status"] != "verified"]}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("generated", nargs="+", type=Path, help="generated Lean files")
    parser.add_argument("--check", action="store_true", help="kernel check and print evidence axioms")
    parser.add_argument("--lean", default="lean", help="Lean executable (default: lean)")
    parser.add_argument("--expect-assumptions", help="comma-separated symbols that must be exactly the assumptions")
    args = parser.parse_args(argv)
    try:
        result = report(args.generated, args.check, args.lean)
    except (OSError, ValueError, KeyError) as error:
        print(f"external-contracts: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2))
    if args.expect_assumptions is not None:
        expected = sorted(filter(None, args.expect_assumptions.split(",")))
        if sorted(result["assumptions"]) != expected:
            print(f"external-contracts: assumptions {result['assumptions']} != expected {expected}",
                  file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
