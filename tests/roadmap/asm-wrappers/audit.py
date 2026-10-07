#!/usr/bin/env python3
"""A03 separation audit: the asm-wrapper harness cannot enter theorem dependencies.

Static checks (always):
  * no Lake library or executable root/glob covers tests/, so no shipped module can import
    the harness;
  * no shipped source (ZigLean, Proofs, Air2Lean, tools, root modules) names `AsmHarness` or
    imports `tests`;
  * the harness Lean files declare only `AsmHarness.*` namespaces and add no theorem, axiom,
    compiler redirection, extern or `sorry`.

With `--assurance REPORT` (scripts/assumptions.py output), also:
  * no audited declaration is an `AsmHarness` name or comes from a `tests` module;
  * every `Asm.airAsm_*` stays a plain opaque with no implementation redirection or extern;
  * every theorem of `Proofs.Asm.Proofs` is in the report and depends only on such opaques.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SHIPPED = ("ZigLean", "Proofs", "Air2Lean", "tools")
HARNESS_LEAN = ("Interp.lean", "Runner.lean")
FORBIDDEN_IN_HARNESS = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:theorem|lemma|axiom|instance)\b|@\[(?:csimp|implemented_by|extern)|\bsorry\b",
    re.M)


def static_issues(root: Path = ROOT, harness: Path = HERE) -> list[str]:
    issues = []
    config = tomllib.loads((root / "lakefile.toml").read_text())
    for kind in ("lean_lib", "lean_exe"):
        for target in config.get(kind, []):
            for pattern in [target.get("name", "")] + target.get("roots", []) + target.get("globs", []) + [target.get("root", "")]:
                if pattern.split(".", 1)[0] == "tests" or "AsmHarness" in pattern:
                    issues.append(f"lakefile {kind} {target.get('name')} covers {pattern}")
            if target.get("srcDir", ".") not in (".", "./"):
                issues.append(f"lakefile {kind} {target.get('name')} has a custom srcDir")
    sources = [p for d in SHIPPED for p in sorted((root / d).rglob("*.lean"))]
    sources += sorted(root.glob("*.lean"))
    for path in sources:
        text = path.read_text()
        if "AsmHarness" in text or re.search(r"^\s*import\s+tests\b", text, re.M):
            issues.append(f"{path.relative_to(root)} refers to the asm harness or a tests module")
    for name in HARNESS_LEAN:
        text = (harness / name).read_text()
        if FORBIDDEN_IN_HARNESS.search(text):
            issues.append(f"{name} declares a logical fact, redirection or sorry")
        namespaces = re.findall(r"^namespace\s+(\S+)", text, re.M)
        if not namespaces or any(n.split(".", 1)[0] != "AsmHarness" for n in namespaces):
            issues.append(f"{name} declares outside the AsmHarness namespace")
        if re.search(r"^\s*import\b", text, re.M):
            issues.append(f"{name} must stay import-free (harness.py assembles the program)")
    return issues


def report_issues(report: dict) -> list[str]:
    if report.get("schema_version") != 1 or "nodes" not in report:
        return ["assurance report is missing or not a completed schema-1 report"]
    issues = []
    nodes = {n["name"]: n for n in report["nodes"]}
    for node in nodes.values():
        if node["name"].startswith("AsmHarness") or node.get("module", "").split(".", 1)[0] == "tests":
            issues.append(f"harness declaration in audited graph: {node['name']}")
    asm_opaques = {name for name in nodes if re.fullmatch(r"Asm\.airAsm_\d+", name)}
    if not asm_opaques:
        issues.append("no Asm.airAsm_* opaque in the audited graph")
    for name in sorted(asm_opaques):
        node = nodes[name]
        if node["kind"] != "opaque" or node.get("implemented_by") or node.get("extern"):
            issues.append(f"{name} is no longer an uninterpreted opaque")
    asm_theorems = [t for t in report.get("theorems", [])
                    if nodes.get(t["name"], {}).get("module") == "Proofs.Asm.Proofs"]
    if not asm_theorems:
        issues.append("Proofs.Asm.Proofs theorems are absent from the report")
    def project(name: str) -> bool:
        return name.startswith("AsmHarness") or (
            nodes.get(name, {}).get("module", "").split(".", 1)[0] in ("Proofs", "ZigLean", "tests"))

    for theorem in asm_theorems:
        extra = [d for d in theorem.get("opaque_dependencies", []) if d not in asm_opaques and project(d)]
        extra += [d for key in ("compiler_redirections", "extern_dependencies")
                  for d in theorem.get(key, []) if project(d)]
        if extra:
            issues.append(f"{theorem['name']} depends on more than the asm opaques: {sorted(extra)}")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--assurance", type=Path, help="scripts/assumptions.py report to check")
    args = parser.parse_args()
    issues = static_issues()
    if args.assurance:
        issues += report_issues(json.loads(args.assurance.read_text()))
    for issue in issues:
        print(f"asm-wrappers audit: {issue}", file=sys.stderr)
    if issues:
        return 1
    print("asm-wrappers audit: harness is outside every Lake target and theorem dependency"
          + (" (assurance report checked)" if args.assurance else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
