#!/usr/bin/env python3
"""Extract compiled Lean dependencies and apply the explicit assurance policy."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MARKER = "AIR2LEAN_ASSURANCE_JSON:"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
POLICY_FIELDS = {"schema_version", "standard_logical_axioms", "project_axioms",
                 "project_opaques", "project_compiler_redirections", "project_externs"}


def is_compiler_axiom(name: str) -> bool:
    # Lean 4.34 nativeEqTrue emits one fresh axiom per tactic invocation.
    name = name.split("::", 1)[-1]
    return name.startswith("Lean.ofReduce") or bool(re.search(
        r"(?:^|\.)_native\.[^.]+\.ax(?:_[0-9]+)*$", name))


def shipped_modules(root: Path = ROOT) -> list[str]:
    """Select modules from paths, never infer theorem names from source text."""
    modules = []
    for directory in ("ZigLean", "Proofs"):
        paths = sorted((root / directory).rglob("*.lean"))
        if not paths:
            raise ValueError(f"{directory}/ contains no Lean modules")
        modules.extend(".".join(p.relative_to(root).with_suffix("").parts) for p in paths)
    if not (root / "ZigLean.lean").is_file():
        raise ValueError("ZigLean.lean is missing")
    return sorted(["ZigLean", *modules])


def load_policy(path: Path) -> dict:
    policy = json.loads(path.read_text())
    if set(policy) != POLICY_FIELDS or policy["schema_version"] != 1:
        raise ValueError("unsupported assurance policy schema")
    if set(policy["standard_logical_axioms"]) != STANDARD_AXIOMS:
        raise ValueError("standard logical axiom policy must list exactly Lean's three axioms")
    for field in POLICY_FIELDS - {"schema_version"}:
        if not isinstance(policy[field], dict):
            raise ValueError(f"policy {field} must be an object")
        for name, entry in policy[field].items():
            if name == "sorryAx" or name.endswith("::sorryAx") or "ofReduce" in name or is_compiler_axiom(name):
                raise ValueError("sorry and compiler proof axioms cannot be allowlisted")
            if field == "project_compiler_redirections":
                if (not isinstance(entry, dict) or set(entry) != {"implementation", "reason"}
                        or not all(isinstance(v, str) and v.strip() for v in entry.values())):
                    raise ValueError(f"invalid compiler redirection policy: {name}")
            elif field == "project_externs":
                if (not isinstance(entry, dict) or set(entry) != {"targets", "reason"}
                        or not isinstance(entry["reason"], str) or not entry["reason"].strip()
                        or not isinstance(entry["targets"], list) or not entry["targets"]):
                    raise ValueError(f"invalid extern policy: {name}")
                for target in entry["targets"]:
                    if (not isinstance(target, dict) or set(target) != {"kind", "backend", "target"}
                            or target["kind"] not in {"standard", "inline", "adhoc", "opaque"}
                            or not isinstance(target["backend"], str) or not target["backend"]
                            or (target["kind"] in {"standard", "inline"} and
                                (not isinstance(target["target"], str) or not target["target"]))
                            or (target["kind"] in {"adhoc", "opaque"} and target["target"] is not None)):
                        raise ValueError(f"invalid extern target: {name}")
            elif not isinstance(entry, str) or not entry.strip():
                raise ValueError(f"policy entry requires a reason: {name}")
    return policy


def policy_key(node: dict) -> str:
    return node["module"] + "::" + node.get("user_name", node["name"])


def is_project_module(module: str, modules: set[str]) -> bool:
    return module in modules or not module.startswith(("Init.", "Std.", "Lean."))


def classify(node: dict, policy: dict, modules: set[str]) -> tuple[str, str | None]:
    name, kind = node["name"], node["kind"]
    if kind == "unresolved":
        return "unresolved", "declaration missing from checked environment"
    if name == "sorryAx":
        return "sorry", "hidden or direct sorry dependency"
    if kind == "axiom":
        if name in STANDARD_AXIOMS:
            return "standard-logical-axiom", None
        if is_compiler_axiom(name):
            return "compiler-proof-axiom", "compiler-dependent proof axiom"
        reason = policy["project_axioms"].get(policy_key(node))
        return ("allowed-project-axiom", None) if reason else (
            "unexpected-axiom", "axiom absent from explicit project policy")
    if node.get("unsafe"):
        return "unsafe-declaration", "unsafe declaration in logical dependencies"
    if kind == "opaque":
        if policy_key(node) in policy["project_opaques"]:
            return "allowed-project-opaque", None
        if is_project_module(node["module"], modules):
            return "unexpected-opaque", "opaque absent from explicit project policy"
        return "standard-library-opaque", None
    return "kernel-declaration", None


def apply_policy(raw: dict, policy: dict) -> dict:
    if raw.get("schema_version") != 1:
        raise ValueError("unsupported extractor schema")
    modules = set(raw["modules"])
    nodes = {n["name"]: dict(n) for n in raw["nodes"]}
    if len(nodes) != len(raw["nodes"]):
        raise ValueError("duplicate declaration in extracted graph")
    issues: dict[str, dict] = {}
    for name, node in nodes.items():
        trust, problem = classify(node, policy, modules)
        node["trust_class"] = trust
        issue_trust = trust
        key = policy_key(node)
        if key in policy["project_opaques"]:
            node["policy_reason"] = policy["project_opaques"][key]
        if key in policy["project_axioms"]:
            node["policy_reason"] = policy["project_axioms"][key]
        # Compiler replacement edges are disclosed separately from logical edges.
        # They do not become extra axioms merely because differential execution uses them.
        if node.get("implemented_by") and is_project_module(node["module"], modules):
            allowed = policy["project_compiler_redirections"].get(key)
            if not allowed or allowed["implementation"] != node["implemented_by"]:
                problem = "project compiler redirection absent from explicit policy"
                node["compiler_trust_class"] = "unexpected-compiler-redirection"
                issue_trust = "unexpected-compiler-redirection"
            else:
                node["compiler_trust_class"] = "allowed-runtime-redirection"
                node["compiler_policy_reason"] = allowed["reason"]
        elif node.get("implemented_by"):
            node["compiler_trust_class"] = "runtime-implementation"
        externs = node.get("extern", [])
        if not isinstance(externs, list):
            raise ValueError(f"extern targets must be explicit entries: {name}")
        if externs and is_project_module(node["module"], modules):
            allowed = policy["project_externs"].get(key)
            if not allowed or allowed["targets"] != externs:
                problem = "project extern targets absent from explicit policy or differ from it"
                node["extern_trust_class"] = "unexpected-project-extern"
                issue_trust = "unexpected-project-extern"
            else:
                node["extern_trust_class"] = "allowed-project-extern"
                node["extern_policy_reason"] = allowed["reason"]
        elif externs:
            node["extern_trust_class"] = "standard-runtime-extern"
        if problem:
            issues[name] = {"name": name, "module": node["module"],
                            "trust_class": issue_trust, "reason": problem}
        for dependency in node["dependencies"]:
            if dependency not in nodes:
                raise ValueError(f"incomplete declaration graph: {name} -> {dependency}")

    theorems = []
    for original in raw["theorems"]:
        theorem = dict(original)
        if theorem["name"] not in nodes or nodes[theorem["name"]]["kind"] != "theorem":
            raise ValueError("theorem inventory does not match checked declaration graph")
        visited, pending = set(), [theorem["name"]]
        while pending:
            name = pending.pop()
            if name not in visited:
                visited.add(name)
                pending.extend(nodes[name]["dependencies"])
        # collectAxioms includes Lean's precomputed dependencies from imported modules.
        # Check its output even if future olean formats hide a proof body from the graph.
        for axiom in theorem["axioms"]:
            if axiom not in nodes:
                issues.setdefault(axiom, {"name": axiom, "module": "", "trust_class": "unresolved-axiom",
                                          "reason": "axiom inventory absent from dependency graph"})
            elif nodes[axiom]["kind"] != "axiom":
                raise ValueError(f"invalid axiom inventory entry: {axiom}")
            visited.add(axiom)
        theorem["dependencies"] = nodes[theorem["name"]]["dependencies"]
        theorem["opaque_dependencies"] = sorted(n for n in visited if n in nodes and nodes[n]["kind"] == "opaque")
        theorem["compiler_redirections"] = sorted(n for n in visited if n in nodes and nodes[n].get("implemented_by"))
        theorem["extern_dependencies"] = sorted(n for n in visited if n in nodes and nodes[n].get("extern"))
        theorem["violations"] = sorted(visited.intersection(issues))
        theorem["allowed"] = not theorem["violations"]
        theorems.append(theorem)
    if not theorems:
        raise ValueError("no checked theorems selected; nothing was audited")
    return {"schema_version": 1, "status": "fail" if issues else "pass",
            "modules": sorted(modules), "theorem_count": len(theorems),
            "theorems": sorted(theorems, key=lambda t: t["name"]),
            "project_declarations": raw.get("project_declarations", []),
            "nodes": sorted(nodes.values(), key=lambda n: n["name"]),
            "violations": sorted(issues.values(), key=lambda n: n["name"])}


def run(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(command)}")
    if result.stderr:
        sys.stderr.write(result.stderr)
    return result.stdout


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def prepare_tool(root: Path = ROOT, runner=run) -> dict:
    """Always ask Lake to validate dependencies; discard unverified/corrupt output."""
    artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
    lake_trace = artifact.with_suffix(".trace")
    manifest = root / ".lake/assurance/tool-trace.json"
    context = {
        "schema_version": 1,
        "module": "tools.Assurance",
        "source_sha256": file_sha256(root / "tools/Assurance.lean"),
        "lean_toolchain_sha256": file_sha256(root / "lean-toolchain"),
        "lake_config_sha256": file_sha256(root / "lakefile.toml"),
    }
    try:
        cached = json.loads(manifest.read_text())
    except (OSError, ValueError):
        cached = {}
    valid = (isinstance(cached, dict) and all(cached.get(k) == v for k, v in context.items())
             and artifact.is_file() and lake_trace.is_file()
             and cached.get("olean_sha256") == file_sha256(artifact)
             and cached.get("lake_trace_sha256") == file_sha256(lake_trace))
    if not valid:
        # Lake must rebuild when output or its independently recorded identity is missing,
        # corrupt, or from a different extractor source, release pin, or configuration.
        artifact.unlink(missing_ok=True)
    # --rehash makes Lake recompute file hashes rather than trust cached hash sidecars.
    # Its dependency trace includes compiler identity and imported module build traces.
    runner(["lake", "--rehash", "build", "AssuranceTools"])
    trace = {**context, "olean_sha256": file_sha256(artifact),
             "lake_trace_sha256": file_sha256(lake_trace)}
    trace["cache_reused"] = bool(valid and cached.get("olean_sha256") == trace["olean_sha256"]
                                 and cached.get("lake_trace_sha256") == trace["lake_trace_sha256"])
    write_report(manifest, trace)
    return trace


def extract(modules: list[str], build: bool) -> dict:
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", m) for m in modules):
        raise ValueError("invalid Lean module name")
    if build:
        # Build each selected module, including newly added modules absent from old manifests.
        run(["lake", "build", *modules])
    tool_trace = prepare_tool()
    directory = ROOT / ".lake/assurance"
    directory.mkdir(parents=True, exist_ok=True)
    driver = "import tools.Assurance\n" + "".join(f"import {m}\n" for m in modules)
    driver += "set_option maxHeartbeats 0\n#assurance_audit [" + ", ".join(json.dumps(m) for m in modules) + "]\n"
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=directory, delete=False) as handle:
        handle.write(driver)
        path = Path(handle.name)
    try:
        output = run(["lake", "env", "lean", str(path)])
    finally:
        path.unlink(missing_ok=True)
    lines = [line[len(MARKER):] for line in output.splitlines() if line.startswith(MARKER)]
    if len(lines) != 1:
        raise ValueError("extractor did not return exactly one environment report")
    raw = json.loads(lines[0])
    raw["extractor"] = tool_trace
    return raw


def write_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as handle:
        json.dump(report, handle, indent=2)
        handle.write("\n")
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/assurance/assumptions.json")
    parser.add_argument("--policy", type=Path, default=ROOT / "assurance/policy.json")
    parser.add_argument("--module", action="append", help="audit explicit modules instead of the complete shipped scope")
    parser.add_argument("--no-build", action="store_true", help="audit prebuilt modules (caller must ensure artifacts are current)")
    args = parser.parse_args()
    try:
        policy = load_policy(args.policy)
        modules = sorted(set(args.module)) if args.module else shipped_modules()
        raw = extract(modules, not args.no_build)
        if raw["modules"] != modules:
            raise ValueError("extractor scope differs from requested module inventory")
        report = apply_policy(raw, policy)
        report["extractor"] = raw["extractor"]
        del raw
        report["scope"] = "explicit-modules" if args.module else "all-shipped-modules"
        report["build_checked"] = not args.no_build
        report["policy_sha256"] = hashlib.sha256(args.policy.read_bytes()).hexdigest()
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        write_report(args.output, report)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        # Overwrite any old successful report; a failed build is never stale assurance evidence.
        write_report(args.output, {"schema_version": 1, "status": "error", "error": str(error)})
        print(f"assurance error: {error}", file=sys.stderr)
        return 2
    print(f"assurance {report['status']}: {report['theorem_count']} checked theorems; report: {args.output}", file=sys.stderr)
    for issue in report["violations"]:
        print(f"  {issue['name']}: {issue['reason']}", file=sys.stderr)
    return 1 if report["violations"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
