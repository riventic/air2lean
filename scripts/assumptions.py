#!/usr/bin/env python3
"""Extract compiled Lean dependencies and apply the explicit assurance policy."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
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
# Modules under these roots ship with the pinned toolchain; every other module in a theorem's
# dependency graph must be replayed through the kernel (`leanchecker`) before it is trusted.
TOOLCHAIN_ROOTS = ("Init", "Std", "Lean", "Lake")
# Module roots of the lakefile.toml targets: their oleans are trace-checked by Lake.
LAKE_ROOTS = ("ZigLean", "Air2Lean", "Proofs", "tools")
REPLAY_FIELDS = {"schema_version", "tool", "tool_sha256", "lean_sha256", "toolchain",
                 "modules", "modules_sha256", "reused", "rejected", "status"}


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


def needs_replay(module: str) -> bool:
    return bool(module) and module.split(".")[0] not in TOOLCHAIN_ROOTS


def modules_digest(modules: list[str]) -> str:
    return hashlib.sha256("".join(m + "\n" for m in modules).encode()).hexdigest()


def replay_record(replay) -> tuple[set[str], set[str]]:
    """Validate a kernel-replay record; return the replayed and the rejected modules."""
    if not isinstance(replay, dict) or set(replay) != REPLAY_FIELDS or replay["schema_version"] != 1:
        raise ValueError("missing or malformed kernel replay record")
    modules, rejected = replay["modules"], replay["rejected"]
    if (replay["tool"] != "leanchecker" or not isinstance(modules, list)
            or modules != sorted(set(modules)) or not all(isinstance(m, str) and m for m in modules)
            or replay["modules_sha256"] != modules_digest(modules) or not isinstance(rejected, list)
            or not all(isinstance(r, dict) and set(r) == {"module", "output"} and r["module"] in modules
                       for r in rejected)
            or not isinstance(replay["reused"], list) or not set(replay["reused"]) <= set(modules)
            or replay["status"] != ("fail" if rejected else "pass")):
        raise ValueError("inconsistent kernel replay record")
    return set(modules), {r["module"] for r in rejected}


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


_FLOAT_SEMANTICS = None


def float_semantics():
    """The float-semantics labeler next to this script (docs/float-semantics.md)."""
    global _FLOAT_SEMANTICS
    if _FLOAT_SEMANTICS is not None:
        return _FLOAT_SEMANTICS
    spec = importlib.util.spec_from_file_location("air2lean_float_semantics", ROOT / "scripts/float-semantics.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _FLOAT_SEMANTICS = module
    return module


def apply_policy(raw: dict, policy: dict, labels: dict | None = None, require_theorems: bool = True) -> dict:
    if raw.get("schema_version") != 1:
        raise ValueError("unsupported extractor schema")
    modules = set(raw["modules"])
    nodes = {n["name"]: dict(n) for n in raw["nodes"]}
    if len(nodes) != len(raw["nodes"]):
        raise ValueError("duplicate declaration in extracted graph")
    replayed, rejected = replay_record(raw.get("kernel_replay"))
    if not modules <= replayed:
        raise ValueError("kernel replay does not cover the selected modules")
    issues: dict[str, dict] = {}
    for name, node in nodes.items():
        trust, problem = classify(node, policy, modules)
        # TRU-01 is enforced, not assumed: a declaration counts only if the kernel re-checked its
        # module. An elaborator option such as debug.skipKernelTC writes unchecked oleans.
        if node["module"] in rejected:
            trust, problem = "kernel-replay-rejected", "module rejected by kernel replay"
        elif needs_replay(node["module"]) and node["module"] not in replayed:
            trust, problem = "kernel-replay-missing", "module was not replayed through the kernel"
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

    if any(t["name"] not in nodes or nodes[t["name"]]["kind"] != "theorem" for t in raw["theorems"]):
        raise ValueError("theorem inventory does not match checked declaration graph")
    # Every numerical theorem states the float semantics it concerns; none claims binary
    # correspondence. Label issues fail the audit exactly like dependency-policy issues.
    labeler = float_semantics()
    registry = labeler.load_registry(root=ROOT) if labels is None else labels
    float_records, float_issues, float_summary = labeler.label_theorems(nodes, raw["theorems"], modules, registry)
    for name, issue in float_issues.items():
        issues.setdefault(name, issue)

    theorems = []
    for original in raw["theorems"]:
        theorem = dict(original)
        theorem.pop("float_semantics", None)
        if theorem["name"] in float_records:
            theorem["float_semantics"] = float_records[theorem["name"]]
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
        # Statement-only edges (kernel type; conclusion without binders/hypotheses) bind goals
        # in `project.py coverage`. They are a subset of the declaration's own edges.
        statement = theorem.get("statement_dependencies")
        conclusion = theorem.get("conclusion_dependencies")
        if statement is not None or conclusion is not None:
            lists = isinstance(statement, list) and isinstance(conclusion, list)
            if not (lists and all(isinstance(n, str) for n in statement + conclusion)
                    and set(conclusion) <= set(statement) <= set(theorem["dependencies"])):
                raise ValueError(f"invalid statement dependencies: {theorem['name']}")
        theorem["opaque_dependencies"] = sorted(n for n in visited if n in nodes and nodes[n]["kind"] == "opaque")
        theorem["compiler_redirections"] = sorted(n for n in visited if n in nodes and nodes[n].get("implemented_by"))
        theorem["extern_dependencies"] = sorted(n for n in visited if n in nodes and nodes[n].get("extern"))
        theorem["violations"] = sorted(visited.intersection(issues))
        theorem["allowed"] = not theorem["violations"]
        theorems.append(theorem)
    if not theorems and require_theorems:
        raise ValueError("no checked theorems selected; nothing was audited")
    return {"schema_version": 1, "status": "fail" if issues else "pass",
            "modules": sorted(modules), "theorem_count": len(theorems),
            "kernel_replay": raw["kernel_replay"],
            "theorems": sorted(theorems, key=lambda t: t["name"]),
            "project_declarations": raw.get("project_declarations", []),
            "nodes": sorted(nodes.values(), key=lambda n: n["name"]),
            "float_semantics": float_summary,
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


def lake_env(name: str) -> str:
    return run(["lake", "env", "printenv", name]).strip()


def git_revision(root: Path = ROOT) -> dict:
    def git(*args):
        return subprocess.run(["git", "-C", str(root), *args], check=True, text=True,
                              capture_output=True, timeout=30).stdout
    try:
        return {"head": git("rev-parse", "HEAD").strip(),
                "tracked_dirty": bool(git("status", "--porcelain", "--untracked-files=no"))}
    except (OSError, subprocess.SubprocessError):
        return {"head": None, "tracked_dirty": True}


def locate(module: str, lean_path: list[Path]) -> Path:
    relative = module.replace(".", "/") + ".olean"
    for directory in lean_path:
        if (directory / relative).is_file():
            return directory / relative
    raise ValueError(f"no compiled module for {module}")


def display(path: Path) -> str:
    return path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)


def kernel_replay(digests: dict[str, str], toolchain: Path, lean_path: str, cache: Path | None = None,
                  cacheable: frozenset = frozenset()) -> dict:
    """Re-check every declaration of each module with the toolchain's independent `leanchecker`.

    Imports are loaded from oleans, so the caller passes every non-toolchain module of the
    dependency graph: together they replay the complete closure above the toolchain. `cache`
    (one build only; receipts never use it) holds `cacheable` (Lake-built) modules that already
    passed with the same checker and identical olean bytes. Their imports are Lake-built too, so
    any differing digest among them drops the whole cache."""
    from concurrent.futures import ThreadPoolExecutor  # Lazy: the offline receipt suite has a 32 MiB budget.
    checker = toolchain / "bin/leanchecker"
    checker_sha = file_sha256(checker)
    environment = {**os.environ, "LEAN_PATH": lean_path}
    jobs = max(1, int(os.environ.get("AIR2LEAN_REPLAY_JOBS") or min(4, os.cpu_count() or 1)))
    try:
        cached = json.loads(cache.read_text()) if cache else {}
    except FileNotFoundError:
        cached = {}
    passed = cached.get("passed", {}) if cached.get("tool_sha256") == checker_sha else {}
    if any(passed.get(m, d) != d for m, d in digests.items() if m in cacheable):
        passed = {}  # Another build: a reused module could depend on a changed one.
    modules = sorted(digests)
    reused = [m for m in modules if m in cacheable and passed.get(m) == digests[m]]

    def check(module: str):
        result = subprocess.run([str(checker), module], cwd=ROOT, env=environment, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return None if result.returncode == 0 else {"module": module, "output": result.stdout[-2000:]}

    with ThreadPoolExecutor(jobs) as pool:
        rejected = [r for r in pool.map(check, sorted(set(modules) - set(reused))) if r is not None]
    if cache:
        failed = {r["module"] for r in rejected}
        passed.update({m: d for m, d in digests.items() if m in cacheable and m not in failed})
        write_report(cache, {"tool_sha256": checker_sha, "passed": passed})
    return {"schema_version": 1, "tool": "leanchecker", "tool_sha256": checker_sha,
            "lean_sha256": file_sha256(toolchain / "bin/lean"),
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "modules": modules, "modules_sha256": modules_digest(modules), "reused": reused,
            "rejected": rejected, "status": "fail" if rejected else "pass"}


def replay_and_freshness(raw: dict, cache: Path | None = None) -> dict:
    """Kernel-replay the audited closure (S1) and bind it to artifact digests and the tree (H1)."""
    toolchain = Path(lake_env("LEAN_SYSROOT")).resolve()
    lean_path_text = lake_env("LEAN_PATH")
    lean_path = [Path(p).resolve() for p in lean_path_text.split(os.pathsep) if p]
    standard = toolchain / "lib/lean"
    graph_modules = {n["module"] for n in raw["nodes"]}
    for module in sorted(m for m in graph_modules if m and not needs_replay(m)):
        if not locate(module, lean_path).is_relative_to(standard):
            raise ValueError(f"toolchain module {module} is shadowed by a project olean")
    built = ROOT / ".lake/build/lib/lean"
    artifacts, lake_modules = [], []
    for module in sorted(set(raw["modules"]) | {m for m in graph_modules if needs_replay(m)}):
        olean = locate(module, lean_path)
        row = {"module": module, "olean": display(olean), "olean_sha256": file_sha256(olean),
               "source": None, "source_sha256": None}
        source = ROOT / (module.replace(".", "/") + ".lean")
        if olean.is_relative_to(built) and module.split(".")[0] in LAKE_ROOTS and source.is_file():
            row.update(source=display(source), source_sha256=file_sha256(source))
            lake_modules.append(module)
        artifacts.append(row)
    if lake_modules:
        # Fails if any Lake-built olean is stale against its sources (--no-build audits too).
        run(["lake", "--rehash", "build", "--no-build", *lake_modules])
    raw["kernel_replay"] = kernel_replay({r["module"]: r["olean_sha256"] for r in artifacts},
                                         toolchain, lean_path_text, cache, frozenset(lake_modules))
    return {"revision": git_revision(), "lake_trace_check": {"modules": lake_modules, "status": "up-to-date"},
            "artifacts": artifacts}


def verify_fresh(report: dict, allow_dirty: bool = False) -> dict:
    """Recompute the digests a report was bound to; fail on a stale report or tree (H1)."""
    freshness = report.get("freshness")
    if not isinstance(freshness, dict) or not isinstance(freshness.get("artifacts"), list):
        raise ValueError("assurance report carries no freshness binding; re-run scripts/assumptions.py")
    recorded, current = freshness.get("revision"), git_revision()
    if not isinstance(recorded, dict) or recorded.get("head") is None or recorded.get("head") != current["head"]:
        raise ValueError(f"assurance report is not for revision {current['head']}")
    dirty = recorded.get("tracked_dirty") or current["tracked_dirty"]
    if dirty and not allow_dirty:
        raise ValueError("assurance report or tree has uncommitted tracked changes (pass --allow-dirty to record them)")
    if (freshness.get("lake_trace_check") or {}).get("status") != "up-to-date":
        raise ValueError("assurance report has no passing Lake trace check")
    for row in freshness["artifacts"]:
        for kind in ("olean", "source"):
            path = row[kind] and (ROOT / row[kind] if not Path(row[kind]).is_absolute() else Path(row[kind]))
            if path and (not path.is_file() or file_sha256(path) != row[kind + "_sha256"]):
                raise ValueError(f"assurance report is stale: {row['module']} {kind} changed")
    return {"head": current["head"], "tracked_dirty": dirty, "dirty_allowed": bool(dirty and allow_dirty),
            "artifacts": len(freshness["artifacts"])}


def write_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        try:
            json.dump(report, handle, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        os.replace(temporary, path)  # Atomic replacement: readers see the old or the complete report.
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/assurance/assumptions.json")
    parser.add_argument("--policy", type=Path, default=ROOT / "assurance/policy.json")
    parser.add_argument("--float-semantics", type=Path, default=ROOT / "assurance/float-semantics.json",
                        help="float-semantics label registry (docs/float-semantics.md)")
    parser.add_argument("--module", action="append", help="audit explicit modules instead of the complete shipped scope")
    parser.add_argument("--no-build", action="store_true",
                        help="audit prebuilt modules; Lake-built ones must still pass Lake's trace check")
    parser.add_argument("--replay-cache", type=Path,
                        help="reuse kernel replays of identical oleans within one run (never for receipts)")
    parser.add_argument("--allow-no-theorems", action="store_true",
                        help="audit declarations of modules whose only proofs are examples")
    args = parser.parse_args()
    try:
        policy = load_policy(args.policy)
        labels = float_semantics().load_registry(args.float_semantics, root=ROOT)
        modules = sorted(set(args.module)) if args.module else shipped_modules()
        raw = extract(modules, not args.no_build)
        if raw["modules"] != modules:
            raise ValueError("extractor scope differs from requested module inventory")
        freshness = replay_and_freshness(raw, args.replay_cache)
        report = apply_policy(raw, policy, labels, not args.allow_no_theorems)
        report["freshness"] = freshness
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
