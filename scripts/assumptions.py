#!/usr/bin/env python3
"""Extract compiled Lean dependencies and apply the explicit assurance policy."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import premise_markers  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
MARKER = "AIR2LEAN_ASSURANCE_JSON:"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
POLICY_FIELDS = {"schema_version", "standard_logical_axioms", "project_axioms",
                 "project_opaques", "project_compiler_redirections", "project_externs",
                 "generated_declarations"}
PREMISE_ID = re.compile(r"[A-Z]{3}-\d{2}")
# A `generated_declarations` name: an identifier template relative to the generated module's
# namespace, with `<n>` for a number and `<binding>` for the index of a model binding of that
# module's `-- air2lean-models:` record; or `<implementation>`, the `implementation` a binding
# of a generated module names (in any module).
NAME_TEMPLATE = re.compile(r"(?:[A-Za-z_][A-Za-z_0-9]*|<n>|<binding>)(?:[A-Za-z_0-9]|<n>|<binding>)*")
IMPLEMENTATION = "<implementation>"
# Modules under these roots ship with the pinned toolchain; every other module in a theorem's
# dependency graph must be replayed through the kernel (`leanchecker`) before it is trusted.
TOOLCHAIN_ROOTS = ("Init", "Std", "Lean", "Lake")
# Module roots of the lakefile.toml targets: their oleans are trace-checked by Lake.
LAKE_ROOTS = ("ZigLean", "Air2Lean", "Proofs", "tools")
COMPILED_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
REPLAY_FIELDS = {"schema_version", "tool", "tool_sha256", "lean_sha256", "toolchain",
                 "modules", "modules_sha256", "reused", "rejected", "status"}


def is_compiler_axiom(name: str) -> bool:
    # Lean 4.34 nativeEqTrue emits one fresh axiom per tactic invocation.
    name = name.split("::", 1)[-1]
    return name.startswith("Lean.ofReduce") or bool(re.search(
        r"(?:^|\.)_native\.[^.]+\.ax(?:_[0-9]+)*$", name))


WITNESS_FIXTURES = Path("assurance/witness-fixtures.json")


def witness_fixtures(root: Path | None = None) -> list[str]:
    """The registered witness-fixture files (assurance/witness-fixtures.json): test modules whose
    companions (`nonvacuity_witness`, ...) the shipped audit loads next to the shipped claims,
    because they need a fixture (a translated allocator) that ZigLean/Proofs must not import."""
    root = ROOT if root is None else root
    data = json.loads((root / WITNESS_FIXTURES).read_text())
    if not isinstance(data, dict) or set(data) != {"description", "fixtures"} or not isinstance(data["fixtures"], list):
        raise ValueError(f"{WITNESS_FIXTURES}: expected {{description, fixtures: [...]}}")
    files = []
    for entry in data["fixtures"]:
        if not isinstance(entry, dict) or set(entry) != {"file", "reason"} or not all(
                isinstance(entry[k], str) and entry[k] for k in ("file", "reason")):
            raise ValueError(f"{WITNESS_FIXTURES}: each fixture is {{file, reason}}")
        if not (root / entry["file"]).is_file() or entry["file"].split("/")[0] in ("ZigLean", "Proofs"):
            raise ValueError(f"{WITNESS_FIXTURES}: {entry['file']} is not a test source file")
        files.append(entry["file"])
    if files != sorted(set(files)):
        raise ValueError(f"{WITNESS_FIXTURES}: fixtures must be sorted and unique")
    return files


def witness_fixture_inputs(root: Path | None = None) -> tuple[str, dict[str, str]]:
    """Bind the registry and its actual universe source closure, without compiling it."""
    root = ROOT if root is None else root
    files = witness_fixtures(root)
    import theorem_universe  # Lazy: theorem_universe imports this module.
    units, _ = theorem_universe.witness_units(files, root)
    digest = hashlib.sha256((root / WITNESS_FIXTURES).read_bytes())
    for unit in sorted(units, key=lambda u: u.file):
        digest.update(unit.module.encode() + b'\0' + unit.file.encode() + b'\0')
        digest.update((root / unit.file).read_bytes())
        digest.update(b'\0')
    return digest.hexdigest(), {u.module: u.file for u in units}


def verify_witness_closure(imports: dict, sources: dict[str, str]) -> None:
    """Actual import headers must stay inside the precompiled local source closure.
    Source parsing may overapproximate; an omitted imported helper must never become an
    unbound private artifact, including helpers without theorem dependency nodes."""
    if not isinstance(imports, dict) or not set(sources) <= imports.keys():
        raise ValueError('witness fixture has no complete actual import metadata')
    actual = set(imports)
    for module in sources:
        dependencies = imports[module]
        if not isinstance(dependencies, list) or not all(isinstance(d, str) for d in dependencies):
            raise ValueError(f'witness fixture has no complete actual imports: {module}')
        actual.update(dependencies)
    unbound = sorted(m for m in actual if needs_replay(m) and m.split('.')[0] not in LAKE_ROOTS
                     and m not in sources)
    if unbound:
        raise ValueError(f'witness fixture imports outside its bound source closure: {unbound}')


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
    generated_rules(policy)
    for field in POLICY_FIELDS - {"schema_version", "generated_declarations"}:
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


def generated_rules(policy: dict) -> list[tuple[dict, re.Pattern | None]]:
    """The validated `generated_declarations` entries, each with its name pattern (None for
    `<implementation>`). Each entry classifies one kind of declaration the translator emits by
    the premise it stands for; it names no single declaration."""
    rules = policy["generated_declarations"]
    if not isinstance(rules, list):
        raise ValueError("policy generated_declarations must be a list")
    compiled = []
    for entry in rules:
        if (not isinstance(entry, dict) or not {"kind", "name", "premises", "reason"} <= set(entry)
                or not set(entry) <= {"kind", "name", "premises", "reason", "trust"}
                or entry["kind"] not in {"axiom", "opaque"}
                or not isinstance(entry["reason"], str) or not entry["reason"].strip()
                or not isinstance(entry["premises"], list) or not entry["premises"]
                or not all(isinstance(p, str) and PREMISE_ID.fullmatch(p) for p in entry["premises"])
                or not isinstance(entry["name"], str)):
            raise ValueError(f"invalid generated declaration policy: {entry}")
        name = entry["name"]
        if name == IMPLEMENTATION:
            compiled.append((entry, None))
            continue
        # A template without a placeholder would allow one named declaration: that is a
        # `project_axioms`/`project_opaques` entry, not a generated-declaration rule.
        if (not NAME_TEMPLATE.fullmatch(name) or name.count("<binding>") > 1
                or ("<n>" not in name and "<binding>" not in name)):
            raise ValueError(f"invalid generated declaration name template: {name}")
        if "trust" in entry and "<binding>" not in name:
            raise ValueError(f"generated declaration trust needs a binding: {name}")
        pattern = re.escape(name).replace(re.escape("<n>"), "[0-9]+").replace(
            re.escape("<binding>"), "(?P<binding>[0-9]+)")
        compiled.append((entry, re.compile(pattern)))
    return compiled


def module_source(module: str, sources: dict[str, str]) -> str | None:
    """The repository-relative source of a module: `sources` (scripts/theorem_universe.py passes
    every universe unit), else the Lake library path of a Lake module."""
    if module in sources:
        return sources[module]
    if module.split(".")[0] in LAKE_ROOTS:
        return "/".join(module.split(".")) + ".lean"
    return None


_RETRANSLATED = None


def retranslated() -> frozenset:
    """The repository-relative generated modules that scripts/gen-integrity.py retranslates and
    requires to equal fresh translator output (its cases). A file that only looks generated (a
    copied `-- air2lean-profile:` record, a hand-written `Gen.lean`) is not one: gen-integrity
    rejects it as a generated module without a retranslation rule, and this audit never trusts
    its declarations."""
    global _RETRANSLATED
    if _RETRANSLATED is None:
        spec = importlib.util.spec_from_file_location("air2lean_gen_integrity", ROOT / "scripts/gen-integrity.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _RETRANSLATED = frozenset(case.path for case in module.all_cases())
    return _RETRANSLATED


def generated_premises(nodes: dict, policy: dict, sources: dict[str, str], root: Path = ROOT,
                       translated: frozenset | None = None) -> dict[str, list[str]]:
    """Kernel name -> premise IDs of each axiom or opaque that a `generated_declarations` entry
    classifies from the translator's metadata: declared in a generated module that
    scripts/gen-integrity.py retranslates (`translated`, default `retranslated()`; and
    `premise_markers.is_generated`) under the namespace that module's metadata records, or named
    as the implementation of a model binding of such a module. A binding's own premise
    (`extern.premise`, EXT-03) joins the entry's. Everything else stays unclassified, and so a
    violation."""
    rules = generated_rules(policy)
    metadata: dict[str, object] = {}

    def generated(module: str):
        nonlocal translated
        if module not in metadata:
            rel = module_source(module, sources)
            if rel is not None and translated is None:
                translated = retranslated()
            metadata[module] = premise_markers.generated_module(root, rel) if rel in (translated or ()) else None
        return metadata[module]

    def binding_premises(binding: dict, entry: dict) -> list[str] | None:
        if "trust" in entry and (binding.get("trust") != entry["trust"] or binding.get("proof") is not None):
            return None
        extern = binding.get("extern")
        own = [extern["premise"]] if isinstance(extern, dict) and isinstance(extern.get("premise"), str) \
            and PREMISE_ID.fullmatch(extern["premise"]) else []
        return sorted({*entry["premises"], *own})

    pool: dict[str, list[dict]] | None = None

    def implementations() -> dict[str, list[dict]]:
        """Implementation name -> the bindings naming it, over every generated module known."""
        nonlocal pool
        if pool is None:
            pool = {}
            for module in sorted({*sources, *(n["module"] for n in nodes.values())}):
                for binding in getattr(generated(module), "bindings", ()):
                    if isinstance(binding.get("implementation"), str):
                        pool.setdefault(binding["implementation"], []).append(binding)
        return pool

    def premises_of(node: dict, user: str, entry: dict, pattern) -> list[str] | None:
        if pattern is None:
            matches = [p for b in implementations().get(user, ()) if (p := binding_premises(b, entry))]
            return sorted({p for ps in matches for p in ps}) or None
        module = generated(node["module"])
        if module is None:
            return None
        local = user[len(module.namespace) + 1:] if module.namespace else user
        # The source declares it under its recorded namespace: the olean and the checked source agree.
        if (module.namespace and not user.startswith(module.namespace + ".")) or (node["kind"], local) not in module.declared:
            return None
        match = pattern.fullmatch(local)
        if match is None:
            return None
        if "binding" not in pattern.groupindex:
            return sorted(entry["premises"])
        index = int(match["binding"])
        return binding_premises(module.bindings[index], entry) if index < len(module.bindings) else None

    classified: dict[str, list[str]] = {}
    for name, node in nodes.items():
        # Toolchain declarations and reviewed policy entries are classified elsewhere (`classify`).
        if (node["kind"] not in {"axiom", "opaque"} or not needs_replay(node["module"])
                or policy_key(node) in policy["project_opaques"] or policy_key(node) in policy["project_axioms"]):
            continue
        user = node.get("user_name", name)
        for entry, pattern in rules:
            if entry["kind"] == node["kind"] and (premises := premises_of(node, user, entry, pattern)):
                classified[name] = premises
                break
    return classified


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


def is_meta_code(node: dict, reachable: set[str] | None) -> bool:
    """An opaque that is compiled code, not a logical constant, and that no theorem depends on.

    Lean gives a `partial def` and an `initialize`d constant (a tactic implementation, an
    environment extension, a cache) a kernel opaque as a handle, and its meaning through the
    compiler: an unsafe `_unsafe_rec` twin or an `[init]` function (`backing` in the extracted
    graph). Such an opaque is harmless only while no theorem's statement or proof term reaches
    it; the kernel reads it as an arbitrary inhabitant. So the rule is the property, not a name:
    `reachable` (every declaration the theorems depend on) must not contain it, and it carries
    no compiler redirection or extern of its own. `reachable=None` (unknown) never matches."""
    return (reachable is not None and node.get("backing") in {"partial", "init"}
            and node["name"] not in reachable and not node.get("implemented_by")
            and not node.get("extern"))


def classify(node: dict, policy: dict, modules: set[str], generated: dict | None = None,
             reachable: set[str] | None = None) -> tuple[str, str | None]:
    """A node's trust class and its violation reason (None if allowed). `generated` holds the
    premises of the generated declarations (`generated_premises`); `reachable` the declarations
    some theorem depends on (`is_meta_code`)."""
    name, kind = node["name"], node["kind"]
    generated = generated or {}
    if kind == "unresolved":
        return "unresolved", "declaration missing from checked environment"
    if name == "sorryAx":
        return "sorry", "hidden or direct sorry dependency"
    if kind == "axiom":
        if name in STANDARD_AXIOMS:
            return "standard-logical-axiom", None
        if is_compiler_axiom(name):
            return "compiler-proof-axiom", "compiler-dependent proof axiom"
        if policy["project_axioms"].get(policy_key(node)):
            return "allowed-project-axiom", None
        if name in generated:
            return "generated-premise-axiom", None
        return "unexpected-axiom", "axiom absent from explicit project policy"
    if node.get("unsafe"):
        return "unsafe-declaration", "unsafe declaration in logical dependencies"
    if kind == "opaque":
        if policy_key(node) in policy["project_opaques"]:
            return "allowed-project-opaque", None
        if name in generated:
            return "generated-premise-opaque", None
        if is_meta_code(node, reachable):
            return "meta-code-opaque", None
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


def apply_policy(raw: dict, policy: dict, labels: dict | None = None, require_theorems: bool = True,
                 sources: dict[str, str] | None = None) -> dict:
    """`sources`: module -> repository-relative source of non-Lake modules (`module_source`)."""
    if raw.get("schema_version") != 1:
        raise ValueError("unsupported extractor schema")
    modules = set(raw["modules"])
    nodes = {n["name"]: dict(n) for n in raw["nodes"]}
    if len(nodes) != len(raw["nodes"]):
        raise ValueError("duplicate declaration in extracted graph")
    replayed, rejected = replay_record(raw.get("kernel_replay"))
    if not modules <= replayed:
        raise ValueError("kernel replay does not cover the selected modules")
    generated = generated_premises(nodes, policy, sources or {})
    # Everything a theorem's statement or proof term reaches (axiom inventories included).
    reachable: set[str] = set()
    pending = [t["name"] for t in raw["theorems"]] + [a for t in raw["theorems"] for a in t.get("axioms", ())]
    while pending:
        name = pending.pop()
        if name not in reachable:
            reachable.add(name)
            pending.extend(nodes[name]["dependencies"] if name in nodes else ())
    issues: dict[str, dict] = {}
    for name, node in nodes.items():
        trust, problem = classify(node, policy, modules, generated, reachable)
        if trust.startswith("generated-premise-"):
            node["premises"] = generated[name]
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
        # The premises the generated axioms and opaques it reaches stand for (`generated_premises`).
        theorem["declaration_premises"] = sorted({p for n in visited if n in nodes for p in nodes[n].get("premises", ())})
        # The ZigLean runtime modules the closure reaches: claims map them to premises (ORD-06).
        theorem["runtime_modules"] = sorted({nodes[n]["module"] for n in visited if n in nodes and
                                             nodes[n]["module"].split(".")[0] == "ZigLean"})
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


def input_tree_records(root: Path, binaries: bool = False, shared: bool = True) -> list[tuple[Path, str, str]]:
    """One traversal for runtime and search-root bindings, including directory aliases."""
    paths, links = set(), {}

    def visit(path: Path, ancestors: frozenset, binaries: bool):
        if not binaries and path.name.endswith('.hash'):
            return  # Lake's mutable hash metadata is never loaded by Lean.
        if path.is_symlink():
            links[path] = os.readlink(path)
            if not path.exists():
                raise ValueError(f"missing compiled input symlink target: {path}")
        if path.is_dir():
            resolved = path.resolve()
            if resolved in ancestors:
                raise ValueError(f"cyclic compiled input directory: {path}")
            for child in sorted(path.iterdir()):
                visit(child, ancestors | {resolved}, binaries)
        elif path.is_file() and (binaries or (shared and (path.suffix in {".dylib", ".dll"}
                                 or re.search(r"\.so(?:\..+)?$", path.name)))
                                 or path.name.endswith(COMPILED_SUFFIXES)):
            paths.add(path)

    visit(root, frozenset(), binaries)
    return [(path, links.get(path, ""), file_sha256(path) if path in paths else "")
            for path in sorted(paths | links.keys())]


def toolchain_runtime_sha256(toolchain: Path) -> str:
    """Bind Lean's executable stubs, shared runtime and compiled logical/IR inputs."""
    overlays = sorted(name for name, value in os.environ.items() if value and name.startswith(("LD_", "DYLD_")))
    if overlays:
        raise ValueError("toolchain runtime loader overlay: " + ", ".join(overlays))
    for name in ("lean", "leanchecker"):
        if not (toolchain / "bin" / name).is_file():
            raise ValueError(f"missing toolchain executable: {name}")
    digest = hashlib.sha256(b"air2lean-toolchain-runtime-v1\0")
    records = [*input_tree_records(toolchain / "bin", True), *input_tree_records(toolchain / "lib")]
    for path, link, content in sorted(records):
        digest.update(path.relative_to(toolchain).as_posix().encode() + b"\0")
        digest.update(link.encode() + b"\0")
        if content:
            digest.update(content.encode() + b"\0")
    return digest.hexdigest()


def compiled_inputs_sha256(paths: list[Path], toolchain: Path) -> str:
    """Bind all compiled logical/IR inputs exposed by the actual ordered search roots.
    The standard library is separately runtime-bound. Additions and absence are covered,
    so introducing a companion file invalidates the manifest too."""
    digest = hashlib.sha256(b"air2lean-compiled-inputs-v1\0")
    standard = (toolchain / "lib/lean").resolve()
    for root in paths:
        # Lean selects a library by the first matching top-level directory, even if
        # that directory is empty. Its presence can shadow a later valid artifact.
        tops = sorted(p.name for p in root.iterdir() if p.is_dir()) if root.is_dir() else []
        digest.update(json.dumps(tops).encode() + b"\0")
        if root.resolve() == standard:
            digest.update(b"toolchain\0" + display(root).encode() + b"\0")
            if root.is_symlink():
                digest.update(os.readlink(root).encode() + b"\0")
            continue
        digest.update(display(root).encode() + b"\0" + str(root.exists()).encode() + b"\0")
        for path, link, content in input_tree_records(root, shared=False):
            digest.update(path.relative_to(root).as_posix().encode() + b"\0")
            digest.update(link.encode() + b"\0" + content.encode() + b"\0")
    return digest.hexdigest()


def compiled_binding(paths: str, toolchain: Path) -> dict:
    roots = [Path(p).absolute() for p in paths.split(os.pathsep) if p]
    return {"schema_version": 1, "roots": [display(p) for p in roots],
            "sha256": compiled_inputs_sha256(roots, toolchain)}


def verify_compiled_binding(binding: dict, toolchain: Path) -> None:
    if (not isinstance(binding, dict) or binding.get("schema_version") != 1
            or not isinstance(binding.get("roots"), list) or not binding["roots"]
            or not all(isinstance(p, str) and p for p in binding["roots"])):
        raise ValueError("assurance report has no compiled search-root binding")
    if compiled_inputs_sha256([ROOT / p for p in binding["roots"]], toolchain) != binding.get("sha256"):
        raise ValueError("assurance report is stale: compiled search-root inputs changed")


def remove_module_outputs(olean: Path) -> None:
    for suffix in COMPILED_SUFFIXES:
        olean.with_suffix(suffix).unlink(missing_ok=True)


def library_sources_sha256(root: Path | None = None) -> str:
    """One source binding for extractor preparation and every strict reuse admission."""
    import runpy  # Lazy: legacy offline receipts do not need source inventory loading.
    root = ROOT if root is None else root
    dependencies = runpy.run_path(str(Path(__file__).with_name('lean-deps.py')))
    digest = hashlib.sha256(b'air2lean-library-sources-v1\0')
    for path in dependencies['library_sources'](root):
        digest.update(path.relative_to(root).as_posix().encode() + b'\0')
        digest.update(file_sha256(path).encode() + b'\0')
    return digest.hexdigest()


def prepare_tool(root: Path = ROOT, runner=run) -> dict:
    """Always ask Lake to validate dependencies; discard unverified/corrupt output."""
    artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
    lake_trace = artifact.with_suffix(".trace")
    manifest = root / ".lake/assurance/tool-trace.json"
    toolchain = Path(runner(["lake", "env", "printenv", "LEAN_SYSROOT"]).strip())
    context = {
        "schema_version": 1,
        "module": "tools.Assurance",
        "source_sha256": file_sha256(root / "tools/Assurance.lean"),
        "lean_toolchain_sha256": file_sha256(root / "lean-toolchain"),
        "lake_config_sha256": file_sha256(root / "lakefile.toml"),
        "toolchain_runtime_sha256": toolchain_runtime_sha256(toolchain),
        "library_sources_sha256": library_sources_sha256(root),
        "compiled_inputs": compiled_binding(runner(["lake", "env", "printenv", "LEAN_PATH"]).strip(), toolchain),
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
        remove_module_outputs(artifact)
    # --rehash makes Lake recompute file hashes rather than trust cached hash sidecars.
    # Its dependency trace includes compiler identity and imported module build traces.
    runner(["lake", "--rehash", "build", "AssuranceTools"])
    if library_sources_sha256(root) != context['library_sources_sha256']:
        raise ValueError('project library sources changed during extractor preparation')
    context["compiled_inputs"] = compiled_binding(runner(["lake", "env", "printenv", "LEAN_PATH"]).strip(), toolchain)
    trace = {**context, "olean_sha256": file_sha256(artifact),
             "lake_trace_sha256": file_sha256(lake_trace)}
    trace["cache_reused"] = bool(valid and cached.get("olean_sha256") == trace["olean_sha256"]
                                 and cached.get("lake_trace_sha256") == trace["lake_trace_sha256"])
    write_report(manifest, trace)
    return trace


def lean_command(arguments: list[str], lean_path: str | None = None) -> list[str]:
    """Override the search path after Lake configures the pinned toolchain environment."""
    return ["lake", "env", *(["env", "LEAN_PATH=" + lean_path] if lean_path is not None else []),
            "lean", *arguments]


def extract(modules: list[str], build: bool, lean_path: str | None = None,
            *, witnesses: list[str] = ()) -> dict:
    """Audit `modules` and the witness-fixture modules `witnesses` (compiled already, on
    LEAN_PATH) in one environment, so that a shipped claim sees its companion."""
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", m) for m in [*modules, *witnesses]):
        raise ValueError("invalid Lean module name")
    if build:
        # Build each selected module, including newly added modules absent from old manifests.
        run(["lake", "build", *modules])
    tool_trace = prepare_tool()
    toolchain = Path(lake_env("LEAN_SYSROOT"))
    search_path = lake_env("LEAN_PATH") if lean_path is None else lean_path
    verify_library_roots([Path(p).absolute() for p in search_path.split(os.pathsep) if p], toolchain)
    inputs = compiled_binding(search_path, toolchain)
    directory = ROOT / ".lake/assurance"
    directory.mkdir(parents=True, exist_ok=True)
    audited = sorted({*modules, *witnesses})
    driver = "import tools.Assurance\n" + "".join(f"import {m}\n" for m in audited)
    # The extractor reads every statement the elaborator accepted, also under a raised
    # `maxRecDepth` (fsym proofs set 20000): resource limits are not audit checks, a failure stays one.
    driver += ("set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n#assurance_audit ["
               + ", ".join(json.dumps(m) for m in audited) + "]\n")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=directory, delete=False) as handle:
        handle.write(driver)
        path = Path(handle.name)
    try:
        output = run(lean_command([str(path)], lean_path))
    finally:
        path.unlink(missing_ok=True)
    lines = [line[len(MARKER):] for line in output.splitlines() if line.startswith(MARKER)]
    if len(lines) != 1:
        raise ValueError("extractor did not return exactly one environment report")
    raw = json.loads(lines[0])
    if library_sources_sha256() != tool_trace.get('library_sources_sha256'):
        raise ValueError('project library sources changed during assurance extraction')
    verify_compiled_binding(inputs, toolchain)
    if inputs != tool_trace["compiled_inputs"]:
        verify_compiled_binding(tool_trace["compiled_inputs"], toolchain)
    raw["compiled_inputs"] = inputs
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
    # Lean.Util.Path.SearchPath.findWithExt selects the first top-level package root,
    # even when the requested descendant is absent. Never fall through to a stale copy.
    relative = module.replace(".", "/") + ".olean"
    top = module.split(".")[0]
    for directory in lean_path:
        if (directory / top).is_dir() or (directory / (top + ".olean")).exists():
            if (directory / relative).is_file():
                return (directory / relative).resolve(strict=True)
            raise ValueError(f"no compiled module for {module} in selected root {directory}")
    raise ValueError(f"no compiled module for {module}")


def verify_library_roots(paths: list[Path], toolchain: Path) -> None:
    """Private audit paths may not replace the extractor's project or standard libraries.
    Check directory identity and every top-level companion: a file-only olean alias could
    otherwise leave a malicious sibling IR file in the selected library."""
    for name in (*LAKE_ROOTS, *TOOLCHAIN_ROOTS):
        expected = ROOT / '.lake/build/lib/lean' if name in LAKE_ROOTS else toolchain / 'lib/lean'
        selected = next((p for p in paths if (p / name).is_dir() or (p / (name + '.olean')).exists()), None)
        for suffix in ('', *COMPILED_SUFFIXES):
            wanted = expected / (name + suffix)
            found = selected / (name + suffix) if selected is not None else None
            if bool(found and found.exists()) != wanted.exists() or (
                    wanted.exists() and found.resolve(strict=True) != wanted.resolve(strict=True)):
                raise ValueError(f'private audit path shadows trusted library {name}{suffix}')


def display(path: Path) -> str:
    return path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)


def kernel_replay(digests: dict[str, str], toolchain: Path, lean_path: str, cache: Path | None = None,
                  cacheable: frozenset = frozenset(), compiled_sha: str | None = None) -> dict:
    """Re-check every declaration of each module with the toolchain's independent `leanchecker`.

    Imports are loaded from oleans, so the caller passes every non-toolchain module of the
    dependency graph: together they replay the complete closure above the toolchain. `cache`
    (one build only; receipts never use it) holds `cacheable` (Lake-built) modules that already
    passed with the same checker and identical olean bytes. Their imports are Lake-built too, so
    any differing digest among them drops the whole cache."""
    from concurrent.futures import ThreadPoolExecutor  # Lazy: the offline receipt suite has a 32 MiB budget.
    checker = toolchain / "bin/leanchecker"
    checker_sha = file_sha256(checker)
    runtime_sha = toolchain_runtime_sha256(toolchain)
    environment = {**os.environ, "LEAN_PATH": lean_path}
    jobs = max(1, int(os.environ.get("AIR2LEAN_REPLAY_JOBS") or os.environ.get("AIR2LEAN_JOBS")
                      or min(4, os.cpu_count() or 1)))
    try:
        cached = json.loads(cache.read_text()) if cache else {}
    except FileNotFoundError:
        cached = {}
    passed = cached.get("passed", {}) if (cached.get("tool_sha256") == checker_sha
                                         and cached.get("runtime_sha256") == runtime_sha
                                         and cached.get("compiled_inputs_sha256") == compiled_sha) else {}
    if any(passed.get(m, d) != d for m, d in digests.items() if m in cacheable):
        passed = {}  # Another build: a reused module could depend on a changed one.
    modules = sorted(digests)
    reused = [m for m in modules if m in cacheable and passed.get(m) == digests[m]]

    def check(module: str):
        result = subprocess.run([str(checker), module], cwd=ROOT, env=environment, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return None if result.returncode == 0 else {
            "module": module, "output": f"leanchecker exited {result.returncode}\n" + result.stdout[-2000:]}

    with ThreadPoolExecutor(jobs) as pool:
        rejected = [r for r in pool.map(check, sorted(set(modules) - set(reused))) if r is not None]
    if toolchain_runtime_sha256(toolchain) != runtime_sha:
        raise ValueError("toolchain runtime changed during kernel replay")
    if cache:
        failed = {r["module"] for r in rejected}
        passed.update({m: d for m, d in digests.items() if m in cacheable and m not in failed})
        write_report(cache, {"tool_sha256": checker_sha, "runtime_sha256": runtime_sha,
                             "compiled_inputs_sha256": compiled_sha, "passed": passed})
    return {"schema_version": 1, "tool": "leanchecker", "tool_sha256": checker_sha,
            "lean_sha256": file_sha256(toolchain / "bin/lean"),
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "modules": modules, "modules_sha256": modules_digest(modules), "reused": reused,
            "rejected": rejected, "status": "fail" if rejected else "pass"}


def verify_expected_artifacts(expected: dict, paths: list[Path]) -> None:
    """A private compilation must remain the artifact the audit actually loads."""
    for module, (path, digest) in expected.items():
        if locate(module, paths) != path or file_sha256(path) != digest:
            raise ValueError(f'private module {module} changed during its audit')


def cacheable_modules(imports: dict, candidates: list[str], paths: list[Path], toolchain: Path) -> frozenset:
    """Reuse only complete actual import closures confined to Lake and the pinned stdlib.
    Missing/unknown/cyclic metadata or a foreign/shadowed artifact takes fresh replay."""
    if not candidates or not isinstance(imports, dict):
        return frozenset()
    standard, built = (toolchain / 'lib/lean').resolve(), (ROOT / '.lake/build/lib/lean').resolve()
    pending = {}
    for module, dependencies in imports.items():
        if (not isinstance(module, str) or not isinstance(dependencies, list)
                or not all(isinstance(dep, str) for dep in dependencies)):
            continue
        relative = module.replace('.', '/') + '.olean'
        try:
            actual = locate(module, paths)
            if module.split('.')[0] in TOOLCHAIN_ROOTS:
                owned = actual.is_relative_to(standard) and actual == (standard / relative).resolve(strict=True)
            else:
                owned = (module.split('.')[0] in LAKE_ROOTS and actual.is_relative_to(built)
                         and actual == (built / relative).resolve(strict=True)
                         and (ROOT / (module.replace('.', '/') + '.lean')).is_file())
            if owned:
                pending[module] = set(dependencies)
        except (OSError, ValueError):
            continue
    approved = set()
    while pending:
        ready = {module for module, dependencies in pending.items() if dependencies <= approved}
        if not ready:
            break
        approved |= ready
        for module in ready:
            del pending[module]
    return frozenset(approved.intersection(candidates))


def replay_and_freshness(raw: dict, cache: Path | None = None, search_path: str | None = None,
                         *, bound: dict[str, str] | None = None) -> dict:
    """Kernel-replay the audited closure (S1) and bind it to artifact digests and the tree (H1)."""
    toolchain = Path(lake_env("LEAN_SYSROOT")).resolve()
    runtime_sha = toolchain_runtime_sha256(toolchain)
    if raw.get("extractor", {}).get("toolchain_runtime_sha256") != runtime_sha:
        raise ValueError("extractor has no matching toolchain runtime binding")
    sources_sha = library_sources_sha256()
    if raw.get('extractor', {}).get('library_sources_sha256') != sources_sha:
        raise ValueError('extractor has no matching project library source binding')
    witnesses_sha = raw.get('witness_fixtures_sha256')
    if witnesses_sha is not None:
        current_sha, fixture_sources = witness_fixture_inputs()
        if current_sha != witnesses_sha or fixture_sources != bound:
            raise ValueError('witness fixture inputs changed during assurance extraction')
        verify_witness_closure(raw.get('module_imports'), fixture_sources)
    lean_path_text = lake_env("LEAN_PATH") if search_path is None else search_path
    inputs = raw.get("compiled_inputs")
    if inputs != compiled_binding(lean_path_text, toolchain):
        raise ValueError("compiled inputs changed after assurance extraction")
    lean_path = [Path(p).resolve() for p in lean_path_text.split(os.pathsep) if p]
    standard = toolchain / "lib/lean"
    graph_modules = {n["module"] for n in raw["nodes"]}
    for module in sorted(m for m in graph_modules if m and not needs_replay(m)):
        if not locate(module, lean_path).is_relative_to(standard):
            raise ValueError(f"toolchain module {module} is shadowed by a project olean")
    built = (ROOT / ".lake/build/lib/lean").resolve()
    artifacts, lake_modules = [], []
    for module in sorted(set(raw["modules"]) | {m for m in graph_modules if needs_replay(m)}):
        olean = locate(module, lean_path)
        row = {"module": module, "olean": display(olean), "olean_sha256": file_sha256(olean),
               "source": None, "source_sha256": None}
        source = ROOT / (module.replace(".", "/") + ".lean")
        if module.split(".")[0] in LAKE_ROOTS:
            if (not olean.is_relative_to(built) or not source.is_file()
                    or olean != (built / (module.replace('.', '/') + '.olean')).resolve(strict=True)):
                raise ValueError(f'Lake module {module} has no canonical artifact/source binding')
            row.update(source=display(source), source_sha256=file_sha256(source))
            lake_modules.append(module)
        elif module in (bound or {}):  # a witness fixture: bound to its source too
            row.update(source=bound[module], source_sha256=file_sha256(ROOT / bound[module]))
        artifacts.append(row)
    if lake_modules:
        # Fails if any Lake-built olean is stale against its sources (--no-build audits too).
        run(["lake", "--rehash", "build", "--no-build", *lake_modules])
    # Only Lake-owned modules can be reused. Their compiled input boundary is the Lake
    # library (including all companion additions), independent of each private bundle.
    lake_inputs = compiled_inputs_sha256([built], toolchain)
    cacheable = cacheable_modules(raw.get('module_imports'), lake_modules, lean_path, toolchain)
    raw["kernel_replay"] = kernel_replay({r["module"]: r["olean_sha256"] for r in artifacts},
                                         toolchain, lean_path_text, cache, cacheable, lake_inputs)
    for row in artifacts:
        current = locate(row["module"], lean_path)
        if display(current) != row["olean"] or file_sha256(current) != row["olean_sha256"]:
            raise ValueError(f"module resolution changed during kernel replay: {row['module']}")
    if toolchain_runtime_sha256(toolchain) != runtime_sha:
        raise ValueError("toolchain runtime changed during assurance extraction")
    if library_sources_sha256() != sources_sha:
        raise ValueError('project library sources changed during kernel replay')
    if witnesses_sha is not None and witness_fixture_inputs()[0] != witnesses_sha:
        raise ValueError('witness fixture inputs changed during kernel replay')
    verify_compiled_binding(inputs, toolchain)
    return {"revision": git_revision(), "lake_trace_check": {"modules": lake_modules, "status": "up-to-date"},
            "toolchain_runtime_sha256": runtime_sha, "compiled_inputs": inputs, "artifacts": artifacts,
            **({'witness_fixtures_sha256': witnesses_sha} if witnesses_sha is not None else {})}


def verify_artifacts(report: dict, *, require_witnesses: bool = False) -> int:
    """Recompute every source/olean binding and check the recorded Lake trace validation.
    A content cache must additionally match its complete current input digest before using
    this lower-level check; receipts use verify_fresh, which also requires the same revision."""
    if require_witnesses or report.get('scope') == 'all-shipped-modules' or report.get('witness_modules') or (
                             isinstance(report.get("freshness"), dict)
                             and "toolchain_runtime_sha256" in report["freshness"]):
        with artifact_batch() as verify:
            return verify(report, require_witnesses=require_witnesses)
    return _verify_artifact_rows(report)


def _verify_artifact_rows(report: dict) -> int:
    freshness = report.get("freshness")
    if not isinstance(freshness, dict) or not isinstance(freshness.get("artifacts"), list):
        raise ValueError("assurance report carries no freshness binding; re-run scripts/assumptions.py")
    if (freshness.get("lake_trace_check") or {}).get("status") != "up-to-date":
        raise ValueError("assurance report has no passing Lake trace check")
    for row in freshness["artifacts"]:
        for kind in ("olean", "source"):
            path = row[kind] and (ROOT / row[kind] if not Path(row[kind]).is_absolute() else Path(row[kind]))
            if path and (not path.is_file() or file_sha256(path) != row[kind + "_sha256"]):
                raise ValueError(f"assurance report is stale: {row['module']} {kind} changed")
    return len(freshness["artifacts"])


@contextmanager
def artifact_batch():
    """Verify runtime-bound reports with fresh toolchain hashes bracketing this batch.
    The yielded verifier cannot be used after the context closes; no digest is memoized."""
    def current_runtime():
        try:
            return toolchain_runtime_sha256(Path(lake_env("LEAN_SYSROOT")))
        except (OSError, RuntimeError) as error:
            raise ValueError(f"cannot verify toolchain runtime: {error}") from error

    runtime, active = current_runtime(), True
    toolchain = Path(lake_env("LEAN_SYSROOT"))
    compiled_bindings = {}
    source_binding = None
    witness_binding = None
    witness_sources = None

    def verify(report, *, require_witnesses: bool = False):
        nonlocal source_binding, witness_binding, witness_sources
        if not active:
            raise ValueError("artifact verification batch is closed")
        freshness = report.get("freshness")
        recorded = freshness.get("toolchain_runtime_sha256") if isinstance(freshness, dict) else None
        if not isinstance(recorded, str) or not re.fullmatch(r"[0-9a-f]{64}", recorded):
            raise ValueError("assurance report has no valid toolchain runtime binding")
        extractor = report.get("extractor")
        if extractor is not None and (not isinstance(extractor, dict)
                                      or extractor.get("toolchain_runtime_sha256") != recorded):
            raise ValueError("assurance extractor and replay have different toolchain runtime bindings")
        if runtime != recorded:
            raise ValueError("assurance report is stale: toolchain runtime changed")
        if extractor is not None and 'library_sources_sha256' in extractor:
            binding = extractor['library_sources_sha256']
            if not isinstance(binding, str) or not re.fullmatch(r'[0-9a-f]{64}', binding):
                raise ValueError('assurance extractor has no valid library source binding')
            if source_binding is None:
                source_binding = library_sources_sha256()
            if source_binding != binding:
                raise ValueError('assurance report is stale: project library sources changed')
        if (require_witnesses or report.get('scope') == 'all-shipped-modules' or report.get('witness_modules')) and not freshness.get(
                'witness_fixtures_sha256'):
            raise ValueError('assurance report has no witness fixture input binding')
        if 'witness_fixtures_sha256' in freshness:
            binding = freshness['witness_fixtures_sha256']
            if not isinstance(binding, str) or not re.fullmatch(r'[0-9a-f]{64}', binding):
                raise ValueError('assurance report has no valid witness fixture input binding')
            if witness_binding is None:
                witness_binding, witness_sources = witness_fixture_inputs()
            if witness_binding != binding:
                raise ValueError('assurance report is stale: witness fixture inputs changed')
            verify_witness_closure(report.get('module_imports'), witness_sources)
            rows = {row['module']: row for row in freshness['artifacts']}
            if any(module not in rows or rows[module].get('source') != source
                   for module, source in witness_sources.items()):
                raise ValueError('assurance report has no complete witness source bindings')
        for section in (freshness, extractor or {}):
            if "compiled_inputs" in section:
                binding = section["compiled_inputs"]
                key = json.dumps(binding, sort_keys=True)
                if key not in compiled_bindings:
                    verify_compiled_binding(binding, toolchain)
                    compiled_bindings[key] = binding
        return _verify_artifact_rows(report)

    try:
        yield verify
        for binding in compiled_bindings.values():
            verify_compiled_binding(binding, toolchain)
        if source_binding is not None and library_sources_sha256() != source_binding:
            raise ValueError('project library sources changed during artifact verification')
        if witness_binding is not None and witness_fixture_inputs()[0] != witness_binding:
            raise ValueError('witness fixture inputs changed during artifact verification')
        if current_runtime() != runtime:
            raise ValueError("toolchain runtime changed during artifact verification")
    finally:
        active = False


def verify_fresh(report: dict, allow_dirty: bool = False, *, require_witnesses: bool = False) -> dict:
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
    artifacts = verify_artifacts(report, require_witnesses=require_witnesses)
    return {"head": current["head"], "tracked_dirty": dirty, "dirty_allowed": bool(dirty and allow_dirty),
            "artifacts": artifacts}


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


def compile_witness_fixtures(build: bool, lean_path: str | None = None) -> tuple[dict, list[Path], dict]:
    """Compile registered fixtures through the same private path and artifact checks."""
    files = witness_fixtures()
    if not files:
        return {}, [], {}
    import theorem_universe  # Lazy: theorem_universe imports this module.
    return theorem_universe.compile_witness_fixtures(
        files, ROOT / ".lake/assurance/witness-fixtures", build, lean_path)


def split_witnesses(report: dict, modules: list[str], witnesses: list[str]) -> None:
    """Keep the audit's scope the requested modules: the fixtures' theorems (checked by the same
    policy and kernel replay) go to `witness_theorems`, where claims.py finds companions."""
    report["modules"] = modules
    report["witness_modules"] = witnesses
    report["witness_theorems"] = [t for t in report["theorems"] if t["module"] in witnesses]
    report["theorems"] = [t for t in report["theorems"] if t["module"] not in witnesses]
    report["theorem_count"] = len(report["theorems"])


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
    parser.add_argument("--sources", type=Path,
                        help="JSON object: module -> repository-relative source of each non-Lake module "
                             "(scripts/theorem_universe.py), for the generated-declaration classification")
    parser.add_argument("--lean-path", help="exact module search path, applied after Lake's environment setup")
    args = parser.parse_args()
    try:
        policy = load_policy(args.policy)
        sources = json.loads(args.sources.read_text()) if args.sources else {}
        if not isinstance(sources, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                                    for k, v in sources.items()):
            raise ValueError("--sources must map module names to source paths")
        labels = float_semantics().load_registry(args.float_semantics, root=ROOT)
        modules = sorted(set(args.module)) if args.module else shipped_modules()
        witness_inputs = None if args.module else witness_fixture_inputs()[0]
        fixtures, paths, expected = ({}, [], {}) if args.module else compile_witness_fixtures(
            not args.no_build, args.lean_path)
        lean_path = os.pathsep.join(map(str, paths)) if paths else args.lean_path
        witnesses = sorted(m for m in fixtures if m not in modules)
        raw = extract(modules, not args.no_build, lean_path, witnesses=witnesses)
        if raw["modules"] != sorted({*modules, *witnesses}):
            raise ValueError("extractor scope differs from requested module inventory")
        if witness_inputs is not None:
            raw['witness_fixtures_sha256'] = witness_inputs
        freshness = replay_and_freshness(raw, args.replay_cache, lean_path, bound=fixtures)
        verify_expected_artifacts(expected, paths)
        report = apply_policy(raw, policy, labels, not args.allow_no_theorems, {**fixtures, **sources})
        split_witnesses(report, modules, witnesses)
        report["freshness"] = freshness
        report["extractor"] = raw["extractor"]
        report['module_imports'] = raw['module_imports']
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
