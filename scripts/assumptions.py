#!/usr/bin/env python3
"""Extract compiled Lean dependencies and apply the explicit assurance policy."""
from __future__ import annotations

import argparse
import contextlib
import fcntl
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


def witness_fixtures(root: Path = ROOT) -> list[str]:
    """The registered witness-fixture files (assurance/witness-fixtures.json): test modules whose
    companions (`nonvacuity_witness`, ...) the shipped audit loads next to the shipped claims,
    because they need a fixture (a translated allocator) that ZigLean/Proofs must not import."""
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
            "module_imports": raw.get("module_imports"),
            "kernel_replay": raw["kernel_replay"],
            "theorems": sorted(theorems, key=lambda t: t["name"]),
            "project_declarations": raw.get("project_declarations", []),
            "nodes": sorted(nodes.values(), key=lambda n: n["name"]),
            "float_semantics": float_summary,
            "violations": sorted(issues.values(), key=lambda n: n["name"])}


def run(command: list[str], *, root: Path | None = None) -> str:
    result = subprocess.run(command, cwd=ROOT if root is None else root, text=True, capture_output=True)
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


def input_tree_records(root: Path, binaries: bool = False, *,
                       suffixes: tuple[str, ...] | None = None,
                       content_exclusions=()) -> list[tuple[Path, str, str]]:
    """Selected input bytes and alias identities, using one traversal for all input sets."""
    paths, links = set(), {}

    def visit(path: Path, ancestors: frozenset):
        if not binaries and path.name.endswith('.hash') and not path.is_dir():
            return  # Lake's mutable hash metadata is not loaded by Lean.
        if path.is_symlink():
            links[path] = os.readlink(path)
            if not path.exists():
                raise ValueError(f"missing compiled input symlink target: {path}")
        if path.is_dir():
            resolved = path.resolve()
            if resolved in ancestors:
                raise ValueError(f"cyclic compiled input directory: {path}")
            for child in sorted(path.iterdir()):
                visit(child, ancestors | {resolved})
        elif path.is_file():
            selected = (path.name.endswith(suffixes) if suffixes is not None else
                        binaries or path.suffix in {'.dylib', '.dll'}
                        or re.search(r'\.so(?:\..+)?$', path.name)
                        or path.name.endswith(COMPILED_SUFFIXES))
            if selected:
                paths.add(path)

    visit(root, frozenset())
    return [(path, links.get(path, ''), file_sha256(path)
             if path in paths and path not in content_exclusions else '')
            for path in sorted(paths | links.keys())]


def library_roots(root: Path) -> set[str]:
    import runpy  # Lazy: policy-only users need no source inventory.
    dependencies = runpy.run_path(str(Path(__file__).with_name('lean-deps.py')))
    roots = dependencies['lib_roots'](root, strict_sources=True)
    if not roots:
        raise ValueError('no configured Lake library sources')
    return roots


def library_source_inputs(root: Path) -> list[list[str]]:
    """Configured source selection; all content/link records use input_tree_records."""
    roots = library_roots(root)
    records = []
    for name in sorted(roots):
        if not name or '/' in name or '\\' in name:
            raise ValueError(f'invalid configured Lake library root: {name!r}')
        selected = [record for path in (root / name, root / (name + '.lean'))
                    for record in input_tree_records(path, suffixes=('.lean',))]
        if not any(content for _, _, content in selected):
            raise ValueError(f'Lake library {name} has no Lean sources')
        records.extend(selected)
    for name in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json'):
        path = root / name
        if name == 'lake-manifest.json' and not path.exists() and not path.is_symlink():
            records.append((path, '', ''))  # Explicit absent-state binding.
        elif not path.is_file():
            raise ValueError(f'missing library source configuration: {path}')
        else:
            records.extend(input_tree_records(path, binaries=True))
    return [[path.relative_to(root).as_posix(), link, content]
            for path, link, content in sorted(records)]


def library_compiled_inputs(root: Path) -> list:
    """The existing cache's canonical Lake inputs, including loaded companions and absence."""
    built = root / '.lake/build/lib/lean'
    records = []
    for name in sorted(library_roots(root)):
        for suffix in ('', *COMPILED_SUFFIXES):
            selected = built / (name + suffix)
            records.append([str(selected), str(selected.resolve()), selected.exists(),
                            [[str(path), link, content]
                             for path, link, content in input_tree_records(selected)]])
    return records


def toolchain_runtime_sha256(toolchain: Path) -> str:
    """Hash executable stubs, shared runtime and installed logical/IR inputs freshly."""
    overlays = sorted(name for name, value in os.environ.items()
                      if value and name.startswith(('LD_', 'DYLD_')))
    if overlays:
        raise ValueError('toolchain runtime loader overlay: ' + ', '.join(overlays))
    for name in ('lean', 'leanchecker'):
        if not (toolchain / 'bin' / name).is_file():
            raise ValueError(f'missing toolchain executable: {name}')
    if not (toolchain / 'lib').is_dir():
        raise ValueError('missing toolchain library directory')
    digest = hashlib.sha256(b'air2lean-toolchain-runtime-v1\0')
    records = [*input_tree_records(toolchain / 'bin', True),
               *input_tree_records(toolchain / 'lib')]
    for path, link, content in sorted(records):
        digest.update(path.relative_to(toolchain).as_posix().encode() + b'\0')
        digest.update(link.encode() + b'\0')
        if content:
            digest.update(content.encode() + b'\0')
    return digest.hexdigest()


def lean_path_binding(root: Path, value: str, *, mutable_outputs=()) -> dict:
    """One ordered-root binding for caller inputs and compiler-owned Unit lookup."""
    entries = value.split(os.pathsep)
    if any(not entry for entry in entries):
        raise ValueError('empty root in caller LEAN_PATH')
    paths = [(root / entry).absolute() for entry in entries]
    mutable_outputs = {path.absolute() for path in mutable_outputs}
    digest = hashlib.sha256(b'air2lean-caller-lean-path-v1\0')
    for path in paths:
        if path.exists() and not path.is_dir():
            raise ValueError(f'caller LEAN_PATH root is not a directory: {path}')
        # An empty top-level directory can select this root ahead of a later library.
        tops = sorted(p.name for p in path.iterdir() if p.is_dir()) if path.is_dir() else []
        identity = {'path': str(path), 'resolved': str(path.resolve()),
                    'exists': path.exists(), 'top_level': tops,
                    'links': [[str(part), os.readlink(part)] for part in (path, *path.parents)
                              if part.is_symlink()]}
        digest.update(json.dumps(identity, sort_keys=True).encode() + b'\0')
        for item, link, content in input_tree_records(
                path, **({'content_exclusions': mutable_outputs} if mutable_outputs else {})):
            if item in mutable_outputs:
                if link:
                    raise ValueError(f'compiler-owned canonical output is an alias: {item}')
                continue  # Exact prederived output slots, never a shared library subtree.
            digest.update(item.relative_to(path).as_posix().encode() + b'\0')
            digest.update(link.encode() + b'\0' + content.encode() + b'\0')
    return {'roots': list(map(str, paths)), 'sha256': digest.hexdigest()}


def caller_lean_path_binding(root: Path) -> dict | None:
    """Bind supported private-library inputs without permitting a sysroot replacement."""
    if os.environ.get('LEAN_SYSROOT'):
        raise ValueError('unsupported caller LEAN_SYSROOT overlay')
    value = os.environ.get('LEAN_PATH')
    return lean_path_binding(root, value) if value else None


def verify_extractor_inputs(trace: dict, root: Path, stage: str) -> None:
    if caller_lean_path_binding(root) != trace['caller_lean_path']:
        raise ValueError(f'caller LEAN_PATH changed during extractor {stage}')
    if toolchain_runtime_sha256(Path(trace['lean_sysroot'])) != trace['toolchain_runtime_sha256']:
        raise ValueError(f'toolchain runtime changed during extractor {stage}')
    if library_source_inputs(root) != trace['library_source_inputs']:
        raise ValueError(f'project library sources changed during extractor {stage}')


@contextlib.contextmanager
def prepared_tool(root: Path = ROOT, runner=None):
    """Yield the extractor's trace while holding the worktree's extractor lock.

    Every assumptions.py invocation in one worktree shares the extractor olean, and preparing it
    may unlink and rebuild it. The exclusive lock covers preparation and the caller's run that
    imports the olean (the `with` body), so no other invocation changes the olean under it.
    A lock or IO error raises."""
    root = root.resolve()
    lock = root / ".lake/assurance/tool.lock"
    lock.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(lock, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)  # Released when the descriptor closes.
        yield prepare_tool(root, runner if runner is not None else lambda command: run(command, root=root))
    finally:
        os.close(descriptor)


def prepare_tool(root: Path, runner) -> dict:
    """Always ask Lake to validate dependencies; discard unverified/corrupt output.
    Only `prepared_tool` calls this, under the extractor lock."""
    artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
    lake_trace = artifact.with_suffix(".trace")
    caller_path = caller_lean_path_binding(root)
    sysroot = runner(["lake", "env", "printenv", "LEAN_SYSROOT"]).strip()
    if not sysroot:
        raise ValueError('empty LEAN_SYSROOT from Lake')
    toolchain = Path(sysroot)
    if not toolchain.is_absolute():
        raise ValueError('nonabsolute LEAN_SYSROOT from Lake')
    sources = library_source_inputs(root)
    manifest_path = root / 'lake-manifest.json'
    context = {
        "schema_version": 1,
        "module": "tools.Assurance",
        "source_sha256": file_sha256(root / "tools/Assurance.lean"),
        "lean_toolchain_sha256": file_sha256(root / "lean-toolchain"),
        "lake_config_sha256": file_sha256(root / "lakefile.toml"),
        "lake_manifest_sha256": file_sha256(manifest_path) if manifest_path.is_file() else None,
        "lean_sysroot": str(toolchain),
        "toolchain_runtime_sha256": toolchain_runtime_sha256(toolchain),
        "caller_lean_path": caller_path,
    }
    # One record per context: invocations with different contexts keep their own records
    # instead of invalidating each other's.
    key = hashlib.sha256(json.dumps(context, sort_keys=True).encode()).hexdigest()
    manifest = root / ".lake/assurance/tool-traces" / f"{key}.json"
    try:
        cached = json.loads(manifest.read_text())
    except (FileNotFoundError, ValueError):
        cached = {}  # No or a corrupt record for this context: Lake rebuilds below.
    artifact_valid = (isinstance(cached, dict) and all(k in cached and cached[k] == v for k, v in context.items())
             and artifact.is_file() and lake_trace.is_file()
             and cached.get("olean_sha256") == file_sha256(artifact)
             and cached.get("lake_trace_sha256") == file_sha256(lake_trace))
    valid = artifact_valid and cached.get('library_source_inputs') == sources
    if not artifact_valid:
        # Lake must rebuild when output or its independently recorded identity is missing,
        # corrupt, or from a different extractor source, release pin, or configuration.
        artifact.unlink(missing_ok=True)
    # --rehash makes Lake recompute file hashes rather than trust cached hash sidecars.
    # Its dependency trace includes compiler identity and imported module build traces.
    runner(["lake", "--rehash", "build", "AssuranceTools"])
    verify_extractor_inputs({**context, 'library_source_inputs': sources}, root, 'preparation')
    trace = {**context, "library_source_inputs": sources, "olean_sha256": file_sha256(artifact),
             "lake_trace_sha256": file_sha256(lake_trace)}
    trace["cache_reused"] = bool(valid and cached.get("olean_sha256") == trace["olean_sha256"]
                                 and cached.get("lake_trace_sha256") == trace["lake_trace_sha256"])
    write_report(manifest, trace)
    return trace


def framework_runtime_types() -> tuple[str, ...]:
    """The existing framework gate's canonical computation families, without a second list."""
    spec = importlib.util.spec_from_file_location("air2lean_proof_framework", ROOT / "scripts/proof-framework.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.PROGRAM_TYPES


def lean_command(arguments: list[str], lean_path: str) -> list[str]:
    """Apply an already resolved lookup path AFTER Lake installs its environment."""
    return ['lake', 'env', 'env', 'LEAN_PATH=' + lean_path, 'lean', *arguments]


def extract(modules: list[str], build: bool, witnesses: list[str] = (), *,
            all_declarations: bool = False, root: Path | None = None,
            lean_path: str | None = None) -> dict:
    """Audit `modules` and the witness-fixture modules `witnesses` (compiled already, on
    LEAN_PATH) in one environment, so that a shipped claim sees its companion."""
    root = (ROOT if root is None else root).resolve()
    runner = lambda command: run(command, root=root)
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", m) for m in [*modules, *witnesses]):
        raise ValueError("invalid Lean module name")
    if build:
        # Build each selected module, including newly added modules absent from old manifests.
        runner(["lake", "build", *modules])
    directory = root / ".lake/assurance"
    directory.mkdir(parents=True, exist_ok=True)
    audited = sorted({*modules, *witnesses})
    driver = "import tools.Assurance\n" + "".join(f"import {m}\n" for m in audited)
    # The extractor reads every statement the elaborator accepted, also under a raised
    # `maxRecDepth` (fsym proofs set 20000): resource limits are not audit checks, a failure stays one.
    driver += "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
    if all_declarations:
        driver += "set_option air2lean.assurance.allDeclarations true\n"
        # Resolve every canonical family in the SAME protected driver/environment. A renamed
        # family must fail, even when no selected declaration happens to reference its old name.
        driver += "".join(f"#check _root_.{name}\n" for name in framework_runtime_types())
    driver += ("#assurance_audit ["
               + ", ".join(json.dumps(m) for m in audited) + "]\n")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=directory, delete=False) as handle:
        handle.write(driver)
        path = Path(handle.name)
    try:
        with prepared_tool(root, runner) as tool_trace:  # The run imports the olean the trace records.
            binding = lean_path_binding(root, lean_path) if lean_path is not None else None
            output = runner(lean_command([str(path)], lean_path) if lean_path is not None else
                            ["lake", "env", "lean", str(path)])
            if binding is not None and lean_path_binding(root, lean_path) != binding:
                raise ValueError('compiled Unit lookup inputs changed during extraction')
    finally:
        path.unlink(missing_ok=True)
    verify_extractor_inputs(tool_trace, root, 'extraction')
    lines = [line[len(MARKER):] for line in output.splitlines() if line.startswith(MARKER)]
    if len(lines) != 1:
        raise ValueError("extractor did not return exactly one environment report")
    raw = json.loads(lines[0])
    raw["extractor"] = tool_trace
    return raw


def framework_candidates(raw: dict) -> dict:
    """Conservative candidate evidence over the existing checked declaration graph.

    These are the resolved computation-family heads of proof-framework.py's PROGRAM_TYPE,
    not declaration-name exceptions. A fixed point propagates their occurrence through the
    original kernel dependencies. Absence of a witness NEVER grants an ordinary-data exemption.
    """
    runtime_types = framework_runtime_types()
    roots = raw["selected_declaration_roots"]
    evidence = raw["selected_declaration_evidence"]
    if (not isinstance(roots, list) or not all(isinstance(n, str) for n in roots)
            or len(roots) != len(set(roots)) or not isinstance(evidence, list)):
        raise ValueError("invalid framework selected-declaration inventory")
    if [row.get("name") for row in evidence if isinstance(row, dict)] != roots or len(evidence) != len(roots):
        raise ValueError("framework evidence differs from exact selected-declaration roots")
    nodes = {node["name"]: node for node in raw["nodes"]}
    if len(nodes) != len(raw["nodes"]):
        raise ValueError("duplicate declaration identity in framework graph")
    reverse = {name: [] for name in nodes}
    unknown = 1 << len(runtime_types)
    masks = {name: ((1 << runtime_types.index(name)) if name in runtime_types else 0)
             | (unknown if node["kind"] in ("unresolved", "opaque", "axiom")
                or node.get("implemented_by") or node.get("extern") else 0)
             for name, node in nodes.items()}
    for name, node in nodes.items():
        for dependency in node["dependencies"]:
            if dependency not in nodes:
                raise ValueError(f"incomplete framework graph: {name} -> {dependency}")
            reverse[dependency].append(name)
    pending = [name for name, mask in masks.items() if mask]
    queued = set(pending)
    while pending:
        name = pending.pop()
        queued.remove(name)
        for parent in reverse[name]:
            combined = masks[parent] | masks[name]
            if combined != masks[parent]:
                masks[parent] = combined
                if parent not in queued:
                    pending.append(parent)
                    queued.add(parent)
    # Each bit only grows once per node, including cycles; no in-progress state means ordinary.
    records = []
    for original in evidence:
        name = original["name"]
        node = nodes.get(name)
        if (node is None or original.get("module") != node["module"]
                or original.get("kind") != node["kind"] or node["module"] not in raw["modules"]):
            raise ValueError(f"framework evidence has a different declaration identity: {name}")
        prop = original.get("prop_valued")
        if prop is not None and type(prop) is not bool:
            raise ValueError(f"invalid framework result-sort evidence: {name}")
        fingerprint = original.get("kernel_fingerprint")
        if not isinstance(fingerprint, str) or not re.fullmatch(r"[0-9a-f]{32}", fingerprint):
            raise ValueError(f"missing framework kernel fingerprint: {name}")
        for field in ("original_type_constants", "original_body_constants"):
            values = original.get(field)
            if (not isinstance(values, list) or not all(isinstance(n, str) for n in values)
                    or len(values) != len(set(values)) or not set(values) <= set(node["dependencies"])):
                raise ValueError(f"invalid framework {field}: {name}")
        programs = [runtime for bit, runtime in enumerate(runtime_types) if masks[name] & (1 << bit)]
        definition = node["kind"] in ("definition", "opaque", "inductive")
        records.append({**original, "program_dependencies": programs,
                        "unresolved_dependency": bool(masks[name] & unknown),
                        "verdict": "candidate" if definition and prop is True and programs else "unknown",
                        "ordinary_exemption": False})
    return {"scope": "selected-modules-only", "phase": "conservative-candidate-evidence",
            "complete": False, "runtime_types": list(runtime_types), "declarations": records,
            "ordinary_exemptions": []}


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
    top = module.split('.')[0]
    for directory in lean_path:
        if (directory / top).is_dir() or (directory / (top + '.olean')).exists():
            if (directory / relative).is_file():
                return directory / relative
            raise ValueError(f"no compiled module for {module} in selected library {directory}")
    raise ValueError(f"no compiled module for {module}")


def display(path: Path) -> str:
    return path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)


def stage_jobs(stage_variable: str) -> int:
    """Workers of one stage: its own override, else the budget build-guard published (`AIR2LEAN_JOBS`),
    else `min(4, cpus)`."""
    value = os.environ.get(stage_variable) or os.environ.get("AIR2LEAN_JOBS")
    return max(1, int(value) if value else min(4, os.cpu_count() or 1))


def kernel_replay(digests: dict[str, str], toolchain: Path, lean_path: str, cache: Path | None = None,
                  cacheable: frozenset = frozenset(), *, expected_runtime: str | None = None,
                  compiled_inputs_sha256: str | None = None, validate_inputs=None) -> dict:
    """Re-check every declaration of each module with the toolchain's independent `leanchecker`.

    Imports are loaded from oleans, so the caller passes every non-toolchain module of the
    dependency graph: together they replay the complete closure above the toolchain. `cache`
    (one build only; receipts never use it) holds `cacheable` (Lake-built) modules that already
    passed with the same checker, installed runtime inputs and identical olean bytes. Any
    differing cacheable-module digest drops the whole cache. The caller still selects cacheable
    modules; this runtime binding does not authenticate project/private import closures.
    Several audits of one build may share `cache` at once (scripts/fixture-checks.py's run): each
    cacheable module is checked under a claim (`<cache>.d/<module>.lock`), the cache is read
    again under it and a pass is merged in at once, so concurrent audits replay each module once
    between them. A pass is merged in only while the compiled inputs are unchanged, and a replay
    that merged passes in and then fails (a changed runtime or input) removes the cache (those
    passes may come from either side of the change)."""
    from concurrent.futures import ThreadPoolExecutor  # Lazy: the offline receipt suite has a 32 MiB budget.
    checker = toolchain / "bin/leanchecker"
    checker_sha = file_sha256(checker)
    runtime_sha = toolchain_runtime_sha256(toolchain)
    if expected_runtime is not None and runtime_sha != expected_runtime:
        raise ValueError('toolchain runtime changed between extraction and replay')
    environment = {**os.environ, "LEAN_PATH": lean_path}
    jobs = stage_jobs("AIR2LEAN_REPLAY_JOBS")

    def load() -> dict:
        """The cache's passes, if they are of this checker and runtime and agree with every
        cacheable digest here; otherwise none (another build: a reused module could depend on a
        changed one)."""
        try:
            cached = json.loads(cache.read_text())
        except FileNotFoundError:
            return {}
        passed = (cached.get("passed", {}) if cached.get("tool_sha256") == checker_sha
                  and cached.get("toolchain_runtime_sha256") == runtime_sha
                  and cached.get("compiled_inputs_sha256") == compiled_inputs_sha256 else {})
        if any(passed.get(m, d) != d for m, d in digests.items() if m in cacheable):
            passed = {}  # Another build: a reused module could depend on a changed one.
        return passed

    @contextlib.contextmanager
    def locked(path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)  # Released when the descriptor closes.
            yield
        finally:
            os.close(descriptor)

    def run_checker(module: str):
        result = subprocess.run([str(checker), module], cwd=ROOT, env=environment, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return None if result.returncode == 0 else {
            "module": module, "output": f"leanchecker exited {result.returncode}\n" + result.stdout[-2000:]}

    def check(module: str):
        """(reused, rejection or None)."""
        if not cache or module not in cacheable:
            return False, run_checker(module)
        claims = cache.with_name(cache.name + ".d")
        with locked(claims / (module + ".lock")):
            if load().get(module) == digests[module]:
                return True, None
            rejection = run_checker(module)
            if rejection is None:
                with locked(claims / "cache.lock"):
                    if validate_inputs is not None:
                        validate_inputs()  # No cache publication from a changed input batch.
                    passed = load()
                    passed[module] = digests[module]
                    write_report(cache, {"tool_sha256": checker_sha, "toolchain_runtime_sha256": runtime_sha,
                                         "compiled_inputs_sha256": compiled_inputs_sha256,
                                         "passed": passed})
                    published.append(module)
            return False, rejection

    modules, published = sorted(digests), []
    try:
        with ThreadPoolExecutor(jobs) as pool:
            results = dict(zip(modules, pool.map(check, modules)))
        if toolchain_runtime_sha256(toolchain) != runtime_sha:
            raise ValueError('toolchain runtime changed during kernel replay')
        if validate_inputs is not None:
            validate_inputs()  # No passing result from a changed input batch.
    except BaseException:
        if published:  # passes this replay merged in may come from the changed runtime or inputs
            cache.unlink(missing_ok=True)
        raise
    reused = [m for m in modules if results[m][0]]
    rejected = [r for _, r in results.values() if r is not None]
    return {"schema_version": 1, "tool": "leanchecker", "tool_sha256": checker_sha,
            "lean_sha256": file_sha256(toolchain / "bin/lean"),
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "modules": modules, "modules_sha256": modules_digest(modules), "reused": reused,
            "rejected": rejected, "status": "fail" if rejected else "pass"}


def cacheable_modules(imports: dict, candidates: list[str], paths: list[Path], toolchain: Path) -> frozenset:
    """Authenticate the existing cache's complete canonical Lake/stdlib import closure.

    Missing, IR-only, cyclic, shadowed or private/external inputs take fresh replay.
    Recovered from the preserved Task04 eligibility rule; no second cache is introduced.
    """
    if not candidates or not isinstance(imports, dict):
        return frozenset()
    standard, built = (toolchain / 'lib/lean').resolve(), (ROOT / '.lake/build/lib/lean').resolve()
    pending, seen, required = {}, set(), list(candidates)
    while required:
        module = required.pop()
        if module in seen:
            continue
        seen.add(module)
        dependencies = imports.get(module)
        if (not isinstance(module, str) or not isinstance(dependencies, list)
                or not all(isinstance(dep, str) for dep in dependencies)):
            continue
        required.extend(dependencies)
        relative = module.replace('.', '/') + '.olean'
        try:
            actual = locate(module, paths).resolve(strict=True)
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


def replay_and_freshness(raw: dict, cache: Path | None = None, bound: dict[str, str] | None = None,
                         *, compiled_units: dict | None = None) -> dict:
    """Kernel-replay the audited closure (S1) and bind it to artifact digests and the tree (H1)."""
    toolchain = Path(lake_env("LEAN_SYSROOT")).resolve()
    extractor = raw.get('extractor')
    if not isinstance(extractor, dict):
        raise ValueError('assurance extraction carries no toolchain runtime binding')
    runtime_sha = extractor.get('toolchain_runtime_sha256')
    if (not isinstance(runtime_sha, str) or not re.fullmatch(r'[0-9a-f]{64}', runtime_sha)
            or not isinstance(extractor.get('lean_sysroot'), str)
            or not Path(extractor['lean_sysroot']).is_absolute()
            or Path(extractor['lean_sysroot']).resolve() != toolchain):
        raise ValueError('assurance extraction carries no matching toolchain runtime binding')
    if compiled_units is not None:
        import theorem_universe
        theorem_universe.verify_compilation(compiled_units)
    lean_path_text = lake_env("LEAN_PATH") if compiled_units is None else compiled_units['lean_path']
    lean_path = [Path(p).resolve() for p in lean_path_text.split(os.pathsep) if p]
    standard = toolchain / "lib/lean"
    graph_modules = {n["module"] for n in raw["nodes"]}
    if compiled_units is not None:
        graph_modules |= theorem_universe.compiled_imports(raw, compiled_units, lean_path, toolchain)
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
        elif compiled_units is not None and module in compiled_units['units']:
            source_record = compiled_units['units'][module]['source']
            row.update(source=source_record['path'], source_sha256=source_record['sha256'])
        elif module in (bound or {}):
            raise ValueError(f'witness source has no compiler-owned run binding: {module}')
        artifacts.append(row)
    if lake_modules:
        # Fails if any Lake-built olean is stale against its sources (--no-build audits too).
        run(["lake", "--rehash", "build", "--no-build", *lake_modules])
    lake_inputs = library_compiled_inputs(ROOT)
    cacheable = cacheable_modules(raw.get('module_imports'), lake_modules, lean_path, toolchain)

    def validate_inputs():
        if library_compiled_inputs(ROOT) != lake_inputs:
            raise ValueError('canonical Lake compiled inputs changed during kernel replay')
        if compiled_units is not None:
            theorem_universe.verify_compilation(compiled_units)

    raw["kernel_replay"] = kernel_replay({r["module"]: r["olean_sha256"] for r in artifacts},
                                         toolchain, lean_path_text, cache, cacheable,
                                         expected_runtime=runtime_sha,
                                         compiled_inputs_sha256=hashlib.sha256(
                                              json.dumps(lake_inputs, sort_keys=True).encode()).hexdigest(),
                                          validate_inputs=validate_inputs)
    return {"revision": git_revision(), "lake_trace_check": {"modules": lake_modules, "status": "up-to-date"},
            "lean_sysroot": str(toolchain), "toolchain_runtime_sha256": runtime_sha,
            "artifacts": artifacts,
            **({'compiled_units': compiled_units} if compiled_units is not None else {})}


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
    runtime_sha, sysroot = freshness.get('toolchain_runtime_sha256'), freshness.get('lean_sysroot')
    extractor = report.get('extractor')
    if (not isinstance(runtime_sha, str) or not re.fullmatch(r'[0-9a-f]{64}', runtime_sha)
            or not isinstance(sysroot, str) or not Path(sysroot).is_absolute()
            or not isinstance(extractor, dict)
            or not isinstance(extractor.get('lean_sysroot'), str)
            or not Path(extractor['lean_sysroot']).is_absolute()
            or Path(extractor['lean_sysroot']).resolve() != Path(sysroot).resolve()
            or extractor.get('toolchain_runtime_sha256') != runtime_sha):
        raise ValueError('assurance report carries no matching toolchain runtime binding; re-run scripts/assumptions.py')
    for row in freshness["artifacts"]:
        for kind in ("olean", "source"):
            path = row[kind] and (ROOT / row[kind] if not Path(row[kind]).is_absolute() else Path(row[kind]))
            if path and (not path.is_file() or file_sha256(path) != row[kind + "_sha256"]):
                raise ValueError(f"assurance report is stale: {row['module']} {kind} changed")
    toolchain = Path(lake_env('LEAN_SYSROOT')).resolve()
    if Path(sysroot).resolve() != toolchain:
        raise ValueError('assurance report is stale: toolchain runtime root changed')
    if toolchain_runtime_sha256(toolchain) != runtime_sha:
        raise ValueError('assurance report is stale: toolchain runtime changed')
    import theorem_universe
    theorem_universe.verify_compiled_report(report)
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


def compile_witness_fixtures(build: bool) -> tuple[dict[str, str], dict]:
    """Compile registered witnesses with the same precompile input/output binding as Units."""
    files = witness_fixtures()
    import theorem_universe  # Lazy: theorem_universe imports this module.
    return theorem_universe.compile_witness_fixtures(files, ROOT / ".lake/assurance/witness-fixtures", build)


def split_witnesses(report: dict, modules: list[str], witnesses: list[str]) -> None:
    """Keep the audit's scope the requested modules: the fixtures' theorems (checked by the same
    policy and kernel replay) go to `witness_theorems`, where claims.py finds companions."""
    report["modules"] = modules
    report["witness_modules"] = witnesses
    report["witness_theorems"] = [t for t in report["theorems"] if t["module"] in witnesses]
    report["theorems"] = [t for t in report["theorems"] if t["module"] not in witnesses]
    report["theorem_count"] = len(report["theorems"])


def main(argv=None, *, compiled_units: dict | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/assurance/assumptions.json")
    parser.add_argument("--policy", type=Path, default=ROOT / "assurance/policy.json")
    parser.add_argument("--float-semantics", type=Path, default=ROOT / "assurance/float-semantics.json",
                        help="float-semantics label registry (docs/float-semantics.md)")
    parser.add_argument("--module", action="append", help="audit explicit modules instead of the complete shipped scope")
    parser.add_argument("--all-declarations", action="store_true",
                        help="include every declaration in the selected modules, including unused private "
                             "definitions and compiler-generated declarations; default: theorem/boundary roots")
    parser.add_argument("--no-build", action="store_true",
                        help="audit prebuilt modules; Lake-built ones must still pass Lake's trace check")
    parser.add_argument("--replay-cache", type=Path,
                        help="reuse kernel replays of identical oleans within one run (never for receipts)")
    parser.add_argument("--allow-no-theorems", action="store_true",
                        help="audit declarations of modules whose only proofs are examples")
    parser.add_argument("--sources", type=Path,
                        help="JSON object: module -> repository-relative source of each non-Lake module "
                             "(scripts/theorem_universe.py), for the generated-declaration classification")
    args = parser.parse_args(argv)
    try:
        policy = load_policy(args.policy)
        sources = json.loads(args.sources.read_text()) if args.sources else {}
        if not isinstance(sources, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                                    for k, v in sources.items()):
            raise ValueError("--sources must map module names to source paths")
        labels = float_semantics().load_registry(args.float_semantics, root=ROOT)
        modules = sorted(set(args.module)) if args.module else shipped_modules()
        fixtures = {}
        if not args.module:
            if compiled_units is not None:
                raise ValueError('default shipped audit requires its own registered witness compilation')
            if not args.no_build:
                # Complete the SAME selected-module prerequisite before freezing witness inputs.
                # extract() must not change those Lake artifacts after the compiler snapshot.
                run(['lake', 'build', *modules])
            fixtures, compiled_units = compile_witness_fixtures(not args.no_build)
        witnesses = sorted(m for m in fixtures if m not in modules)
        if compiled_units is not None:
            import theorem_universe
            theorem_universe.verify_compilation(compiled_units)
            if args.module:
                if (modules != compiled_units['selected_modules'] or witnesses
                        or 'witness_registry' in compiled_units):
                    raise ValueError('compiled Unit context differs from the requested audit scope')
            elif ('witness_registry' not in compiled_units
                  or witnesses != compiled_units['selected_modules']):
                raise ValueError('compiled witness context differs from the requested audit scope')
        raw = extract(modules, bool(args.module) and not args.no_build, witnesses,
                      all_declarations=args.all_declarations,
                      **({'lean_path': compiled_units['lean_path']} if compiled_units is not None else {}))
        if raw["modules"] != sorted({*modules, *witnesses}):
            raise ValueError("extractor scope differs from requested module inventory")
        freshness = replay_and_freshness(raw, args.replay_cache, fixtures,
                                        **({'compiled_units': compiled_units}
                                           if compiled_units is not None else {}))
        report = apply_policy(raw, policy, labels, not args.allow_no_theorems, {**fixtures, **sources})
        split_witnesses(report, modules, witnesses)
        report["freshness"] = freshness
        report["extractor"] = raw["extractor"]
        if args.all_declarations:
            report["selected_declaration_roots"] = raw["selected_declaration_roots"]
            report["framework_candidates"] = framework_candidates(raw)
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
