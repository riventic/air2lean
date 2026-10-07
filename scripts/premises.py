#!/usr/bin/env python3
"""Map every shipped theorem and roadmap client theorem to the premise IDs of docs/premises.md.

`check` (default) derives the per-theorem premise index from source and fails when the
committed index is stale, a premise ID is undefined or unused, a runtime module or import
has no premise mapping, or the catalogue is malformed. `write` regenerates the index.
`explain` prints the derivation of one theorem. `compiled` applies the same tables to the
kernel dependency graph written by scripts/assumptions.py. See docs/premises.md.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
CONFIG = Path("assurance/premises.json")
ID_RE = re.compile(r"\b[A-Z]{3}-\d{2}\b")
HEADING_RE = re.compile(r"^### ([A-Z]{3}-\d{2}) — (\S.*)$")
KINDS = {"environment", "trusted", "meaning"}
FIELDS = ("Kind", "Statement", "Derived from", "Sources")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXTERNAL_IMPORTS = ("Lean", "Init", "Std", "Lake")
DECL_KW = {"def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive",
           "class", "opaque", "axiom", "example"}
CMD_KW = DECL_KW | {"namespace", "section", "end", "open", "variable", "universe", "set_option",
                    "attribute", "mutual", "macro", "macro_rules", "syntax", "elab", "elab_rules",
                    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "import",
                    "register_simp_attr", "initialize", "builtin_initialize", "deriving", "export",
                    "declare_syntax_cat", "add_decl_doc", "termination_by",
                    # Proofs/Threadsync/Lock.lean's block for one OS's translation.
                    "if_decl", "end_if"}
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
COMMAND_RE = re.compile(r"^" + ATTRS + MODIFIERS + r"([#A-Za-z_][A-Za-z_0-9]*)")
ATTR_ONLY_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)+$")
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿][A-Za-z_0-9'!?À-ɏͰ-Ͽἀ-῿₀-ₜ]*"
TOKEN_RE = re.compile(IDENT + r"(?:\." + IDENT + r")*")
NAME_RE = re.compile(r"\s*(" + IDENT + r"(?:\." + IDENT + r")*)")
CTOR_RE = re.compile(r"^\s*\|\s*(" + IDENT + r")")
PROFILE_MARKER = "-- air2lean-profile:"


# ----------------------------------------------------------------------------- catalogue

def load_catalog(path: Path) -> tuple[dict, dict, list[str]]:
    """Return (premises, reports, errors) parsed from docs/premises.md."""
    premises: dict[str, dict] = {}
    reports: dict[str, list[str]] = {}
    errors: list[str] = []
    lines = path.read_text().splitlines()
    current = None
    section = None
    for number, line in enumerate(lines, 1):
        heading = HEADING_RE.match(line)
        if heading:
            pid = heading.group(1)
            if pid in premises:
                errors.append(f"{path}:{number}: duplicate premise {pid}")
            anchor = f'<a id="{pid.lower()}"></a>'
            previous = next((l for l in reversed(lines[:number - 1]) if l.strip()), "")
            if previous.strip() != anchor:
                errors.append(f"{path}:{number}: premise {pid} lacks anchor {anchor}")
            current = premises.setdefault(pid, {"title": heading.group(2), "fields": {}, "line": number})
            continue
        if line.startswith("#"):
            current = None
            section = line.lstrip("#").strip()
            continue
        if current is not None:
            match = re.match(r"^- ([A-Za-z ]+): (.*)$", line)
            if match:
                current["fields"][match.group(1)] = match.group(2)
                last = match.group(1)
            elif line.startswith("  ") and current["fields"]:
                current["fields"][last] += " " + line.strip()
        if section == "Reports" and line.startswith("|") and not re.match(r"^\|\s*(Report|-+)\s*\|", line):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            ids = ID_RE.findall(cells[-1]) if len(cells) >= 2 else []
            if not ids:
                errors.append(f"{path}:{number}: report row has no premise IDs")
            reports[cells[0]] = ids
    for pid, entry in premises.items():
        for name in FIELDS:
            if not entry["fields"].get(name, "").strip():
                errors.append(f"{path}:{entry['line']}: premise {pid} lacks '- {name}:'")
        kind = entry["fields"].get("Kind", "").rstrip(".")
        if kind and kind not in KINDS:
            errors.append(f"{path}:{entry['line']}: premise {pid} has unknown kind {kind!r}")
        sources = entry["fields"].get("Sources", "")
        if sources and "](" not in sources and "`" not in sources:
            errors.append(f"{path}:{entry['line']}: premise {pid} sources name no document or file")
    for number, line in enumerate(lines, 1):
        for pid in ID_RE.findall(line):
            if pid not in premises:
                errors.append(f"{path}:{number}: undefined premise ID {pid}")
    if not premises:
        errors.append(f"{path}: no premises defined")
    return premises, reports, errors


def load_config(path: Path) -> dict:
    config = json.loads(path.read_text())
    if config.get("schema_version") != 1:
        raise ValueError("unsupported premise configuration schema")
    for key in ("catalog", "index", "universal", "theorem_roots", "import_roots", "excluded", "generated_imports",
                "generated_premises", "profiles", "float_semantics", "source_axiom",
                "runtime_modules", "rules", "implies"):
        if key not in config:
            raise ValueError(f"premise configuration lacks {key}")
    for rule in config["rules"]:
        if set(rule) != {"premise", "scope", "pattern"} or rule["scope"] not in {"closure", "statement"}:
            raise ValueError(f"invalid premise rule: {rule}")
        rule["regex"] = re.compile(rule["pattern"])
    return config


def config_ids(config: dict) -> list[tuple[str, str]]:
    """Every (location, premise ID) mentioned by the configuration."""
    found = [("universal", p) for p in config["universal"]]
    found += [("generated_premises", p) for p in config["generated_premises"]]
    found += [(f"profiles.{k}", p) for k, p in config["profiles"].items()]
    found += [(f"float_semantics.{k}", p) for k, ps in config["float_semantics"].items() for p in ps]
    found += [("source_axiom", p) for p in config["source_axiom"]]
    found += [(f"runtime_modules.{m}", p) for m, ps in config["runtime_modules"].items() for p in ps]
    found += [(f"rules[{i}]", r["premise"]) for i, r in enumerate(config["rules"])]
    found += [(f"implies.{k}", p) for k, ps in config["implies"].items() for p in [k, *ps]]
    return found


# ----------------------------------------------------------------------------- Lean source

def strip_comments(text: str) -> str:
    """Blank comments and string contents, preserving line structure."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            out.append("  ")
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            out.append(" " * (end - i))
            i = end
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""')
            i = j + 1
            continue
        if c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")):
            match = re.match(r"'(?:\\.|[^\\'\n])'", text[i:i + 8])
            if match:
                out.append(" " * len(match.group(0)))
                i += len(match.group(0))
                continue
        out.append(c)
        i += 1
    return "".join(out)


def statement_of(text: str) -> str:
    """Text of a declaration before its first top-level `:=`."""
    depth = 0
    for i, c in enumerate(text):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return text[:i]
    return text


@dataclass
class Decl:
    name: str
    kind: str
    file: "LeanFile"
    line: int
    text: str
    namespaces: tuple[str, ...]
    opens: tuple[str, ...]
    conditions: tuple[str, ...] = ()
    statement: str = ""
    tokens: set = field(default_factory=set)
    targets: list | None = None


@dataclass
class LeanFile:
    path: Path
    rel: str
    module: str
    imports: list[str]
    header: str
    decls: list[Decl] = field(default_factory=list)
    resolved_imports: list["LeanFile"] = field(default_factory=list)
    gate_generated: bool = False

    @property
    def runtime(self) -> bool:
        return self.module == "ZigLean" or self.module.startswith("ZigLean.")

    @property
    def generated(self) -> bool:
        return self.path.name == "Gen.lean"


def module_name(rel: Path) -> str:
    return ".".join(rel.with_suffix("").parts)


def parse_file(path: Path, root: Path) -> LeanFile:
    raw = path.read_text()
    first = raw.split("\n", 1)[0]
    text = strip_comments(raw)
    rel = path.relative_to(root)
    lean = LeanFile(path, rel.as_posix(), module_name(rel),
                    [m.group(1) for m in re.finditer(r"^import\s+(\S+)", text, re.M)],
                    first if first.startswith(PROFILE_MARKER) else "")
    items: list[list] = []  # [keyword, first line, lines]
    for number, line in enumerate(text.split("\n"), 1):
        if line and not line[0].isspace():
            if ATTR_ONLY_RE.match(line.strip()):
                items.append(["@attr", number, [line]])
                continue
            match = COMMAND_RE.match(line)
            keyword = match.group(1) if match else ""
            if keyword in CMD_KW or keyword.startswith("#"):
                if items and items[-1][0] == "@attr" and keyword in DECL_KW:
                    items[-1][0] = keyword
                    items[-1][2].append(line)
                else:
                    items.append([keyword, number, [line]])
                continue
        if items:
            items[-1][2].append(line)
    scopes: list[list] = []  # [kind, name parts, opens]
    file_opens: list[str] = []
    for keyword, number, lines in items:
        body = "\n".join(lines)
        head = lines[0]
        rest = COMMAND_RE.sub("", head, count=1)
        namespaces = tuple(p for s in scopes if s[0] == "namespace" for p in s[1])
        if keyword == "namespace":
            scopes.append(["namespace", rest.split()[0].split("."), []])
        elif keyword in {"section", "mutual"}:
            scopes.append([keyword, [], []])
        elif keyword == "if_decl":
            scopes.append([keyword, [], [], rest.split()[0]])
        elif keyword in {"end", "end_if"}:
            if scopes:
                scopes.pop()
        elif keyword == "open":
            names = []
            for word in rest.replace("(", " ( ").split():
                if word in {"in", "(", "hiding", "renaming"}:
                    break
                if word != "scoped":
                    names.append(word)
            (scopes[-1][2] if scopes else file_opens).extend(names)
        elif keyword in DECL_KW:
            opens = tuple(file_opens + [o for s in scopes for o in s[2]])
            name = ""
            if keyword != "example":
                after = rest
                if keyword == "instance":
                    after = re.sub(r"^\s*\(priority\s*:=[^)]*\)", "", after)
                match = NAME_RE.match(after)
                if match and match.group(1) not in {"where", "extends"}:
                    name = match.group(1)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([*namespaces, name]) if name else ""
            conditions = tuple(s[3] for s in scopes if s[0] == "if_decl")
            decl = Decl(full, keyword, lean, number, body, namespaces, opens, conditions)
            decl.tokens = set(TOKEN_RE.findall(body))
            if keyword in {"theorem", "lemma", "example"}:
                decl.statement = statement_of(body)
            lean.decls.append(decl)
    return lean


# ----------------------------------------------------------------------------- repository

@dataclass
class Repository:
    root: Path
    config: dict
    files: dict[str, LeanFile]
    table: dict[str, list[Decl]]
    errors: list[str]

    def visible(self, lean: LeanFile) -> set[str]:
        seen, pending = set(), [lean]
        while pending:
            current = pending.pop()
            if current.rel not in seen:
                seen.add(current.rel)
                pending.extend(current.resolved_imports)
        return seen


def lean_files(directory: Path):
    for dirpath, dirnames, filenames in os.walk(directory):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
        for name in sorted(filenames):
            if name.endswith(".lean"):
                yield Path(dirpath) / name


def resolve_import(module: str, lean: LeanFile, root: Path, extra: list[str] = ()) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    base = lean.path.parent
    while True:
        candidate = base / relative
        if candidate.is_file():
            return candidate
        if base == root or root not in base.parents:
            break
        base = base.parent
    for base in [root, *(root / e for e in extra)]:
        if (base / relative).is_file():
            return base / relative
    return None


def load_repository(root: Path, config: dict) -> Repository:
    errors: list[str] = []
    files: dict[str, LeanFile] = {}
    pending = []
    for top in ["ZigLean", *config["theorem_roots"]]:
        if not (root / top).is_dir():
            errors.append(f"theorem root {top}/ is missing")
            continue
        pending.extend(lean_files(root / top))
    if (root / "ZigLean.lean").is_file():
        pending.append(root / "ZigLean.lean")
    while pending:
        path = pending.pop()
        rel = path.relative_to(root).as_posix()
        if rel in files:
            continue
        lean = files[rel] = parse_file(path, root)
        for module in lean.imports:
            target = resolve_import(module, lean, root, config["import_roots"])
            if target is not None:
                pending.append(target)
    for lean in files.values():
        for module in lean.imports:
            target = resolve_import(module, lean, root, config["import_roots"])
            if target is not None:
                lean.resolved_imports.append(files[target.relative_to(root).as_posix()])
            elif module in config["generated_imports"]:
                lean.gate_generated = True
            elif module.split(".")[0] not in EXTERNAL_IMPORTS:
                errors.append(f"{lean.rel}: import {module} is unresolved and not an allowed generated import")
    names = {d.name for lean in files.values() for d in lean.decls if d.name}
    for lean in files.values():
        # `if_decl X in ... end_if` elaborates only when the selected translation declares X.
        lean.decls = [d for d in lean.decls
                      if all(any((f"{p}.{c}" if p else c) in names for p in prefixes(d.namespaces))
                             for c in d.conditions)]
    table: dict[str, list[Decl]] = {}
    for lean in files.values():
        for decl in lean.decls:
            if decl.name:
                table.setdefault(decl.name, []).append(decl)
                if decl.kind == "inductive":
                    for line in decl.text.split("\n")[1:]:
                        ctor = CTOR_RE.match(line)
                        if ctor:
                            table.setdefault(f"{decl.name}.{ctor.group(1)}", []).append(decl)
                elif decl.kind in {"structure", "class"}:
                    table.setdefault(f"{decl.name}.mk", []).append(decl)
    return Repository(root, config, files, table, errors)


def prefixes(parts: tuple[str, ...]) -> list[str]:
    return [".".join(parts[:i]) for i in range(len(parts), -1, -1)]


def resolve(repo: Repository, decl: Decl, visible: set[str]) -> list[Decl]:
    if decl.targets is not None:
        return decl.targets
    bases = prefixes(decl.namespaces)
    for opened in decl.opens:
        bases += [f"{b}.{opened}" if b else opened for b in prefixes(decl.namespaces)]
    found: dict[int, Decl] = {}
    for token in decl.tokens:
        # An unresolved dotted name may be a field or projection: retry its owner.
        parts = token.split(".")
        while parts:
            hits = [t for base in bases
                    for t in repo.table.get(f"{base}.{'.'.join(parts)}" if base else ".".join(parts), ())
                    if t.file.rel in visible]
            if hits:
                found.update((id(t), t) for t in hits if t is not decl)
                break
            parts.pop()
    decl.targets = sorted(found.values(), key=lambda d: (d.file.rel, d.line))
    return decl.targets


def profile_premises(config: dict, lean: LeanFile) -> tuple[list[str], str]:
    if not lean.header:
        return [config["profiles"]["absent"]], "no profile header"
    record = json.loads(lean.header[len(PROFILE_MARKER):])
    name = record.get("profile", {}).get("name")
    if name not in config["profiles"]:
        raise ValueError(f"{lean.rel}: profile {name!r} has no premise mapping")
    semantics = record.get("float_semantics", "ieee")
    if semantics not in config["float_semantics"]:
        raise ValueError(f"{lean.rel}: float semantics {semantics!r} has no premise mapping")
    return [config["profiles"][name], *config["float_semantics"][semantics]], f"profile {name}, float {semantics}"


def close(config: dict, via: dict[str, list[str]]) -> dict[str, list[str]]:
    pending = list(via)
    while pending:
        premise = pending.pop()
        for implied in config["implies"].get(premise, ()):
            if implied not in via:
                via[implied] = []
                pending.append(implied)
            via[implied].append(f"implied by {premise}")
    return via


def apply_rules(config: dict, via: dict, tokens, scope: str) -> None:
    for rule in config["rules"]:
        if rule["scope"] != scope:
            continue
        hits = sorted(t for t in tokens if rule["regex"].search(t))
        if hits:
            via.setdefault(rule["premise"], []).append(f"{scope} token {hits[0]}")


def derive(repo: Repository, theorem: Decl, visible: set[str]) -> dict[str, list[str]]:
    config = repo.config
    via: dict[str, list[str]] = {p: ["universal"] for p in config["universal"]}
    seen, pending, tokens = {id(theorem)}, [theorem], set()
    runtime: set[str] = set()
    generated: set[str] = set()
    while pending:
        current = pending.pop()
        tokens |= current.tokens
        for target in resolve(repo, current, visible):
            if target.file.runtime:
                runtime.add(target.file.module)
                continue
            if target.kind == "axiom":
                for premise in config["source_axiom"]:
                    via.setdefault(premise, []).append(f"axiom {target.name}")
            if target.file.generated:
                generated.add(target.file.rel)
            if id(target) not in seen:
                seen.add(id(target))
                pending.append(target)
    for module in sorted(runtime):
        for premise in config["runtime_modules"].get(module, ()):
            via.setdefault(premise, []).append(f"runtime module {module}")
    apply_rules(config, via, tokens, "closure")
    apply_rules(config, via, set(TOKEN_RE.findall(theorem.statement)), "statement")
    gate = any(repo.files[rel].gate_generated for rel in visible)
    for rel in sorted(generated):
        profile, reason = profile_premises(config, repo.files[rel])
        for premise in [*config["generated_premises"], *profile]:
            via.setdefault(premise, []).append(f"generated {rel} ({reason})")
    if gate:
        for premise in [*config["generated_premises"], config["profiles"]["gate-time"]]:
            via.setdefault(premise, []).append("gate-time generated import")
    return close(config, via)


def premise_key(pid: str) -> tuple:
    order = ["PRF", "ALC", "THR", "ORD", "TMR", "MTH", "ASM", "SEM", "EXT", "TRU"]
    prefix = pid.split("-")[0]
    return (order.index(prefix) if prefix in order else len(order), pid)


def is_excluded(config: dict, rel: str) -> bool:
    return any(rel.startswith(prefix) for prefix in config["excluded"])


def build_index(repo: Repository) -> tuple[list[dict], list[str]]:
    errors: list[str] = []
    entries = []
    roots = tuple(f"{r}/" for r in repo.config["theorem_roots"])
    for rel in sorted(repo.files):
        lean = repo.files[rel]
        if not rel.startswith(roots) or is_excluded(repo.config, rel):
            continue
        theorems = [d for d in lean.decls if d.kind in {"theorem", "lemma", "example"}]
        if not theorems:
            continue
        visible = repo.visible(lean)
        names = set()
        for theorem in theorems:
            if theorem.kind == "example":
                theorem.name = f"example@L{theorem.line}"
            if not theorem.name:
                errors.append(f"{rel}:{theorem.line}: theorem without a parsable name")
                continue
            if theorem.name in names:
                errors.append(f"{rel}:{theorem.line}: duplicate theorem {theorem.name}")
            names.add(theorem.name)
            try:
                via = derive(repo, theorem, visible)
            except ValueError as error:
                errors.append(str(error))
                continue
            if not via:
                errors.append(f"{rel}:{theorem.line}: theorem {theorem.name} lacks a premise mapping")
            entries.append({"file": rel, "theorem": theorem.name, "line": theorem.line,
                            "premises": sorted(via, key=premise_key), "via": via})
    return entries, errors


def render_index(entries: list[dict], premises: dict) -> str:
    lines = ["<!-- Generated by `python3 scripts/premises.py write`; do not edit. -->",
             "# Theorem premise index", "",
             "Each row lists the premise IDs that a theorem uses. Their meanings are in",
             "[premises.md](premises.md). `scripts/premises.py explain <theorem>` shows why each",
             "premise was derived. This index covers the committed generated modules.", "",
             f"{len(entries)} theorems in {len({e['file'] for e in entries})} files.", "",
             "| Premise | Theorems | Title |", "|---|---|---|"]
    for pid in sorted(premises, key=premise_key):
        count = sum(pid in e["premises"] for e in entries)
        lines.append(f"| [{pid}](premises.md#{pid.lower()}) | {count} | {premises[pid]['title']} |")
    current = None
    for entry in entries:
        if entry["file"] != current:
            current = entry["file"]
            union = sorted({p for e in entries if e["file"] == current for p in e["premises"]}, key=premise_key)
            lines += ["", f"## `{current}`", "", f"File premises: {', '.join(union)}", "",
                      "| Theorem | Premises |", "|---|---|"]
        lines.append(f"| `{entry['theorem']}` | {', '.join(entry['premises'])} |")
    return "\n".join(lines) + "\n"


def runtime_errors(repo: Repository) -> list[str]:
    errors = []
    mapping = repo.config["runtime_modules"]
    runtime = {lean.module: lean for lean in repo.files.values() if lean.runtime}
    for module, lean in sorted(runtime.items()):
        if any(d.name for d in lean.decls) and module not in mapping:
            errors.append(f"runtime module {module} has declarations but no premise mapping")
    for module in sorted(mapping):
        if module not in runtime:
            errors.append(f"runtime_modules names missing module {module}")
    return errors


def check(root: Path = ROOT, write: bool = False) -> tuple[list[str], list[dict]]:
    config = load_config(root / CONFIG)
    premises, reports, errors = load_catalog(root / config["catalog"])
    referenced = set()
    for where, pid in config_ids(config):
        referenced.add(pid)
        if pid not in premises:
            errors.append(f"{CONFIG}: {where} uses undefined premise {pid}")
    for report, ids in reports.items():
        referenced.update(ids)
    for pid in sorted(set(premises) - referenced):
        errors.append(f"premise {pid} is referenced by no rule, runtime module or report")
    if set(config["profiles"]) != {"absent", "legacy-abi64-le", "abi64-le-v1", "gate-time"}:
        errors.append(f"{CONFIG}: profiles must map absent, legacy-abi64-le, abi64-le-v1 and gate-time")
    repo = load_repository(root, config)
    errors += repo.errors + runtime_errors(repo)
    entries, index_errors = build_index(repo)
    errors += index_errors
    for entry in entries:
        for pid in entry["premises"]:
            if pid not in premises:
                errors.append(f"{entry['file']}: {entry['theorem']} uses undefined premise {pid}")
    if not entries:
        errors.append("no theorems found; nothing was indexed")
    rendered = render_index(entries, premises)
    index = root / config["index"]
    if write:
        index.write_text(rendered)
    elif not index.is_file() or index.read_text() != rendered:
        errors.append(f"{config['index']} is stale; run python3 scripts/premises.py write")
    return errors, entries


# ----------------------------------------------------------------------------- compiled graph

def compiled(report: dict, root: Path, config: dict, source: list[dict] | None) -> dict:
    """Derive premises from the kernel dependency graph of scripts/assumptions.py."""
    if report.get("schema_version") != 1 or report.get("status") not in {"pass", "fail"}:
        raise ValueError("assumption report is not a completed schema-1 audit")
    nodes = {n["name"]: n for n in report["nodes"]}
    errors, theorems, skipped = [], [], 0
    profiles: dict[str, tuple[list[str], str]] = {}
    by_name: dict[str, set] = {}
    for entry in source or ():
        by_name.setdefault(entry["theorem"], set()).update(entry["premises"])

    def runtime(module: str) -> bool:
        return module == "ZigLean" or module.startswith("ZigLean.")

    def external(module: str) -> bool:
        return module.split(".")[0] in EXTERNAL_IMPORTS

    for theorem in report["theorems"]:
        if runtime(theorem["module"]):
            skipped += 1
            continue
        via: dict[str, list[str]] = {p: ["universal"] for p in config["universal"]}
        seen, pending, names, modules, generated = set(), [theorem["name"]], set(), set(), set()
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            node = nodes.get(name)
            if node is None:
                raise ValueError(f"incomplete declaration graph: {name}")
            module = node["module"]
            if runtime(module):
                modules.add(module)
                names.add(name)
                continue
            if external(module):
                continue
            names.add(name)
            if node["kind"] == "axiom" and name not in STANDARD_AXIOMS:
                for premise in config["source_axiom"]:
                    via.setdefault(premise, []).append(f"axiom {name}")
            if module.split(".")[-1] == "Gen":
                generated.add(module)
            pending.extend(node["dependencies"])
        for axiom in theorem.get("axioms", ()):
            if axiom not in STANDARD_AXIOMS:
                for premise in config["source_axiom"]:
                    via.setdefault(premise, []).append(f"axiom {axiom}")
        for module in sorted(modules):
            if module not in config["runtime_modules"]:
                errors.append(f"{theorem['name']}: runtime module {module} has no premise mapping")
            for premise in config["runtime_modules"].get(module, ()):
                via.setdefault(premise, []).append(f"runtime module {module}")
        apply_rules(config, via, names, "closure")
        # The graph does not separate type from proof edges: statement rules see all direct edges.
        apply_rules(config, via, set(nodes[theorem["name"]]["dependencies"]), "statement")
        for module in sorted(generated):
            if module not in profiles:
                path = root / Path(*module.split(".")).with_suffix(".lean")
                header = ""
                if path.is_file():
                    first = path.read_text().split("\n", 1)[0]
                    header = first if first.startswith(PROFILE_MARKER) else ""
                    profiles[module] = profile_premises(config, LeanFile(path, module, module, [], header))
                else:
                    profiles[module] = ([config["profiles"]["gate-time"]], "generated module not in repository")
            profile, reason = profiles[module]
            for premise in [*config["generated_premises"], *profile]:
                via.setdefault(premise, []).append(f"generated {module} ({reason})")
        via = close(config, via)
        entry = {"name": theorem["name"], "module": theorem["module"],
                 "premises": sorted(via, key=premise_key)}
        if source is not None:
            short = theorem["name"]
            known = by_name.get(short)
            if known is not None:
                entry["source_gaps"] = sorted(set(entry["premises"]) - known, key=premise_key)
        theorems.append(entry)
    gaps = [t for t in theorems if t.get("source_gaps")]
    return {"schema_version": 1, "status": "fail" if errors else "pass",
            "theorem_count": len(theorems), "runtime_theorems_skipped": skipped,
            "source_gap_count": len(gaps), "errors": errors, "theorems": theorems}


# ----------------------------------------------------------------------------- CLI

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("check", help="verify the committed index and premise mappings (default)")
    sub.add_parser("write", help="regenerate the committed index")
    explain = sub.add_parser("explain", help="show why a theorem has each premise")
    explain.add_argument("theorem")
    dump = sub.add_parser("json", help="write the source-derived index as JSON")
    dump.add_argument("--output", type=Path, required=True)
    graph = sub.add_parser("compiled", help="derive premises from a scripts/assumptions.py report")
    graph.add_argument("--assurance", type=Path, required=True)
    graph.add_argument("--output", type=Path, required=True)
    graph.add_argument("--strict", action="store_true", help="also fail when the source index misses a compiled premise")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    command = args.command or "check"
    try:
        if command == "compiled":
            config = load_config(root / CONFIG)
            _, entries = check(root)
            report = compiled(json.loads(args.assurance.read_text()), root, config, entries)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
            for error in report["errors"]:
                print(f"  {error}", file=sys.stderr)
            print(f"premises {report['status']}: {report['theorem_count']} compiled theorems, "
                  f"{report['source_gap_count']} with source-index gaps; report: {args.output}", file=sys.stderr)
            return 1 if report["errors"] or (args.strict and report["source_gap_count"]) else 0
        errors, entries = check(root, write=command == "write")
    except (OSError, ValueError, KeyError, re.error) as error:
        print(f"premise error: {error}", file=sys.stderr)
        return 2
    if command == "explain":
        matches = [e for e in entries if e["theorem"] == args.theorem or e["theorem"].endswith("." + args.theorem)]
        if not matches:
            print(f"no indexed theorem named {args.theorem}", file=sys.stderr)
            return 1
        for entry in matches:
            print(f"{entry['theorem']} ({entry['file']}:{entry['line']})")
            for pid in entry["premises"]:
                print(f"  {pid}: {'; '.join(dict.fromkeys(entry['via'][pid]))}")
        return 0
    if command == "json":
        args.output.write_text(json.dumps([{k: e[k] for k in ("file", "theorem", "line", "premises")}
                                           for e in entries], indent=2) + "\n")
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    status = "fail" if errors else "pass"
    print(f"premises {status}: {len(entries)} theorems indexed", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
