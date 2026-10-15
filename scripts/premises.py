#!/usr/bin/env python3
"""Map every shipped theorem and roadmap client theorem to the premise IDs of docs/premises.md.

`check` (default) derives the per-theorem premise index from source and fails when the
committed index is stale, a premise ID is undefined or unused, a runtime module or import
has no premise mapping, or the catalogue is malformed. `write` regenerates the index.
`explain` prints the derivation of one theorem. `compiled` applies the same tables to the
kernel dependency graph written by scripts/assumptions.py. Both fail when a concurrency theorem
or report omits the memory-model adequacy premise (`memory_model`, C12). See docs/premises.md.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assumptions import STANDARD_AXIOMS, file_sha256, toolchain_runtime_sha256, write_report  # noqa: E402
from premise_markers import (GeneratedMarkers, generated_module, markers as premise_markers,  # noqa: E402
                             module_path as generated_path)

ROOT = Path(__file__).resolve().parents[1]
CONFIG = Path("assurance/premises.json")
ID_RE = re.compile(r"\b[A-Z]{3}-\d{2}\b")
HEADING_RE = re.compile(r"^### ([A-Z]{3}-\d{2}) — (\S.*)$")
KINDS = {"environment", "trusted", "meaning"}
FIELDS = ("Kind", "Statement", "Derived from", "Sources")
EXTERNAL_IMPORTS = ("Lean", "Init", "Std", "Lake")
DECL_KW = {"def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive",
           "class", "opaque", "axiom", "example"}
CMD_KW = DECL_KW | {"namespace", "section", "end", "open", "variable", "universe", "set_option",
                    "attribute", "mutual", "macro", "macro_rules", "syntax", "elab", "elab_rules",
                    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "import",
                    "register_simp_attr", "initialize", "builtin_initialize", "deriving", "export",
                    "declare_syntax_cat", "add_decl_doc", "termination_by",
                    # Proofs/Threadsync/Variant.lean's block for one OS's translation.
                    "if_decl", "end_if"}
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
COMMAND_RE = re.compile(r"^" + ATTRS + MODIFIERS + r"([#A-Za-z_][A-Za-z_0-9]*)")
ATTR_ONLY_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)+$")
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿][A-Za-z_0-9'!?À-ɏͰ-Ͽἀ-῿₀-ₜ]*"
TOKEN_RE = re.compile(IDENT + r"(?:\." + IDENT + r")*")
NAME_RE = re.compile(r"\s*(" + IDENT + r"(?:\." + IDENT + r")*)")
CTOR_RE = re.compile(r"\|\s*(" + IDENT + r")")
# `.ctor` with an expected type (`throw .unspecified`), not a field access on a term (nor on
# the anonymous-function argument `·`).
DOT_CTOR_RE = re.compile(r"(?<![\w.'!?)\]}⟩·])\.(" + IDENT + r")")
# `(·.f …)`: field notation on the argument of an anonymous function. In this repository it is
# the projection argument `Ptr → Ptr` of pointer formation (`ptrProject p (·.add 8)`,
# `ptrProjectDevice`, `BlkAt.proj (f := ·.elem …)`), so `f` elaborates to `Zig.Ptr.f`.
DOT_FIELD_RE = re.compile(r"·\.(" + IDENT + r")")
# `(a b : T ...)`, `{a : T}`, `[a : T]`, `⦃a : T⦄`: bound names and the head token of their type.
BINDER_RE = re.compile(r"[(\[{⦃]\s*((?:" + IDENT + r"\s+)*" + IDENT + r")\s*:(?!=)\s*@?("
                       + IDENT + r"(?:\." + IDENT + r")*)")
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
                "generated_premises", "generated_markers", "profiles", "float_semantics", "source_axiom",
                "runtime_modules", "rules", "implies", "memory_model"):
        if key not in config:
            raise ValueError(f"premise configuration lacks {key}")
    model = config["memory_model"]
    if (not isinstance(model, dict) or not isinstance(model.get("premise"), str)
            or not isinstance(model.get("concurrency"), list) or not model["concurrency"]
            or not isinstance(model.get("targets"), dict) or not isinstance(model.get("unqualified"), dict)):
        raise ValueError("memory_model needs a premise, concurrency premises, targets and unqualified targets")
    for rule in config["rules"]:
        if set(rule) != {"premise", "scope", "pattern"} or rule["scope"] not in {"closure", "statement"}:
            raise ValueError(f"invalid premise rule: {rule}")
        rule["regex"] = re.compile(rule["pattern"])
    if (not isinstance(config.get("declaration_carriers", {}), dict)
            or not isinstance(config.get("carrier_coverage", {}), dict)
            or not isinstance(config.get("kernel_index", False), bool)):
        raise ValueError("declaration_carriers/coverage must be objects and kernel_index a boolean")
    for pid, carrier in config.get("declaration_carriers", {}).items():
        if (not isinstance(pid, str) or not ID_RE.fullmatch(pid) or not isinstance(carrier, dict)
                or set(carrier) != {"modules", "declarations", "namespaces", "reason"}
                or not isinstance(carrier["reason"], str) or not carrier["reason"].strip() or not carrier["modules"]
                or not all(isinstance(carrier[k], list) and
                           all(isinstance(n, str) and n for n in carrier[k])
                           for k in ("modules", "declarations", "namespaces"))
                or not (carrier["declarations"] or carrier["namespaces"])):
            raise ValueError(f"invalid declaration carrier for {pid}")
        for module in carrier["modules"]:
            if pid not in config["runtime_modules"].get(module, ()):
                raise ValueError(f"carrier {pid} replaces no mapping in {module}")
            if module.replace(".", "/") + ".lean" not in config.get("carrier_coverage", {}):
                raise ValueError(f"carrier {pid} has no coverage review for {module}")
    for rel, digest in config.get("carrier_coverage", {}).items():
        if (Path(rel).is_absolute() or ".." in Path(rel).parts or not rel.endswith(".lean")
                or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)):
            raise ValueError(f"invalid declaration carrier coverage: {rel}")
    return config


def config_ids(config: dict) -> list[tuple[str, str]]:
    """Every (location, premise ID) mentioned by the configuration."""
    found = [("universal", p) for p in config["universal"]]
    found += [("generated_premises", p) for p in config["generated_premises"]]
    found += [("generated_markers", p) for p in config["generated_markers"]]
    found += [(f"profiles.{k}", p) for k, p in config["profiles"].items()]
    found += [(f"float_semantics.{k}", p) for k, ps in config["float_semantics"].items() for p in ps]
    found += [(f"admissions.{k}", p) for k, ps in config.get("admissions", {}).items() for p in ps]
    found += [("source_axiom", p) for p in config["source_axiom"]]
    found += [(f"runtime_modules.{m}", p) for m, ps in config["runtime_modules"].items() for p in ps]
    found += [(f"rules[{i}]", r["premise"]) for i, r in enumerate(config["rules"])]
    found += [("declaration_carriers", p) for p in config.get("declaration_carriers", {})]
    found += [(f"implies.{k}", p) for k, ps in config["implies"].items() for p in [k, *ps]]
    model = config["memory_model"]
    found += [("memory_model.premise", model["premise"])]
    found += [("memory_model.concurrency", p) for p in model["concurrency"]]
    return found


def memory_model_errors(config: dict, entries, where) -> list[str]:
    """C12: every entry whose premises contain a concurrency premise lists the memory-model
    adequacy premise. `where(entry)` names the entry in the message."""
    model = config["memory_model"]
    return [f"{where(e)} makes a concurrency claim without the memory-model adequacy premise "
            f"{model['premise']}" for e in entries
            if set(model["concurrency"]) & set(e["premises"]) and model["premise"] not in e["premises"]]


def memory_model_record_errors(config: dict, reports: dict, root: Path) -> list[str]:
    """The adequacy qualification record names its evidence, and every concurrency report of
    docs/premises.md lists the premise itself (not only through `implies`)."""
    model, errors = config["memory_model"], []
    for target, entry in sorted(model["targets"].items()):
        if not entry.get("hardware") or not entry.get("argument") or not entry.get("evidence"):
            errors.append(f"memory_model.targets.{target} needs hardware, argument and evidence")
        for path in entry.get("evidence", ()):
            if not (root / path).exists():
                errors.append(f"memory_model.targets.{target}: evidence {path} does not exist")
    for target in sorted(set(model["targets"]) & set(model["unqualified"])):
        errors.append(f"memory_model: {target} is both qualified and unqualified")
    for name, ids in sorted(reports.items()):
        reached = close(config, {p: [] for p in ids})
        if set(model["concurrency"]) & set(reached) and model["premise"] not in ids:
            errors.append(f"report {name!r} rests on a concurrency premise but does not list {model['premise']}")
    return errors


# ----------------------------------------------------------------------------- Lean source

def is_runtime(module: str) -> bool:
    return module == "ZigLean" or module.startswith("ZigLean.")


def profile_header(text: str) -> str:
    first = text.split("\n", 1)[0]
    return first if first.startswith(PROFILE_MARKER) else ""


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


def top_level(text: str, sep: str) -> int:
    """Index of the first `sep` outside brackets, or -1."""
    depth = 0
    for i, c in enumerate(text):
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(sep, i):
            return i
    return -1


def statement_of(text: str) -> str:
    """Text of a declaration before its first top-level `:=`."""
    end = top_level(text, ":=")
    return text if end < 0 else text[:end]


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
    binders: dict = field(default_factory=dict)
    dot_ctors: set = field(default_factory=set)
    dot_fields: set = field(default_factory=set)
    targets: list | None = None
    markers: dict = field(default_factory=dict)  # premise ID -> parameter indices


@dataclass
class LeanFile:
    path: Path
    rel: str
    module: str
    imports: list[str]
    header: str
    decls: list[Decl] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    resolved_imports: list["LeanFile"] = field(default_factory=list)
    gate_generated: bool = False

    @property
    def runtime(self) -> bool:
        return is_runtime(self.module)

    @property
    def generated(self) -> bool:
        return self.path.name == "Gen.lean"


def module_name(rel: Path) -> str:
    return ".".join(rel.with_suffix("").parts)


def binders(text: str) -> list[tuple[str, str]]:
    """(name, type head) of every explicit binder group in `text`."""
    return [(name, match.group(2)) for match in BINDER_RE.finditer(text) for name in match.group(1).split()]


def type_head(decl: Decl, allow_parameters: bool = False) -> str:
    """The head name of a binder-free constant's declared type, `def S : Sem Ph where` -> `Sem`."""
    text = re.split(r":=|\bwhere\b", statement_of(decl.text), maxsplit=1)[0]
    colon = top_level(text, ":")
    if colon < 0 or (not allow_parameters and binders(text[:colon])):
        return ""
    match = TOKEN_RE.search(text[colon + 1:])
    return match.group(0) if match else ""


def instance_type(decl: Decl) -> frozenset:
    """Names in an instance's type, `instance [Enc α] : Enc (Array α) where` -> {Enc, Array}.
    Binder names and single-letter (auto-bound) variables are dropped."""
    text = re.split(r"\bwhere\b", statement_of(decl.text), maxsplit=1)[0]
    colon = top_level(text, ":")
    if colon < 0:
        return frozenset()
    text = text[colon + 1:]
    bound = {name for name, _ in binders(decl.text)}
    names = {t.rsplit(".", 1)[-1] for t in TOKEN_RE.findall(text)}
    return frozenset(n for n in names - bound - {"Type", "Prop", "Sort"} if len(n.rstrip("'₀₁₂₃₄₅₆₇₈₉")) > 1)


def parse_file(path: Path, root: Path) -> LeanFile:
    raw = path.read_text()
    text = strip_comments(raw)
    rel = path.relative_to(root)
    lean = LeanFile(path, rel.as_posix(), module_name(rel),
                    [m.group(1) for m in re.finditer(r"^import\s+(\S+)", text, re.M)],
                    profile_header(raw))
    markers, lean.errors = premise_markers(raw, lean.rel)
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
    scopes: list[list] = []  # [kind, name parts, opens, variable binders, if_decl condition]
    file_opens: list[str] = []
    file_vars: list[tuple[str, str]] = []
    ambient_vars: list[tuple[int, set[str], set[str]]] = []
    for keyword, number, lines in items:
        body = "\n".join(lines)
        head = lines[0]
        rest = COMMAND_RE.sub("", head, count=1)
        namespaces = tuple(p for s in scopes if s[0] == "namespace" for p in s[1])
        if keyword == "namespace":
            scopes.append(["namespace", rest.split()[0].split("."), [], []])
        elif keyword in {"section", "mutual"}:
            scopes.append([keyword, [], [], []])
        elif keyword == "if_decl":
            scopes.append([keyword, [], [], [], rest.split()[0]])
        elif keyword == "variable":
            (scopes[-1][3] if scopes else file_vars).extend(binders(body))
            names = {n for n, _ in binders(body)}
            ambient_vars.append((len(scopes), names, set(TOKEN_RE.findall(body)) - names - {"variable"}))
        elif keyword in {"end", "end_if"}:
            if scopes:
                scopes.pop()
                ambient_vars = [v for v in ambient_vars if v[0] <= len(scopes)]
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
            conditions = tuple(s[4] for s in scopes if s[0] == "if_decl")
            decl = Decl(full, keyword, lean, number, body, namespaces, opens, conditions)
            decl.tokens = set(TOKEN_RE.findall(body))
            # A used section variable carries its whole declared type, including concrete
            # generated target parameters absent from this theorem's explicit telescope.
            while True:
                used = {token.split(".", 1)[0] for token in decl.tokens}
                extra = {t for _, names, types in ambient_vars if names & used for t in types}
                if extra <= decl.tokens:
                    break
                decl.tokens |= extra
            decl.dot_ctors = set(DOT_CTOR_RE.findall(body))
            decl.dot_fields = set(DOT_FIELD_RE.findall(body))
            for name, head in [*file_vars, *(b for s in scopes for b in s[3]), *binders(body)]:
                decl.binders.setdefault(name, set()).add(head)
            if keyword in {"theorem", "lemma", "example"}:
                decl.statement = statement_of(body)
            if keyword == "def" and number in markers:
                decl.markers = markers.pop(number)
            lean.decls.append(decl)
    # A marker that does not sit directly above a `def` would silently drop its premise.
    lean.errors += [f"{lean.rel}:{number - 1}: air2lean-premises marker does not precede a def"
                    for number in markers]
    return lean


# ----------------------------------------------------------------------------- repository

@dataclass
class Repository:
    root: Path
    config: dict
    files: dict[str, LeanFile]
    table: dict[str, list[Decl]]
    errors: list[str]
    ctors: dict[str, list[Decl]] = field(default_factory=dict)  # constructor short name -> inductives
    _visible: dict[str, set[str]] = field(default_factory=dict)
    _instances: list | None = None

    def instances(self) -> list[tuple[Decl, frozenset]]:
        """Every instance with the last name components of its instance type (cached)."""
        if self._instances is None:
            # An instance type with no recognisable names would match every closure: skip it.
            self._instances = [(d, need) for lean in self.files.values() for d in lean.decls
                               if d.kind == "instance" and (need := instance_type(d))]
        return self._instances

    def visible(self, lean: LeanFile) -> set[str]:
        """Files reachable through `lean`'s transitive imports (cached per file)."""
        if lean.rel not in self._visible:
            seen, pending = set(), [lean]
            while pending:
                current = pending.pop()
                if current.rel not in seen:
                    seen.add(current.rel)
                    pending.extend(current.resolved_imports)
            self._visible[lean.rel] = seen
        return self._visible[lean.rel]


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
        errors += lean.errors
        errors += [f"{rel}: air2lean-premises marker names {p}, not a generated_markers premise"
                   for d in lean.decls for p in d.markers if p not in config["generated_markers"]]
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
    ctors: dict[str, list[Decl]] = {}
    for lean in files.values():
        for decl in lean.decls:
            if decl.name:
                table.setdefault(decl.name, []).append(decl)
                if decl.kind == "inductive":
                    first, _, rest = decl.text.partition("\n")
                    for line in [first.partition(" where")[2], *rest.split("\n")]:
                        # `| a | b`: every constructor of the line, including `inductive T where | a | b`.
                        for ctor in CTOR_RE.findall(line) if line.lstrip().startswith("|") else ():
                            table.setdefault(f"{decl.name}.{ctor}", []).append(decl)
                            ctors.setdefault(ctor, []).append(decl)
                elif decl.kind in {"structure", "class"}:
                    table.setdefault(f"{decl.name}.mk", []).append(decl)
    return Repository(root, config, files, table, errors, ctors)


def prefixes(parts: tuple[str, ...]) -> list[str]:
    return [".".join(parts[:i]) for i in range(len(parts), -1, -1)]


def resolve(repo: Repository, decl: Decl) -> list[Decl]:
    """Declarations named by `decl`, resolved against its own file's imports."""
    if decl.targets is not None:
        return decl.targets
    visible = repo.visible(decl.file)

    def scope_bases(d: Decl) -> list[str]:
        bases = prefixes(d.namespaces)
        for opened in d.opens:
            bases += [f"{b}.{opened}" if b else opened for b in prefixes(d.namespaces)]
        return bases

    bases = scope_bases(decl)

    def lookup(name: str, scope: Decl | None = None) -> list[Decl]:
        """`name` in `decl`'s scope, or in `scope`'s (its namespaces, opens and imports)."""
        names, vis = (bases, visible) if scope is None else (scope_bases(scope), repo.visible(scope.file))
        return [t for base in names for t in repo.table.get(f"{base}.{name}" if base else name, ())
                if t.file.rel in vis]

    def typed(token: str, depth: int = 0) -> list[Decl]:
        """`x.f` on a bound `x : T ...` is generalized field notation for `T.f x`."""
        local, _, rest = token.partition(".")
        if not rest or local not in decl.binders or depth > 2:
            return []
        hits, owners = [], []
        for head in decl.binders[local]:
            owners += typed(head, depth + 1) or lookup(head)
        for field_name in rest.split("."):
            fields = [t for owner in owners for t in repo.table.get(f"{owner.name}.{field_name}", ())
                      if t.file.rel in visible]
            hits += fields
            owners = [owner for target in fields if (head := type_head(target, allow_parameters=True))
                      for owner in lookup(head, target)]
        return hits

    found: dict[int, Decl] = {}
    for name in decl.dot_ctors:
        # The expected type is unknown in source: resolve only a constructor name that exactly one
        # visible inductive declares. Ambiguous names (generated exits, phases) are left out.
        owners = {id(t): t for t in repo.ctors.get(name, ()) if t.file.rel in visible}
        if len(owners) == 1 and decl not in owners.values():
            found.update(owners)
    for name in decl.dot_fields:
        # The elaborated constant of `·.f`: the `Ptr` operation `f`; nothing if there is none
        # (the receiver type is unknown in source; `compiled` sees the elaborated constant).
        found.update((id(t), t) for t in repo.table.get(f"Zig.Ptr.{name}", ())
                     if t.file.rel in visible and t is not decl)
    for token in decl.tokens:
        found.update((id(t), t) for t in typed(token) if t is not decl)
        # An unresolved dotted name may be a field or projection: retry its owner.
        parts = token.split(".")
        while parts:
            hits = lookup(".".join(parts))
            if hits:
                found.update((id(t), t) for t in hits if t is not decl)
                rest = token.split(".")[len(parts):]
                if rest:
                    # `c.f` on a constant `c : T ...` is generalized field notation for `T.f c`;
                    # `T` is named in the constant's own scope, not the referencing one.
                    for hit in hits:
                        head = type_head(hit)
                        for owner in lookup(head, hit) if head else ():
                            found.update((id(t), t) for t in repo.table.get(f"{owner.name}.{rest[0]}", ())
                                         if t.file.rel in visible and t is not decl)
                break
            parts.pop()
    decl.targets = sorted(found.values(), key=lambda d: (d.file.rel, d.line))
    return decl.targets


# Translator flags that are admission opt-ins, by the name the header records (`admission`).
ADMISSION_FLAGS = {"--allow-unqualified-build-mode": "unqualified-build-mode", "--assume-no-libc": "no-libc",
                   "--assume-asm-cpu-features": "asm-cpu-features"}


def example_admissions(lean: LeanFile) -> list[str]:
    """A committed example translation (`Proofs/<Ex>/Gen.lean`) is a canonical body without a
    header; its admission opt-ins are those of `examples/<ex>/translate.args`, which every
    translation of the example uses (scripts/check.sh)."""
    parts = lean.rel.split("/")
    if len(parts) != 3 or parts[0] != "Proofs" or parts[2] != "Gen.lean":
        return []
    args = lean.path.parents[2] / "examples" / parts[1].lower() / "translate.args"
    tokens = args.read_text().split() if args.is_file() else []
    return [ADMISSION_FLAGS[t] for t in tokens if t in ADMISSION_FLAGS]


def admission_premises(config: dict, lean: LeanFile, admissions: list[str]) -> list[str]:
    mapped = config.get("admissions", {})
    for admission in admissions:
        if admission not in mapped:
            raise ValueError(f"{lean.rel}: admission {admission!r} has no premise mapping")
    return [p for a in admissions for p in mapped[a]]


def profile_premises(config: dict, lean: LeanFile) -> tuple[list[str], str]:
    if not lean.header:
        admissions = example_admissions(lean)
        why = "no profile header" + (f", translate.args admission {','.join(admissions)}" if admissions else "")
        return [config["profiles"]["absent"], *admission_premises(config, lean, admissions)], why
    record = json.loads(lean.header[len(PROFILE_MARKER):])
    name = record.get("profile", {}).get("name")
    if name not in config["profiles"]:
        raise ValueError(f"{lean.rel}: profile {name!r} has no premise mapping")
    semantics = record.get("float_semantics", "ieee")
    if semantics not in config["float_semantics"]:
        raise ValueError(f"{lean.rel}: float semantics {semantics!r} has no premise mapping")
    # An admission opt-in (`"admission": "unqualified-build-mode,no-libc"`) widens the claim scope:
    # each one maps to its premises (`admissions`), and an unmapped one fails closed.
    admissions = [a for a in record.get("admission", "").split(",") if a]
    premises = [config["profiles"][name], *config["float_semantics"][semantics],
                *admission_premises(config, lean, admissions)]
    why = f"profile {name}, float {semantics}" + (f", admission {','.join(admissions)}" if admissions else "")
    return premises, why


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


def apply_markers(via: dict, name: str, markers: dict) -> None:
    """A reached generated definition's caller obligations (W1): its marker's premises."""
    for premise, params in markers.items():
        via.setdefault(premise, []).append(f"marker on {name} (parameters {', '.join(map(str, params))})")


def apply_rules(config: dict, via: dict, tokens, scope: str) -> None:
    for rule in config["rules"]:
        if rule["scope"] != scope:
            continue
        hits = sorted(t for t in tokens if rule["regex"].search(t))
        if hits:
            via.setdefault(rule["premise"], []).append(f"{scope} token {hits[0]}")


def binding_premises(repo: Repository, rel: str, tokens) -> list[tuple[str, str]]:
    """(premise, binding) for each model binding of generated module `rel` whose own premise
    (`extern.premise`, EXT-03) the closure reaches: a token naming the binding's declarations
    (`air2lean_model_<i>`, `_contract`, `_evidence`) or its implementation. The audit derives the
    same premise from the binding's evidence axiom or implementation opaque (scripts/assumptions.py
    `generated_premises`); here a use of any of its declarations counts."""
    module = generated_module(repo.root, rel)
    names = {t.rsplit(".", 1)[-1] for t in tokens}
    found = []
    for index, binding in enumerate(getattr(module, "bindings", ())):
        extern = binding.get("extern")
        premise = extern.get("premise") if isinstance(extern, dict) else None
        stems = {f"air2lean_model_{index}", binding.get("implementation")}
        if isinstance(premise, str) and ID_RE.fullmatch(premise) and any(
                n in stems or (n.startswith(f"air2lean_model_{index}_")) for n in names):
            found.append((premise, f"air2lean_model_{index}"))
    return found


def derive(repo: Repository, theorem: Decl) -> dict[str, list[str]]:
    config = repo.config
    via: dict[str, list[str]] = {p: ["universal"] for p in config["universal"]}
    seen, pending, tokens = {id(theorem)}, [theorem], set()
    runtime: set[str] = set()
    unfolded: set[str] = set()
    runtime_targets: list[Decl] = []
    proof_names: set[str] = set()  # last name components the proofs of the closure's theorems name
    generated: set[str] = set()
    visible = repo.visible(theorem.file)
    instances = [(d, need) for d, need in repo.instances() if d.file.rel in visible]

    def visit(target: Decl) -> None:
        if target.name:
            tokens.add(target.name)  # as in the kernel graph, rules also see resolved names
        apply_markers(via, target.name, target.markers)
        if target.file.runtime:
            runtime.add(target.file.module)
            seen.add(id(target))
            # A proof that names a runtime definition can unfold it (`simp only [d]`, `unfold d`):
            # the kernel term then holds the constants of its body, so the closure rules see them.
            # Decided below, once every proof of the closure is known.
            runtime_targets.append(target)
            return
        if target.kind == "axiom":
            for premise in config["source_axiom"]:
                via.setdefault(premise, []).append(f"axiom {target.name}")
        if target.file.generated:
            generated.add(target.file.rel)
        if id(target) not in seen:
            seen.add(id(target))
            pending.append(target)

    while True:
        while pending:
            current = pending.pop()
            tokens |= current.tokens
            if current.kind in THEOREM_KINDS:
                proof_names.update(t.rsplit(".", 1)[-1] for t in TOKEN_RE.findall(current.text[len(current.statement):]))
            for target in resolve(repo, current):
                visit(target)
        # Instance arguments are implicit in source: assume every visible instance whose type
        # names only things the closure names is used.
        names = {t.rsplit(".", 1)[-1] for t in tokens}
        found = [d for d, need in instances if id(d) not in seen and need <= names]
        if not found:
            break
        for instance in found:
            visit(instance)
    # Only a proof unfolds: a statement, or a generated definition that applies a runtime
    # definition, keeps the constant. A type has no body to unfold.
    for target in runtime_targets:
        if target.kind not in {"inductive", "structure", "class"} and target.name.rsplit(".", 1)[-1] in proof_names:
            unfolded.update(target.tokens)
    # A tactic applies lemmas of runtime modules that the source does not name (`tactic_modules`).
    for token in sorted(tokens):
        runtime.update(config.get("tactic_modules", {}).get(token.rsplit(".", 1)[-1], ()))
    for module in sorted(runtime):
        lean = repo.files.get(module.replace(".", "/") + ".lean")
        imported = {repo.files[r].module for r in repo.visible(lean) if repo.files[r].runtime} if lean else {module}
        for dependency in sorted(imported):
            for premise in config["runtime_modules"].get(dependency, ()):
                reason = f"runtime module {dependency}"
                if dependency != module:
                    reason += f" (source import fallback for {module})"
                via.setdefault(premise, []).append(reason)
    apply_rules(config, via, tokens | unfolded, "closure")
    apply_rules(config, via, set(TOKEN_RE.findall(theorem.statement)), "statement")
    gate = any(repo.files[rel].gate_generated for rel in repo.visible(theorem.file))
    for rel in sorted(generated):
        profile, reason = profile_premises(config, repo.files[rel])
        for premise in [*config["generated_premises"], *profile]:
            via.setdefault(premise, []).append(f"generated {rel} ({reason})")
        for premise, binding in binding_premises(repo, rel, tokens):
            via.setdefault(premise, []).append(f"generated {rel} (extern model binding {binding})")
    if gate:
        for premise in [*config["generated_premises"], config["profiles"]["gate-time"]]:
            via.setdefault(premise, []).append("gate-time generated import")
    return close(config, via)


def premise_key(pid: str) -> tuple:
    order = ["PRF", "ALC", "IOM", "THR", "ORD", "TMR", "MTH", "ASM", "SEM", "STK", "EXT", "TRU"]
    prefix = pid.split("-")[0]
    return (order.index(prefix) if prefix in order else len(order), pid)


def is_excluded(config: dict, rel: str) -> bool:
    return any(rel.startswith(prefix) for prefix in config["excluded"])


THEOREM_KINDS = {"theorem", "lemma", "example"}


def theorem_files(repo: Repository) -> list[LeanFile]:
    """The indexed theorem files. scripts/theorem_universe.py compiles and audits exactly these."""
    roots = tuple(f"{r}/" for r in repo.config["theorem_roots"])
    return [repo.files[rel] for rel in sorted(repo.files)
            if rel.startswith(roots) and not is_excluded(repo.config, rel)
            and any(d.kind in THEOREM_KINDS for d in repo.files[rel].decls)]


def build_index(repo: Repository) -> tuple[list[dict], list[str]]:
    errors: list[str] = []
    entries = []
    for lean in theorem_files(repo):
        rel = lean.rel
        theorems = [d for d in lean.decls if d.kind in THEOREM_KINDS]
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
                via = derive(repo, theorem)
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
             "Kernel rows use the checked declaration closure. Source fallback rows retain the",
             "conservative module/tactic approximation for declarations absent from the audit.", "",
             f"{len(entries)} theorems in {len({e['file'] for e in entries})} files.", "",
             "| Premise | Theorems | Dropped from source baseline | Title |", "|---|---|---|---|"]
    for pid in sorted(premises, key=premise_key):
        count = sum(pid in e["premises"] for e in entries)
        dropped = sum(pid in e.get("dropped", ()) for e in entries)
        lines.append(f"| [{pid}](premises.md#{pid.lower()}) | {count} | {dropped} | {premises[pid]['title']} |")
    current = None
    for entry in entries:
        if entry["file"] != current:
            current = entry["file"]
            union = sorted({p for e in entries if e["file"] == current for p in e["premises"]}, key=premise_key)
            lines += ["", f"## `{current}`", "", f"File premises: {', '.join(union)}", "",
                      "| Theorem | Premises | Derivation |", "|---|---|---|"]
        lines.append(f"| `{entry['theorem']}` | {', '.join(entry['premises'])} | "
                     f"{entry.get('derivation', 'source fallback')} |")
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
    for tactic, modules in sorted(repo.config.get("tactic_modules", {}).items()):
        errors += [f"tactic_modules.{tactic} names {m}, which is not a mapped runtime module"
                   for m in modules if m not in mapping]
    for pid, carrier in repo.config.get("declaration_carriers", {}).items():
        for name in [*carrier["declarations"], *carrier["namespaces"]]:
            if name not in repo.table:
                errors.append(f"declaration carrier {pid} names missing declaration {name}")
            for decl in repo.table.get(name, ()):
                if decl.file.runtime and decl.file.rel not in repo.config.get("carrier_coverage", {}):
                    errors.append(f"declaration carrier {pid} has no coverage review for {decl.file.rel}")
    errors += carrier_coverage_errors(repo.root, repo.config)
    return errors


def carrier_coverage_errors(root: Path, config: dict) -> list[str]:
    """A model/rule edit invalidates its carrier coverage review instead of silently losing a
    newly introduced semantic dependency. The subset property alone cannot establish this."""
    errors = []
    for rel, digest in config.get("carrier_coverage", {}).items():
        path = root / rel
        if not path.is_file() or file_sha256(path) != digest:
            errors.append(f"declaration carrier coverage is stale for {rel}; re-review carriers or retain module fallback")
    return errors


def kernel_inputs(repo: Repository) -> str:
    """Bind cached extraction to every source, carrier and extractor input, including clients
    whose staged olean has no repository-relative source in the assurance freshness record."""
    paths = {f.path for f in repo.files.values()}
    paths.update(repo.root / p for p in (
        "tools/Assurance.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/premises.py", "scripts/assumptions.py", "scripts/theorem_universe.py",
        "scripts/premise_markers.py", "assurance/premises.json", "assurance/policy.json",
        "assurance/float-semantics.json"))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(repo.root)).encode() + b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    toolchain = subprocess.run(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=repo.root,
                               text=True, capture_output=True, check=True).stdout.strip()
    digest.update(toolchain_runtime_sha256(Path(toolchain)).encode())
    return digest.hexdigest()


def kernel_reports(repo: Repository):
    directory = repo.root / ".lake/premise-index"
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for path, sources in _kernel_reports(repo):
            yield json.loads(path.read_text()), sources


def reusable_shipped(root: Path, path: Path) -> bool:
    """Recover a completed shipped stage after a later stage fails. Revalidate the actual
    artifacts/extractor/binaries and current policy, rather than trusting an old cache key."""
    from assumptions import apply_policy, load_policy, needs_replay, shipped_modules, verify_artifacts
    try:
        report = json.loads(path.read_text())
        if (report.get("status") != "pass" or report.get("scope") != "all-shipped-modules"
                or report.get("modules") != shipped_modules(root)
                or report.get("kernel_replay", {}).get("status") != "pass"
                or not report.get("freshness", {}).get("toolchain_runtime_sha256")
                or report.get("policy_sha256") != file_sha256(root / "assurance/policy.json")):
            return False
        expected = set(report["modules"]) | {n["module"] for n in report["nodes"] if needs_replay(n["module"])}
        rows = report["freshness"]["artifacts"]
        if {r["module"] for r in rows} != expected:
            return False
        for row in rows:
            source = row["module"].replace(".", "/") + ".lean"
            if (root / source).is_file() and row.get("source") != source:
                return False
        verify_artifacts(report)
        extractor = report["extractor"]
        artifacts = {"source_sha256": root / "tools/Assurance.lean",
                     "lean_toolchain_sha256": root / "lean-toolchain", "lake_config_sha256": root / "lakefile.toml",
                     "olean_sha256": root / ".lake/build/lib/lean/tools/Assurance.olean",
                     "lake_trace_sha256": root / ".lake/build/lib/lean/tools/Assurance.trace"}
        if any(extractor.get(key) != file_sha256(file) for key, file in artifacts.items()):
            return False
        toolchain = subprocess.run(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=root,
                                   text=True, capture_output=True, check=True).stdout.strip()
        replay = report["kernel_replay"]
        if any(replay.get(field) != file_sha256(Path(toolchain) / "bin" / binary)
               for field, binary in (("lean_sha256", "lean"), ("tool_sha256", "leanchecker"))):
            return False
        current = apply_policy(report, load_policy(root / "assurance/policy.json"))
        return current["status"] == "pass" and current["theorems"] == report["theorems"]
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError):
        return False


def _kernel_reports(repo: Repository) -> list[tuple[Path, dict]]:
    """Use the existing kernel-replayed assurance pipeline, caching only verified artifacts.
    Missing/stale data is regenerated; a failed extraction never licenses a premise drop."""
    directory = repo.root / ".lake/premise-index"
    manifest = directory / "manifest.json"
    inputs = kernel_inputs(repo)

    def read() -> list[tuple[Path, dict]]:
        from assumptions import artifact_batch
        cache = json.loads(manifest.read_text())
        if cache["inputs"] != inputs:
            raise ValueError("premise dependency cache has stale inputs")
        reports = []
        with artifact_batch() as verify:
            for row in cache["reports"]:
                path = directory / row["report"]
                if file_sha256(path) != row["sha256"]:
                    raise ValueError(f"premise dependency cache changed: {path}")
                report = json.loads(path.read_text())
                if report.get("status") != "pass" or report.get("kernel_replay", {}).get("status") != "pass":
                    raise ValueError(f"premise dependency audit did not pass: {path}")
                if not report.get("freshness", {}).get("toolchain_runtime_sha256"):
                    raise ValueError(f"premise dependency audit has no toolchain runtime binding: {path}")
                if report.get("extractor", {}).get("toolchain_runtime_sha256") != report["freshness"]["toolchain_runtime_sha256"]:
                    raise ValueError(f"premise extractor has no matching toolchain runtime binding: {path}")
                # A content cache also works in CI's parentless checkout. Actual source,
                # artifact and toolchain bytes are checked, with no persistent digest memo.
                # Receipt provenance retains verify_fresh's strict revision check.
                verify(report)
                reports.append((path, row["sources"]))
                del report
        if not reports:
            raise ValueError("empty premise dependency cache")
        if inputs != kernel_inputs(repo):
            raise ValueError("premise inputs changed during cache validation")
        return reports

    try:
        return read()
    except (OSError, ValueError, KeyError):
        pass
    directory.mkdir(parents=True, exist_ok=True)
    manifest.unlink(missing_ok=True)
    # Do not add a second extractor: both scopes use tools/Assurance.lean and the existing
    # theorem-universe compiler, including its collision-safe bundles and gate-time exclusions.
    commands = [
        [sys.executable, "-B", "scripts/assumptions.py", "--output", str(directory / "shipped.json"),
         "--replay-cache", str(directory / "replay.json")],
        [sys.executable, "-B", "scripts/theorem_universe.py", "audit", "--no-build",
         "--output-dir", str(directory / "universe"),
         "--replay-cache", str(directory / "replay.json")],
    ]
    for i, command in enumerate(commands):
        if i == 0 and reusable_shipped(repo.root, directory / "shipped.json"):
            print("premises: reusing fully revalidated shipped audit", file=sys.stderr)
            continue
        guarded = [sys.executable, "-B", "scripts/build-guard.py", "--report", str(directory / f"guard-{i}.json"),
                   "--log", str(directory / f"guard-{i}.log"), "--rss-mib", "11000", "--timeout", "7200",
                   "--lock-wait", os.environ.get("AIR2LEAN_LOCK_WAIT", "3600"), "--", *command]
        subprocess.run(guarded, cwd=repo.root, check=True)
    universe = json.loads((directory / "universe/universe.json").read_text())
    if universe["status"] != "pass":
        raise ValueError("theorem-universe premise extraction failed")
    rows = [{"report": "shipped.json", "sources": {}}]
    for audit in universe["audits"]:
        if audit["status"] != "pass":
            continue  # A colliding bundle was split; its passing children supply the data.
        path = Path(audit["report"])
        number = path.stem.removeprefix("audit-")
        rows.append({"report": str(path.relative_to(directory)),
                     "sources": json.loads((path.parent / f"sources-{number}.json").read_text())})
    for row in rows:
        row["sha256"] = file_sha256(directory / row["report"])
    if inputs != kernel_inputs(repo):
        raise ValueError("premise inputs changed during extraction; retry")
    write_report(manifest, {"inputs": inputs, "reports": rows})
    return read()


def refine_index(repo: Repository, entries: list[dict]) -> list[str]:
    """Keep source fallback for anonymous examples and gate-time-only theorems."""
    errors, exact = [], {}
    for report, sources in kernel_reports(repo):
        derived = compiled(report, repo.root, repo.config, None)
        errors += derived["errors"]
        nodes = {n["name"]: n for n in report["nodes"]}
        for theorem in derived["theorems"]:
            module = theorem["module"]
            rel = sources.get(module, module.replace(".", "/") + ".lean")
            name = nodes[theorem["name"]].get("user_name", theorem["name"])
            key = (rel, name)
            if key in exact and exact[key]["premises"] != theorem["premises"]:
                errors.append(f"inconsistent compiled premises for {rel}: {name}")
            exact[key] = theorem
        del report, nodes, derived
    for entry in entries:
        theorem = exact.get((entry["file"], entry["theorem"]))
        entry["derivation"] = "kernel" if theorem else "source fallback (not present in audit)"
        if theorem is None:
            continue
        old = set(entry["premises"])
        if not set(theorem["premises"]) <= old:
            errors.append(f"{entry['file']}: {entry['theorem']}: compiled premises exceed source baseline: "
                          + ", ".join(sorted(set(theorem["premises"]) - old)))
            continue
        entry["module_premises"] = entry["premises"]
        entry["dropped"] = sorted(old - set(theorem["premises"]), key=premise_key)
        entry["premises"], entry["via"] = theorem["premises"], theorem["via"]
    return errors


def check(root: Path = ROOT, write: bool = False, kernel: bool = True,
          check_index: bool = True) -> tuple[list[str], list[dict]]:
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
    # `abi64-be-v1` (the big-endian model profile, T03) is optional for fixture configurations.
    if set(config["profiles"]) - {"abi64-be-v1"} != {"absent", "legacy-abi64-le", "abi64-le-v1", "gate-time"}:
        errors.append(f"{CONFIG}: profiles must map absent, legacy-abi64-le, abi64-le-v1 and gate-time "
                      "(and optionally abi64-be-v1)")
    repo = load_repository(root, config)
    errors += repo.errors + runtime_errors(repo)
    entries, index_errors = build_index(repo)
    errors += index_errors
    if kernel and config.get("kernel_index") and not errors:
        errors += refine_index(repo, entries)
    errors += memory_model_errors(config, entries, lambda e: f"{e['file']}: {e['theorem']}")
    errors += memory_model_record_errors(config, reports, root)
    for entry in entries:
        for pid in entry["premises"]:
            if pid not in premises:
                errors.append(f"{entry['file']}: {entry['theorem']} uses undefined premise {pid}")
    if not entries:
        errors.append("no theorems found; nothing was indexed")
    rendered = render_index(entries, premises)
    index = root / config["index"]
    if write and not errors:
        index.write_text(rendered)
    elif check_index and (not index.is_file() or index.read_text() != rendered):
        errors.append(f"{config['index']} is stale; run python3 scripts/premises.py write")
    return errors, entries


# ----------------------------------------------------------------------------- compiled graph

EQUATION_RE = re.compile(r"\.(?:eq_\d+|eq_def|eq_unfold)$")


def defining_module(node: dict, nodes: dict) -> str:
    """The module a declaration belongs to for premises. Lean realizes the equation lemmas of a
    definition (`d.eq_1`, `d.eq_def`) in the module whose proof first unfolds it, which can be
    another one than the definition's; they belong to the definition."""
    name = node["name"]
    parent = nodes.get(EQUATION_RE.sub("", name)) if EQUATION_RE.search(name) else None
    return (parent or node)["module"]


def declaration_hits(config: dict, names: set[str]) -> dict[str, list[str]]:
    """Reviewed semantic carriers; a namespace includes its root and all descendants."""
    return {pid: sorted(n for n in names if n in c["declarations"] or
                        any(n == ns or n.startswith(ns + ".") for ns in c["namespaces"]))
            for pid, c in config.get("declaration_carriers", {}).items()}


def reachable_carriers(config: dict, nodes: dict) -> dict[str, dict[str, str]]:
    """Propagate each carrier backwards once, sharing closure work across all theorems.
    Sorted seeds give a stable, lexicographically first witness, also in cyclic graphs."""
    reverse: dict[str, list[str]] = {}
    users: dict[str, list[str]] = {}
    for name, node in nodes.items():
        users.setdefault(node.get("user_name", name), []).append(name)
        for dependency in node["dependencies"]:
            if dependency not in nodes:
                raise ValueError(f"incomplete declaration graph: {name} -> {dependency}")
            reverse.setdefault(dependency, []).append(name)
    reached = {}
    for pid, seeds in declaration_hits(config, set(users)).items():
        witnesses: dict[str, str] = {}
        for seed in seeds:
            pending = list(users[seed])
            while pending:
                name = pending.pop()
                if name in witnesses:
                    continue
                witnesses[name] = seed
                pending.extend(reverse.get(name, ()))
        reached[pid] = witnesses
    return reached


def compiled(report: dict, root: Path, config: dict, source: list[dict] | None) -> dict:
    """Derive premises from the kernel dependency graph of scripts/assumptions.py."""
    if report.get("schema_version") != 1 or report.get("status") != "pass":
        raise ValueError("assumption report is not a passing schema-1 audit")
    nodes = {n["name"]: n for n in report["nodes"]}
    if len(nodes) != len(report["nodes"]):
        raise ValueError("duplicate declaration in premise dependency graph")
    errors, theorems, skipped = carrier_coverage_errors(root, config), [], 0
    carriers = reachable_carriers(config, nodes) if config.get("declaration_carriers") else {}
    errors += [f"dependency {n['name']} is unresolved in the checked environment"
               for n in nodes.values() if n["kind"] == "unresolved"]
    profiles: dict[str, tuple[list[str], str]] = {}
    markers = GeneratedMarkers(root)
    # Kernel names of private declarations carry a `_private.<module>.0.` prefix; rules and the
    # source comparison use the user-facing name so module paths cannot trigger token rules.
    def user(name: str) -> str:
        return nodes[name].get("user_name", name) if name in nodes else name

    by_name: dict[tuple[str, str], set] = {}
    for entry in source or ():
        key = (module_name(Path(entry["file"])), entry["theorem"])
        by_name.setdefault(key, set()).update(entry["premises"])

    def external(module: str) -> bool:
        return module.split(".")[0] in EXTERNAL_IMPORTS

    for theorem in report["theorems"]:
        if is_runtime(theorem["module"]):
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
            if node["kind"] == "unresolved":
                errors.append(f"{theorem['name']}: dependency {name} is unresolved in the checked environment")
            module = defining_module(node, nodes)
            if is_runtime(module):
                modules.add(module)
                names.add(user(name))
                continue
            if external(module):
                continue
            names.add(user(name))
            if node["kind"] == "axiom" and name not in STANDARD_AXIOMS:
                for premise in config["source_axiom"]:
                    via.setdefault(premise, []).append(f"axiom {name}")
            if module.split(".")[-1] == "Gen":
                generated.add(module)
                apply_markers(via, user(name), markers.of(module, user(name)))
            pending.extend(node["dependencies"])
        for axiom in theorem.get("axioms", ()):
            if axiom not in STANDARD_AXIOMS:
                for premise in config["source_axiom"]:
                    via.setdefault(premise, []).append(f"axiom {axiom}")
        # The premises the audit classified its generated axioms and opaques by
        # (assurance/policy.json `generated_declarations`, e.g. an extern binding's EXT-03).
        for premise in theorem.get("declaration_premises", ()):
            via.setdefault(premise, []).append("generated declaration")
        for module in sorted(modules):
            if module not in config["runtime_modules"]:
                errors.append(f"{theorem['name']}: runtime module {module} has no premise mapping")
            for premise in config["runtime_modules"].get(module, ()):
                via.setdefault(premise, []).append(f"runtime module {module}")
        apply_rules(config, via, names, "closure")
        # Statement rules see the kernel type's edges (`statement_dependencies`, as the source
        # index sees the theorem's own statement); a report without them falls back to every
        # direct edge, type and proof.
        statement = theorem.get("statement_dependencies", nodes[theorem["name"]]["dependencies"])
        apply_rules(config, via, {user(n) for n in statement}, "statement")
        for module in sorted(generated):
            if module not in profiles:
                path = generated_path(root, module)
                if path.is_file():
                    header = profile_header(path.read_text())
                    profiles[module] = profile_premises(config, LeanFile(path, module, module, [], header))
                else:
                    profiles[module] = ([config["profiles"]["gate-time"]], "generated module not in repository")
            profile, reason = profiles[module]
            for premise in [*config["generated_premises"], *profile]:
                via.setdefault(premise, []).append(f"generated {module} ({reason})")
        baseline = set(close(config, {p: [] for p in via}))
        if carriers:
            for pid, carrier in config["declaration_carriers"].items():
                # Remove only the reviewed coarse module attributions. Explicit markers,
                # token rules, generated admissions and unreviewed modules keep their premise.
                reasons = [r for r in via.get(pid, ()) if not any(
                    r == f"runtime module {m}" for m in carrier["modules"])]
                witness = carriers[pid].get(theorem["name"])
                if witness and pid in baseline:
                    reasons.append(f"declaration {witness}")
                if reasons:
                    via[pid] = reasons
                else:
                    via.pop(pid, None)
        via = close(config, via)
        if not set(via) <= baseline:
            errors.append(f"{theorem['name']}: declaration premises exceed the module baseline")
        entry = {"name": theorem["name"], "module": theorem["module"],
                 "premises": sorted(via, key=premise_key), "via": via,
                 "module_premises": sorted(baseline, key=premise_key),
                 "dropped": sorted(baseline - set(via), key=premise_key)}
        if source is not None:
            known = by_name.get((theorem["module"], user(theorem["name"])))
            if known is not None:
                entry["source_gaps"] = sorted(set(entry["premises"]) - known, key=premise_key)
                if entry["source_gaps"]:
                    entry["gap_via"] = {p: sorted(set(via[p])) for p in entry["source_gaps"]}
        theorems.append(entry)
    errors += markers.errors
    errors += memory_model_errors(config, theorems, lambda t: t["name"])
    gaps = [t for t in theorems if t.get("source_gaps")]
    return {"schema_version": 1, "status": "fail" if errors else "pass",
            "theorem_count": len(theorems), "runtime_theorems_skipped": skipped,
            "source_gap_count": len(gaps), "errors": errors, "theorems": theorems,
            "drop_counts": {p: sum(p in t["dropped"] for t in theorems)
                            for p in sorted({p for t in theorems for p in t["dropped"]}, key=premise_key)}}


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
            source_errors, entries = check(root, kernel=False, check_index=False)
            if source_errors:
                raise ValueError("; ".join(source_errors))
            report = compiled(json.loads(args.assurance.read_text()), root, config, entries)
            write_report(args.output, report)
            for error in report["errors"]:
                print(f"  {error}", file=sys.stderr)
            print(f"premises {report['status']}: {report['theorem_count']} compiled theorems, "
                  f"{report['source_gap_count']} with source-index gaps; report: {args.output}", file=sys.stderr)
            return 1 if report["errors"] or (args.strict and report["source_gap_count"]) else 0
        errors, entries = check(root, write=command == "write")
    except (OSError, ValueError, KeyError, re.error, subprocess.CalledProcessError) as error:
        print(f"premise error: {error}", file=sys.stderr)
        return 2
    if command == "explain":
        matches = [e for e in entries if e["theorem"] == args.theorem or e["theorem"].endswith("." + args.theorem)]
        if not matches:
            print(f"no indexed theorem named {args.theorem}", file=sys.stderr)
            return 1
        for entry in matches:
            print(f"{entry['theorem']} ({entry['file']}:{entry['line']})")
            print(f"  derivation: {entry.get('derivation', 'source fallback')}")
            if entry.get("dropped"):
                print("  dropped from source baseline: " + ", ".join(entry["dropped"]))
            for pid in entry["premises"]:
                print(f"  {pid}: {'; '.join(dict.fromkeys(entry['via'][pid]))}")
        return 0
    if command == "json":
        write_report(args.output, [{k: e[k] for k in ("file", "theorem", "line", "premises", "derivation",
                                                      "module_premises", "dropped") if k in e} for e in entries])
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    status = "fail" if errors else "pass"
    print(f"premises {status}: {len(entries)} theorems indexed", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
