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

sys.path.insert(0, str(Path(__file__).resolve().parent))
from assumptions import STANDARD_AXIOMS, write_report  # noqa: E402

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
                    # Proofs/Threadsync/Lock.lean's block for one OS's translation.
                    "if_decl", "end_if"}
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
COMMAND_RE = re.compile(r"^" + ATTRS + MODIFIERS + r"([#A-Za-z_][A-Za-z_0-9]*)")
ATTR_ONLY_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)+$")
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿][A-Za-z_0-9'!?À-ɏͰ-Ͽἀ-῿₀-ₜ]*"
TOKEN_RE = re.compile(IDENT + r"(?:\." + IDENT + r")*")
NAME_RE = re.compile(r"\s*(" + IDENT + r"(?:\." + IDENT + r")*)")
CTOR_RE = re.compile(r"\|\s*(" + IDENT + r")")
# `.ctor` with an expected type (`throw .unspecified`), not a field access on a term.
DOT_CTOR_RE = re.compile(r"(?<![\w.'!?)\]}⟩])\.(" + IDENT + r")")
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
        return is_runtime(self.module)

    @property
    def generated(self) -> bool:
        return self.path.name == "Gen.lean"


def module_name(rel: Path) -> str:
    return ".".join(rel.with_suffix("").parts)


def binders(text: str) -> list[tuple[str, str]]:
    """(name, type head) of every explicit binder group in `text`."""
    return [(name, match.group(2)) for match in BINDER_RE.finditer(text) for name in match.group(1).split()]


def type_head(decl: Decl) -> str:
    """The head name of a binder-free constant's declared type, `def S : Sem Ph where` -> `Sem`."""
    text = re.split(r":=|\bwhere\b", statement_of(decl.text), maxsplit=1)[0]
    colon = top_level(text, ":")
    if colon < 0 or binders(text[:colon]):
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
            conditions = tuple(s[4] for s in scopes if s[0] == "if_decl")
            decl = Decl(full, keyword, lean, number, body, namespaces, opens, conditions)
            decl.tokens = set(TOKEN_RE.findall(body))
            decl.dot_ctors = set(DOT_CTOR_RE.findall(body))
            for name, head in [*file_vars, *(b for s in scopes for b in s[3]), *binders(body)]:
                decl.binders.setdefault(name, set()).add(head)
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
        field_name = rest.split(".")[0]
        hits = []
        for head in decl.binders[local]:
            for owner in typed(head, depth + 1) or lookup(head):
                hits += [t for t in repo.table.get(f"{owner.name}.{field_name}", ()) if t.file.rel in visible]
        return hits

    found: dict[int, Decl] = {}
    for name in decl.dot_ctors:
        # The expected type is unknown in source: resolve only a constructor name that exactly one
        # visible inductive declares. Ambiguous names (generated exits, phases) are left out.
        owners = {id(t): t for t in repo.ctors.get(name, ()) if t.file.rel in visible}
        if len(owners) == 1 and decl not in owners.values():
            found.update(owners)
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


def derive(repo: Repository, theorem: Decl) -> dict[str, list[str]]:
    config = repo.config
    via: dict[str, list[str]] = {p: ["universal"] for p in config["universal"]}
    seen, pending, tokens = {id(theorem)}, [theorem], set()
    runtime: set[str] = set()
    generated: set[str] = set()
    visible = repo.visible(theorem.file)
    instances = [(d, need) for d, need in repo.instances() if d.file.rel in visible]

    def visit(target: Decl) -> None:
        if target.name:
            tokens.add(target.name)  # as in the kernel graph, rules also see resolved names
        if target.file.runtime:
            runtime.add(target.file.module)
            seen.add(id(target))
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
    for module in sorted(runtime):
        for premise in config["runtime_modules"].get(module, ()):
            via.setdefault(premise, []).append(f"runtime module {module}")
    apply_rules(config, via, tokens, "closure")
    apply_rules(config, via, set(TOKEN_RE.findall(theorem.statement)), "statement")
    gate = any(repo.files[rel].gate_generated for rel in repo.visible(theorem.file))
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
            module = node["module"]
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
        apply_rules(config, via, {user(n) for n in nodes[theorem["name"]]["dependencies"]}, "statement")
        for module in sorted(generated):
            if module not in profiles:
                path = root / Path(*module.split(".")).with_suffix(".lean")
                if path.is_file():
                    header = profile_header(path.read_text())
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
            known = by_name.get((theorem["module"], user(theorem["name"])))
            if known is not None:
                entry["source_gaps"] = sorted(set(entry["premises"]) - known, key=premise_key)
                if entry["source_gaps"]:
                    entry["gap_via"] = {p: sorted(set(via[p])) for p in entry["source_gaps"]}
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
            write_report(args.output, report)
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
        write_report(args.output, [{k: e[k] for k in ("file", "theorem", "line", "premises")} for e in entries])
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    status = "fail" if errors else "pass"
    print(f"premises {status}: {len(entries)} theorems indexed", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
