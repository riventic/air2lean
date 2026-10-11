"""The translator's caller-obligation markers (W1; docs/premises.md ALC-09, IOM-01).

`Air2Lean/Emit.lean` (`interfacePremiseMarker`) writes `-- air2lean-premises: {"ALC-09":[0]}`
on the line before each generated `def` with a parameter that contains a `std.mem.Allocator`
(ALC-09) or a `std.Io` (IOM-01), with the indices of those parameters. scripts/premises.py
derives the premises from them per theorem; proof receipts and scripts/claims.py list them per
audited theorem (`caller_obligations`). Kept small and dependency-free: the proof-receipt
suite runs under a 32 MiB budget.
"""
from __future__ import annotations

import json
from pathlib import Path
import re

MARKER = "-- air2lean-premises:"
MARKER_RE = re.compile(r"^-- air2lean-premises: (\{.*\})$")
ID_RE = re.compile(r"[A-Z]{3}-\d{2}")
DEF_RE = re.compile(r"^def\s+([^\s(:]+)")
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")


def markers(raw: str, rel: str) -> tuple[dict[int, dict], list[str]]:
    """`{line of the marked declaration: {premise: parameters}}` and malformed-marker errors."""
    found, errors = {}, []
    for number, line in enumerate(raw.split("\n"), 1):
        if not line.startswith(MARKER):
            continue
        match = MARKER_RE.match(line)
        try:
            record = json.loads(match.group(1)) if match else None
        except json.JSONDecodeError:
            record = None
        if (not isinstance(record, dict) or not record or
                not all(ID_RE.fullmatch(k) and isinstance(v, list) and v and
                        all(type(i) is int and i >= 0 for i in v) for k, v in record.items())):
            errors.append(f"{rel}:{number}: malformed air2lean-premises marker")
            continue
        found[number + 1] = record
    return found, errors


def definitions(raw: str, rel: str) -> tuple[dict[str, dict], list[str]]:
    """`{namespaced def name: marker}` of one generated module (one top-level `namespace`)."""
    found, errors = markers(raw, rel)
    lines = raw.split("\n")
    namespace = next((m.group(1) for line in lines if (m := NAMESPACE_RE.match(line))), "")
    named = {}
    for number, record in found.items():
        match = DEF_RE.match(lines[number - 1]) if number <= len(lines) else None
        if match is None:
            errors.append(f"{rel}:{number - 1}: air2lean-premises marker does not precede a def")
            continue
        # A keyword name is escaped (`def «at»`); its kernel name is `at`.
        name = match.group(1).replace("«", "").replace("»", "")
        named[f"{namespace}.{name}" if namespace else name] = record
    return named, errors


def module_path(root: Path, module: str) -> Path:
    return root / Path(*module.split(".")).with_suffix(".lean")


class GeneratedMarkers:
    """The markers of generated modules, read once per module."""

    def __init__(self, root: Path):
        self.root, self.errors, self.by_module = root, [], {}

    def of(self, module: str, name: str) -> dict:
        if module not in self.by_module:
            path = module_path(self.root, module)
            named, errors = definitions(path.read_text(), str(path.relative_to(self.root))) \
                if path.is_file() else ({}, [])
            self.errors += errors
            self.by_module[module] = named
        return self.by_module[module].get(name, {})


def caller_obligations(report: dict, root: Path) -> dict[str, list[str]]:
    """Per audited theorem, the caller-obligation premises of the marked generated definitions
    its kernel dependency graph reaches. Theorems with none are omitted."""
    nodes = {n["name"]: n for n in report["nodes"]}
    generated = GeneratedMarkers(root)
    reverse: dict[str, set[str]] = {}
    pending: list[tuple[str, str]] = []
    for name, node in nodes.items():
        for dep in node["dependencies"]:
            reverse.setdefault(dep, set()).add(name)
        if node["module"].split(".")[-1] == "Gen":
            pending += [(name, p) for p in generated.of(node["module"], node.get("user_name", name))]
    if generated.errors:
        raise ValueError("; ".join(generated.errors))
    # Propagate each marked premise backwards along dependency edges.
    reached: dict[str, set[str]] = {}
    while pending:
        name, premise = pending.pop()
        if premise in reached.setdefault(name, set()):
            continue
        reached[name].add(premise)
        pending += [(user, premise) for user in reverse.get(name, ())]
    return {t["name"]: sorted(reached[t["name"]]) for t in report["theorems"] if reached.get(t["name"])}
