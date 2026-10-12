#!/usr/bin/env python3
"""Ratchet: one proof framework (docs/proof-framework.md, CLAUDE.md "One proof framework").

Proofs use the full-state logic (`FTriple`, `FTotalTriple`, `CTriple`) and the symbolic executor
`fsym`; the library grows by lemmas and `@[fsym]` rules only. `assurance/proof-framework.json`
lists what exists today, so that nothing parallel is added:

* `judgments`: every definition of a program judgment in a tracked Lean file: a `def`, `abbrev`,
  `structure`, `class`, `inductive` or `opaque` whose name ends in one of `SUFFIXES` (`Triple`,
  `Returns`, `Within`, `Template`, `Spec`, …), with its module and status;
* `tactics`: every tactic declaration (`syntax`/`macro`/`elab` … `: tactic`, kind `syntax`) and
  every extension of a tactic declared elsewhere (`macro_rules`/`elab_rules` alternatives for
  `` `(tactic| kw …) ``, kind `rules`), by keyword, module and status;
* `legacy_users`: every Lean file that uses the legacy separation logic (imports a module of
  `LEGACY_MODULES` or names a legacy triple, `LEGACY_NAMES`), by path.

Status is `target` (the framework) or `legacy-to-retire` (to be migrated and deleted). The check
fails on an entry that the tree has and the file lacks (a new judgment, tactic or legacy user), on
an entry that the file has and the tree lacks (delete it), and, with a base revision (`--base`;
in CI the pull request's base branch or `main`), on an entry that the base's file lacks unless it
records the coordinator's approval (`"approved": "<who, date, where>"`): the file only shrinks
except by an explicit, reviewed decision.

Usage: scripts/proof-framework.py [--root DIR] [--base REV] [--write]
  --write   rewrite the file from the tree (keeps statuses and approvals; a new entry gets
            `legacy-to-retire` and no approval, which the base comparison then refuses)
Exit 1 with one line per violation.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

FILE = "assurance/proof-framework.json"
STATUSES = ("target", "legacy-to-retire")

# Names of program judgments (relations between a precondition, a program and a postcondition,
# their total/bounded/eventual forms, and the templates and contracts built from them).
SUFFIXES = ("Triple", "TripleIn", "Returns", "ReturnsUnder", "Within", "Stk", "Stops", "Turns",
            "Halts", "Template", "Spec")
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|structure|class|inductive|opaque)\s+([A-Za-z_][\w.]*)", re.M)
TACTIC_DECL = re.compile(r"(?:@\[[^\]]*\]\s*)*(?:(?:scoped|local)\s+)?(?:syntax|macro|elab)\b")
TACTIC_RULES = re.compile(r"(?:@\[[^\]]*\]\s*)*(?:(?:scoped|local)\s+)?(?:macro_rules|elab_rules)\b")
TACTIC_RULE = re.compile(r"^\s*(?:macro_rules|elab_rules[^|]*)?\s*\|\s*`\(tactic\|\s*([^\s$)\]]+)", re.M)
STRING = re.compile(r'"([^"\\]*(?:\\.[^"\\]*)*)"')

# The legacy separation logic, deleted in Plan A's last phase. The base vocabulary that stays
# (`Sep/Heap`, `Sep/Assert`, `Sep/AllocSpec/{Region,Norm,Ops}`) is not listed. `Sep/Triple` also
# holds the vocabulary (`pts`, `arr`): until that is split out, its importers count as users.
LEGACY_MODULES = re.compile(
    r"^ZigLean\.Sep(\.(Triple|Total|Bounded|Loop|LoopTemplate|DispatchTemplate|Step|Automation"
    r"|Array|Array\.\w+|Block|Try|TryAlias|Discard|Sentinel|SentinelRealloc|Remap|RawAlloc|Alloc"
    r"|Owned|OsMalloc|ArenaClient|AddrReuse|Cost|Witness|Mmap|AllocSpec"
    r"|AllocSpec\.(Wrap|Wrappers|Dispatch|Toy)|Full\.Pinned))?$"
    r"|^ZigLean\.Conc\.Own$")
LEGACY_NAMES = re.compile(r"\b(Triple|TotalTriple|TotalTripleIn|TTriple|TTripleIn|TotalTripleWithin)\b")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
# The framework's own judgments and automation.
TARGET_JUDGMENTS = {"FTriple", "FTotalTriple", "FReturns", "CTriple", "FAllocSpec"}
TARGET_TACTIC = re.compile(r"^fsym")


def strip_comments_and_strings(text, keep_strings=False):
    """`text` without `--` line comments and nestable `/- … -/` blocks (newlines kept), and
    without string literals unless `keep_strings`."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if keep_strings:
                out.append(text[i:j + 1])
            i = j + 1
        elif text[i] == "'" and i + 2 < n and text[i + 2] == "'":  # a character literal 'x'
            out.append(text[i:i + 3] if keep_strings else "")
            i += 3
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def chunks(code, start):
    """The declarations whose first line matches `start`, each with its continuation (the
    following lines indented deeper)."""
    lines = code.splitlines()
    for i, line in enumerate(lines):
        if not start.match(line.lstrip()):
            continue
        indent = len(line) - len(line.lstrip())
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > indent):
            j += 1
        yield "\n".join([line.lstrip()] + lines[i + 1:j])


def module_of(path):
    return path[:-len(".lean")].replace("/", ".")


def scan_file(path, text):
    """(judgments, tactics, legacy reason) of one file."""
    code = strip_comments_and_strings(text, keep_strings=True)
    judgments, tactics = set(), set()
    for name in DECL.findall(code):
        if name.split(".")[-1].endswith(SUFFIXES) and name.split(".")[-1][:1].isupper():
            judgments.add(name)
    for chunk in chunks(code, TACTIC_DECL):
        s = STRING.search(chunk)
        if s and re.search(r":\s*tactic\b", chunk):
            tactics.add(("syntax", s.group(1).strip()))
    for chunk in chunks(code, TACTIC_RULES):
        tactics.update(("rules", kw) for kw in TACTIC_RULE.findall(chunk))
    # Rules for a tactic declared in the same file are its implementation, not an extension.
    tactics -= {("rules", kw) for kind, kw in tactics if kind == "syntax"}
    legacy = None
    for module in IMPORT.findall(text):
        if LEGACY_MODULES.match(module):
            legacy = f"imports {module}"
            break
    if legacy is None:
        m = LEGACY_NAMES.search(strip_comments_and_strings(text))
        legacy = f"names {m.group(1)}" if m else None
    return judgments, tactics, legacy


def tracked_lean(root):
    out = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
                         check=True, capture_output=True).stdout.decode()
    return sorted(p for p in out.split("\0") if p)


def scan(root):
    """The tree's entries, keyed for comparison."""
    judgments, tactics, users = {}, {}, {}
    for path in tracked_lean(root):
        js, ts, legacy = scan_file(path, (root / path).read_text(encoding="utf-8"))
        mod = module_of(path)
        for name in js:
            judgments[(name, mod)] = {"name": name, "module": mod}
        for kind, kw in ts:
            tactics[(kw, kind, mod)] = {"tactic": kw, "kind": kind, "module": mod}
        if legacy:
            users[path] = legacy
    return judgments, tactics, users


def entry_keys(data):
    """Every entry of the file by its key, with the entry."""
    out = {}
    for e in data.get("judgments", []):
        out[("judgment", e["name"], e["module"])] = e
    for e in data.get("tactics", []):
        out[("tactic", e["tactic"], e["kind"], e["module"])] = e
    for e in data.get("legacy_users", []):
        out[("legacy user", e["path"])] = e
    return out


def keys(data):
    k = entry_keys(data)
    return ({x[1:] for x in k if x[0] == "judgment"}, {x[1:] for x in k if x[0] == "tactic"},
            {x[1] for x in k if x[0] == "legacy user"})


def default_status(entry):
    if "name" in entry:
        return "target" if entry["name"].split(".")[-1] in TARGET_JUDGMENTS else "legacy-to-retire"
    return "target" if TARGET_TACTIC.match(entry["tactic"]) else "legacy-to-retire"


def render(judgments, tactics, users, old):
    known = entry_keys(old)

    def keep(key, e):
        prev = known.get(key, {})
        out = dict(e)
        if "path" not in e:
            out["status"] = prev.get("status", default_status(e))
        if "approved" in prev:
            out["approved"] = prev["approved"]
        return out

    js = [keep(("judgment", *k), e) for k, e in sorted(judgments.items())]
    ts = [keep(("tactic", *k), e) for k, e in sorted(tactics.items())]
    us = [keep(("legacy user", p), {"path": p}) for p in sorted(users)]
    return {
        "description": "One proof framework (docs/proof-framework.md): the program judgments, "
                       "tactics and legacy-logic users that exist. Only shrinks; additions need "
                       "the coordinator (scripts/proof-framework.py).",
        "judgments": js,
        "tactics": ts,
        "legacy_users": us,
    }


def base_revision(root, explicit):
    """`--base`, else in CI the pull request's base branch (`GITHUB_BASE_REF`) or `main`
    (merge queue, pushes), fetched shallowly if missing."""
    if explicit:
        return explicit
    if not os.environ.get("GITHUB_ACTIONS"):
        return None
    branch = os.environ.get("GITHUB_BASE_REF") or "main"
    ref = f"refs/remotes/origin/{branch}"
    if subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "-q", ref],
                      capture_output=True).returncode != 0:
        subprocess.run(["git", "-C", str(root), "fetch", "-q", "--depth=1", "origin",
                        f"+refs/heads/{branch}:{ref}"], check=True)
    return ref


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--base")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args(argv)
    root, path = args.root, args.root / FILE
    old = json.loads(path.read_text()) if path.exists() else {}
    judgments, tactics, users = scan(root)
    if args.write:
        path.write_text(json.dumps(render(judgments, tactics, users, old), indent=2) + "\n")
        old = json.loads(path.read_text())
    errors = []
    for e in old.get("judgments", []) + old.get("tactics", []):
        if e.get("status") not in STATUSES:
            errors.append(f"{FILE}: {e} has no status among {STATUSES}")
    fj, ft, fu = keys(old)
    hint = "use the full-state logic and fsym (docs/proof-framework.md); a new one is a coordinator decision"
    for name, mod in sorted(set(judgments) - fj):
        errors.append(f"{mod}: new program judgment `{name}`; {hint}")
    for kw, kind, mod in sorted(set(tactics) - ft):
        errors.append(f"{mod}: new tactic {kind} `{kw}`; {hint}")
    for p in sorted(set(users) - fu):
        errors.append(f"{p}: uses the legacy logic ({users[p]}); {hint}")
    for name, mod in sorted(fj - set(judgments)):
        errors.append(f"{FILE}: judgment `{name}` ({mod}) is gone; delete its entry")
    for kw, kind, mod in sorted(ft - set(tactics)):
        errors.append(f"{FILE}: tactic {kind} `{kw}` ({mod}) is gone; delete its entry")
    for p in sorted(fu - set(users)):
        errors.append(f"{FILE}: {p} no longer uses the legacy logic; delete it from legacy_users")
    rev = base_revision(root, args.base)
    if rev:
        r = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{FILE}"], capture_output=True)
        if r.returncode == 0:
            before = entry_keys(json.loads(r.stdout))
            for k, e in sorted(entry_keys(old).items(), key=lambda x: str(x[0])):
                if k not in before and not e.get("approved"):
                    errors.append(f"{FILE}: {k} is not in {rev}'s file; the file only shrinks "
                                  "(an addition records the coordinator's approval: \"approved\")")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print(f"proof-framework: {len(fj)} judgments, {len(ft)} tactic entries, "
              f"{len(fu)} legacy users; nothing new")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
