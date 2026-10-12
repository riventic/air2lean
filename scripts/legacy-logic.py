#!/usr/bin/env python3
"""Ratchet: the legacy proof logic only loses users (docs/one-logic.md, Plan A).

The full-state logic (`FTriple`, `FTotalTriple`, `CTriple` and `fsym`, docs/sep-full-state.md)
replaces the legacy separation logic (`Triple`, `TotalTriple`, `TTriple` and the rule modules
built on them). A tracked Lean file *uses the legacy logic* when

* it imports a legacy module (`LEGACY_MODULES`), or
* its code (comments and string literals excluded) names a legacy triple (`LEGACY_NAMES`).

Every such file must be listed in `scripts/legacy-logic-users.txt` (the allow-list), and every
listed file must still use the legacy logic, so the list is exact: a migrated file leaves it in
the same change. A file that is not listed fails the check, so no new user appears. With a base
revision (`--base REV`; in CI the base branch, see `base_revision`), the list may only shrink:
an entry that the base's list lacks fails too.

Usage: scripts/legacy-logic.py [--root DIR] [--base REV] [--write]
  --write   rewrite the allow-list to the current users (only to create it, or to drop entries;
            the check still refuses additions against the base)
Exit 1 with one line per violation.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

ALLOW = "scripts/legacy-logic-users.txt"

# Modules of the legacy logic (to be deleted in Plan A's last phase). The base vocabulary that
# stays (`Sep/Heap`, `Sep/Assert`, `Sep/AllocSpec/{Region,Norm,Ops}`) is not listed. `Sep/Triple`
# is listed although it also holds the vocabulary (`pts`, `arr`): until that is split out, its
# importers count as users.
LEGACY_MODULES = re.compile(
    r"^ZigLean\.Sep(\.(Triple|Total|Bounded|Loop|LoopTemplate|DispatchTemplate|Step|Automation"
    r"|Array|Array\.\w+|Block|Try|TryAlias|Discard|Sentinel|SentinelRealloc|Remap|RawAlloc|Alloc"
    r"|Owned|OsMalloc|ArenaClient|AddrReuse|Cost|Witness|Mmap|AllocSpec"
    r"|AllocSpec\.(Wrap|Wrappers|Dispatch|Toy)|Full\.Pinned))?$"
    r"|^ZigLean\.Conc\.Own$"
)
# The legacy triples. `FTriple`, `CTriple`, `FTotalTriple`, `ofTriple` are other words.
LEGACY_NAMES = re.compile(r"\b(Triple|TotalTriple|TotalTripleIn|TripleIn|TTriple)\b")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def strip_comments_and_strings(text):
    """`text` without `--` line comments, nestable `/- … -/` blocks and string literals."""
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
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif text[i] == "'" and i + 2 < n and text[i + 2] == "'":  # a character literal 'x'
            i += 3
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def uses_legacy(text):
    """Why a file uses the legacy logic (an import or a name), or None."""
    for module in IMPORT.findall(text):
        if LEGACY_MODULES.match(module):
            return f"imports {module}"
    m = LEGACY_NAMES.search(strip_comments_and_strings(text))
    return f"names {m.group(1)}" if m else None


def tracked_lean(root):
    out = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
                         check=True, capture_output=True).stdout.decode()
    return sorted(p for p in out.split("\0") if p)


def read_list(text):
    return {line.strip() for line in text.splitlines() if line.strip() and not line.startswith("#")}


def base_revision(root, explicit):
    """The revision whose allow-list bounds this one: `--base`, else in CI the pull request's base
    branch (`GITHUB_BASE_REF`) or `main` (merge queue, pushes), fetched shallowly if missing."""
    if explicit:
        return explicit
    if not os.environ.get("GITHUB_ACTIONS"):
        return None
    branch = os.environ.get("GITHUB_BASE_REF") or "main"
    ref = f"refs/remotes/origin/{branch}"
    have = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "-q", ref],
                          capture_output=True).returncode == 0
    if not have:
        subprocess.run(["git", "-C", str(root), "fetch", "-q", "--depth=1", "origin",
                        f"+refs/heads/{branch}:{ref}"], check=True)
    return ref


def base_list(root, rev):
    """The base's allow-list, or None when the base has none yet."""
    r = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{ALLOW}"], capture_output=True)
    return read_list(r.stdout.decode()) if r.returncode == 0 else None


HEADER = """\
# Lean files that use the legacy proof logic (scripts/legacy-logic.py). The list only shrinks:
# migrate a file to the full-state logic (FTriple/FTotalTriple/CTriple, fsym) and delete its line.
# Do not add lines; a new file uses the full-state logic.
"""


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--base")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args(argv)
    root = args.root
    users = {}
    for path in tracked_lean(root):
        why = uses_legacy((root / path).read_text(encoding="utf-8"))
        if why:
            users[path] = why
    allow_path = root / ALLOW
    if args.write:
        allow_path.write_text(HEADER + "".join(f"{p}\n" for p in sorted(users)))
    allowed = read_list(allow_path.read_text()) if allow_path.exists() else set()
    errors = []
    for path in sorted(set(users) - allowed):
        errors.append(f"{path}: uses the legacy logic ({users[path]}) and is not in {ALLOW}; "
                      "use the full-state logic (FTriple/FTotalTriple/CTriple, fsym)")
    for path in sorted(allowed - set(users)):
        errors.append(f"{ALLOW}: {path} no longer uses the legacy logic; delete its line")
    rev = base_revision(root, args.base)
    if rev:
        before = base_list(root, rev)
        if before is not None:
            for path in sorted(allowed - before):
                errors.append(f"{ALLOW}: {path} is not in {rev}'s list; the list only shrinks")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print(f"legacy-logic: {len(allowed)} legacy users, no new ones")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
