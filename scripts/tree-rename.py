#!/usr/bin/env python3
"""Mechanical tree renames: a rename map as data, a dry run, an apply, and a check.

    scripts/tree-rename.py [--dry-run] [--groups G1,G2|all] [--tree REV] [-v]   (default: dry run)
    scripts/tree-rename.py --check [--groups ...] [--old REV]
    scripts/tree-rename.py --apply --groups G1                                  (one group per PR)

The map (`assurance/tree-rename.json`) lists groups. A group is one PR: a list
of rules that move files, and every reference to a moved file follows. A later group names the
paths as the earlier groups leave them, so a dry run of several groups is the tree after all of
them (the groups are applied in order, in memory).

Rules (the most specific rule wins; two rules of one specificity that disagree are an error):
  {"kind": "file",   "from": "a/b.lean", "to": "c/b.lean"}
  {"kind": "files",  "from_dir": "docs", "to_dir": "docs/logic", "names": ["x.md", "y.md"]}
  {"kind": "family", "dir": "ZigLean/Sep", "name": "Lock"}      Lock<Upper>… moves to Lock/<Upper>…
                     (optional "into": "RwLock", "as": "Prod": RwProd<Upper>… moves to RwLock/Prod<Upper>…)
  {"kind": "dir",    "from": "tests/roadmap", "to": "tests/fixtures"}   every tracked file below it
A rule that matches nothing is an error (the map is stale), unless it has `"optional": true`.

What a move rewrites, in every tracked text file (never the map, this script and its tests,
`never_rewrite` in the map):
  * a path (`ZigLean/Sep/Full/Auto.lean`, `docs/ci.md`, a directory prefix `tests/roadmap`) and,
    for a file of a Lean root (`lean_roots`), its module (`ZigLean.Sep.Full.Auto`, a module
    prefix): imports, lakefiles, `assurance/*.json`, scripts, workflows, docs, fixtures;
  * a relative link of a Markdown file (it is resolved against the old directory of the file and
    written against the new one, for the target's move and the file's own);
  * a pathlib join in Python (`ROOT / 'tests' / 'roadmap'`) when the join keeps its length; a join
    that changes its length is reported, not rewritten (a manual hit).
A moved file that holds `../` and changes its directory depth is reported too.

`--check` (after an apply, with `--old REV` the tree before it, default origin/main) fails when a
reference to an old path or module remains, an old file remains, or a new file is missing.

Nothing moves unless `--apply` is given; `--apply` refuses a dirty tree and several groups
(`--allow-multi` composes them into one PR). After an apply run the post steps it prints.
"""
import argparse
import difflib
import fnmatch
import json
import os
from pathlib import Path
import posixpath
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MAP = "assurance/tree-rename.json"
SPECIFICITY = {"file": 3, "files": 3, "family": 2, "dir": 1}


class RenameError(Exception):
    pass


# ---------------------------------------------------------------- trees

def git(root, *args, input=None):
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          input=input).stdout


class Tree:
    """The tracked files of the working tree, or of a revision (`rev`)."""

    def __init__(self, root, rev=None):
        self.root, self.rev = Path(root), rev
        if rev is None:
            out = git(root, "ls-files", "-s", "-z").decode("utf-8", "surrogateescape")
            entries = [e.split("\t", 1) for e in out.split("\0") if e]
        else:
            out = git(root, "ls-tree", "-r", "-z", rev).decode("utf-8", "surrogateescape")
            entries = [(e.split("\t", 1)[0].split(" "), e.split("\t", 1)[1]) for e in out.split("\0") if e]
            entries = [(" ".join(m), p) for m, p in entries]
        self.symlinks = {p for m, p in entries if m.startswith("120000")}
        self.files = sorted(p for m, p in entries if not m.startswith("160000") and (rev is not None or (self.root / p).exists() or p in self.symlinks))

    def blobs(self):
        """Every blob of the revision in one `git cat-file --batch` (a `git show` per file is minutes)."""
        if not hasattr(self, "_blobs"):
            self._blobs = {}
            spec = "".join(f"{self.rev}:{p}\n" for p in self.files if p not in self.symlinks).encode("utf-8", "surrogateescape")
            out = git(self.root, "cat-file", "--batch", input=spec)
            pos = 0
            for p in (p for p in self.files if p not in self.symlinks):
                end = out.index(b"\n", pos)
                head = out[pos:end].split()
                size = int(head[2]) if len(head) == 3 and head[1] == b"blob" else 0
                self._blobs[p] = out[end + 1:end + 1 + size]
                pos = end + 1 + size + 1
        return self._blobs

    def read(self, path):
        """The text of a tracked file, or None for a binary, a symlink or a missing file."""
        if path in self.symlinks:
            return None
        try:
            data = (self.root / path).read_bytes() if self.rev is None else self.blobs()[path]
        except (OSError, KeyError):
            return None
        if b"\0" in data[:8192]:
            return None
        try:
            return data.decode("utf-8")
        except UnicodeDecodeError:
            return None


# ---------------------------------------------------------------- the map

def load_map(root, path=MAP):
    data = json.loads((Path(root) / path).read_text())
    groups = data["groups"]
    ids = [g["id"] for g in groups]
    if len(set(ids)) != len(ids):
        raise RenameError("duplicate group ids")
    return data


def strip(p):
    return p.rstrip("/")


def is_module_file(path, lean_roots):
    return path.endswith(".lean") and path.split("/")[0].removesuffix(".lean") in lean_roots


def module_of(path):
    return path.removesuffix(".lean").replace("/", ".")


def expand(files, group):
    """The moves of one group over the tracked `files`: {old: new}, and the rules' dir pairs."""
    files = list(files)
    fileset = set(files)
    candidates = {}  # old -> {(specificity, new): rule index}
    used = [0] * len(group["rules"])

    def offer(old, new, rule, i):
        used[i] += 1
        candidates.setdefault(old, {}).setdefault(SPECIFICITY[rule["kind"]], set()).add(new)

    for i, rule in enumerate(group["rules"]):
        kind = rule["kind"]
        if kind == "file":
            if rule["from"] in fileset:
                offer(rule["from"], rule["to"], rule, i)
        elif kind == "files":
            for name in rule["names"]:
                old = f'{strip(rule["from_dir"])}/{name}'
                if old in fileset:
                    offer(old, f'{strip(rule["to_dir"])}/{name}', rule, i)
                elif not rule.get("optional"):
                    raise RenameError(f'{group["id"]}: {old} is not tracked (stale map)')
        elif kind == "family":
            d, name = strip(rule["dir"]), rule["name"]
            into, prefix = rule.get("into", name), rule.get("as", "")
            rx = re.compile(re.escape(d) + "/" + re.escape(name) + r"([A-Z][^/]*)$")
            for f in files:
                m = rx.match(f)
                if m:
                    offer(f, f"{d}/{into}/{prefix}{m.group(1)}", rule, i)
        elif kind == "dir":
            src, dst = strip(rule["from"]), strip(rule["to"])
            suffix = rule.get("suffix", "")
            for f in files:
                if f.startswith(src + "/") and f.endswith(suffix):
                    offer(f, dst + f[len(src):], rule, i)
        else:
            raise RenameError(f'{group["id"]}: unknown rule kind {kind!r}')
    for i, rule in enumerate(group["rules"]):
        if not used[i] and not rule.get("optional"):
            raise RenameError(f'{group["id"]}: rule matches no tracked file (stale map): {json.dumps(rule)}')
    moves = {}
    for old, by_spec in candidates.items():
        top = by_spec[max(by_spec)]
        if len(top) > 1:
            raise RenameError(f'{group["id"]}: {old} has two targets of one specificity: {sorted(top)}')
        (new,) = top
        if new != old:
            moves[old] = new
    targets = {}
    for old, new in moves.items():
        if new in targets:
            raise RenameError(f'{group["id"]}: {old} and {targets[new]} both move to {new}')
        targets[new] = old
        if new in fileset and new not in moves:
            raise RenameError(f'{group["id"]}: {old} moves onto the tracked file {new}')
        parts = new.split("/")
        for k in range(1, len(parts)):
            prefix = "/".join(parts[:k])
            if prefix in fileset and prefix not in moves:
                raise RenameError(f'{group["id"]}: {new} would sit below the file {prefix}')
    return moves


def dir_pairs(group):
    return [(strip(r["from"]), strip(r["to"])) for r in group["rules"] if r["kind"] == "dir"]


def apply_moves(files, moves):
    return sorted({moves.get(f, f) for f in files})


# ---------------------------------------------------------------- the rewriter

INLINE_LINK = re.compile(r'(\]\(\s*<?)([^)\s>]+)')
REF_LINK = re.compile(r'^(\[[^\]]+\]:\s*<?)(\S+?)(?=>?\s|>?$)', re.M)


class Rewriter:
    def __init__(self, files, moves, dirs, lean_roots, drop_prefix):
        self.files, self.moves, self.dirs, self.lean_roots = set(files), moves, dirs, lean_roots
        self.dirset = {posixpath.dirname(f) for f in files} | {d for f in files for d in parents(f)}
        paths, stems, mods = {}, {}, {}
        for old, new in moves.items():
            if is_module_file(old, lean_roots) and is_module_file(new, lean_roots):
                stems[old.removesuffix(".lean")] = new.removesuffix(".lean")
                mods[module_of(old)] = module_of(new)
            else:
                paths[old] = new
        for old, new in dirs:
            paths[old] = new
            if old.split("/")[0] in lean_roots and new.split("/")[0] in lean_roots:
                mods[old.replace("/", ".")] = new.replace("/", ".")
        for table, sep, conv in ((paths, "/", str), (stems, "/", str), (mods, ".", lambda d: d.replace("/", "."))):
            for k in list(table):  # a file that its directory pair carries to the same target needs no entry
                for d, dn in dirs:
                    d, dn = conv(d), conv(dn)
                    if k.startswith(d + sep) and table[k] == dn + k[len(d):]:
                        del table[k]
                        break
        self.joins = self._joins({**paths, **{o + ".lean": n + ".lean" for o, n in stems.items()}})
        for table in (paths, stems):
            for old, new in list(table.items()):
                for pre in drop_prefix:
                    if old.startswith(pre) and new.startswith(pre) and "/" in old[len(pre):]:
                        table.setdefault(old[len(pre):], new[len(pre):])
        self.paths, self.stems, self.mods = paths, stems, mods
        self.sc_path = Scanner(paths, "/")
        self.sc_stem = Scanner(stems, "/", stem=True)
        self.sc_mod = Scanner(mods, ".")

    @staticmethod
    def _joins(paths):
        """pathlib joins: (regex, new components or None for a manual hit) per path pair of 2+ components."""
        out = []
        for old, new in paths.items():
            a, b = old.split("/"), new.split("/")
            if len(a) < 2:
                continue
            body = r"\s*/\s*".join(r"(['\"])" + re.escape(c) + r"\%d" % (i + 1) for i, c in enumerate(a))
            out.append((re.compile(r"(?<![\w.])" + body), b if len(a) == len(b) else None, a))
        return out

    def rewrite(self, text, old_path, new_path):
        """(new text, replacement count, manual hits)."""
        n, manual = 0, []
        if old_path.endswith(".md"):
            text, k = self.rewrite_links(text, old_path, new_path)
            n += k
            text, k = self.sub_outside_links(text)
            n += k
        else:
            text, k = self.sub(text)
            n += k
        if old_path.endswith(".py"):
            text, k, manual = self.rewrite_joins(text)
            n += k
        return text, n, manual

    def sub(self, text):
        n = 0
        for scanner in (self.sc_path, self.sc_stem, self.sc_mod):
            text, k = scanner.sub(text)
            n += k
        return text, n

    def sub_outside_links(self, text):
        """`sub` on the text of a Markdown file outside its relative link targets."""
        spans = sorted((m.start(2), m.end(2)) for rx in (INLINE_LINK, REF_LINK) for m in rx.finditer(text)
                       if is_relative_link(m.group(2)))
        out, pos, n = [], 0, 0
        for s, e in spans:
            if s < pos:
                continue
            chunk, k = self.sub(text[pos:s])
            out.append(chunk), out.append(text[s:e])
            n += k
            pos = e
        chunk, k = self.sub(text[pos:])
        out.append(chunk)
        return "".join(out), n + k

    def map_path(self, p):
        if p in self.moves:
            return self.moves[p]
        for old, new in sorted(self.dirs, key=lambda x: -len(x[0])):
            if p == old or p.startswith(old + "/"):
                return new + p[len(old):]
        return p

    def exists(self, p):
        return p in self.files or p in self.dirset

    def rewrite_links(self, text, old_path, new_path):
        old_dir, new_dir = posixpath.dirname(old_path), posixpath.dirname(new_path)
        count = [0]

        def fix(m):
            target = m.group(2)
            if not is_relative_link(target):
                return m.group(0)
            body, sep, frag = target.partition("#")
            body, qsep, query = body.partition("?")
            if not body:
                return m.group(0)
            resolved = posixpath.normpath(posixpath.join(old_dir, body))
            if resolved.startswith("..") or not self.exists(resolved):
                return m.group(0)
            mapped = self.map_path(resolved)
            if mapped == resolved and new_dir == old_dir:
                return m.group(0)
            rel = posixpath.relpath(mapped, new_dir or ".")
            if body.endswith("/") and not rel.endswith("/"):
                rel += "/"
            if body.startswith("./") and not rel.startswith("."):
                rel = "./" + rel
            new = rel + qsep + query + sep + frag
            if new == target:
                return m.group(0)
            count[0] += 1
            return m.group(1) + new
        text = INLINE_LINK.sub(fix, text)
        text = REF_LINK.sub(fix, text)
        return text, count[0]

    def rewrite_joins(self, text):
        n, manual = 0, []
        for rx, new, old in self.joins:
            if old[-1] not in text:
                continue
            if new is None:
                for m in rx.finditer(text):
                    manual.append("/".join(old))
                continue

            def fix(m, new=new):
                parts = []
                for i, c in enumerate(new):
                    q = m.group(i + 1)
                    parts.append(f"{q}{c}{q}")
                return " / ".join(parts)
            text, k = rx.subn(fix, text)
            n += k
        return text, n, manual


def is_relative_link(t):
    return bool(t) and not t.startswith(("#", "/", "mailto:")) and "://" not in t and ":" not in t.split("/")[0]


def parents(path):
    parts = path.split("/")
    return ["/".join(parts[:k]) for k in range(1, len(parts))]


class Scanner:
    """Replace the keys of `table` (paths or dotted modules) in a text, longest key first.

    A candidate starts at a first component of a key that no word, `.` or `-` precedes (for a path;
    for a module no word or `.`), runs over the path characters, and ends at a `/` or `.` boundary or
    at the end of the run, so `tests/roadmap` matches in `tests/roadmap/x` and `'tests/roadmap'` but
    not in `tests/roadmap-x`. A stem (a module file without `.lean`) must not be followed by `/`.
    """

    def __init__(self, table, sep, stem=False):
        self.table, self.sep, self.stem = table, sep, stem
        firsts = sorted({k.split(sep)[0] for k in table}, key=lambda c: (-len(c), c))
        before = r"(?<![\w.-])" if sep == "/" else r"(?<![\w.])"
        self.start = re.compile(before + "(?:" + "|".join(re.escape(c) for c in firsts) + r")(?![\w-])") if firsts else None
        self.run = re.compile(r"[\w./-]+" if sep == "/" else r"[\w.]+")

    def sub(self, text):
        if not self.start:
            return text, 0
        out, pos, n = [], 0, 0
        for m in self.start.finditer(text):
            if m.start() < pos:
                continue
            run = self.run.match(text, m.start()).group(0)
            cuts = [i for i, c in enumerate(run) if c in "/."] if self.sep == "/" else [i for i, c in enumerate(run) if c == "."]
            for i in sorted(cuts + [len(run)], reverse=True):
                key = run[:i]
                if key not in self.table:
                    continue
                if self.stem and i < len(run) and run[i] == "/":
                    continue
                out.append(text[pos:m.start()])
                out.append(self.table[key])
                pos, n = m.start() + i, n + 1
                break
        out.append(text[pos:])
        return "".join(out), n


# ---------------------------------------------------------------- the plan

def category(path):
    top = path.split("/")[0]
    if path.endswith(".lean") and top in ("ZigLean", "Air2Lean", "Proofs", "tools"):
        return "lean"
    if path.endswith(("lakefile.toml", "lake-manifest.json")):
        return "lakefile"
    if top == "assurance":
        return "assurance"
    if top == "scripts":
        return "scripts"
    if top == "tests":
        return "tests"
    if top == "docs" or path.endswith(".md"):
        return "docs"
    if top == ".github":
        return "workflows"
    return "other"


def build_plan(tree, data, group_ids, rev_files=None):
    """The plan of the selected groups over `tree`: per group moves and rewriters, per file the end result."""
    groups = [g for g in data["groups"] if group_ids is None or g["id"] in group_ids]
    if group_ids is not None:
        missing = set(group_ids) - {g["id"] for g in groups}
        if missing:
            raise RenameError(f"unknown groups: {sorted(missing)}")
    lean_roots = tuple(data.get("lean_roots", ("ZigLean", "Air2Lean", "Proofs", "tools")))
    drop = tuple(data.get("drop_prefix", ()))
    current, stages = list(tree.files), []
    for g in groups:
        moves = expand(current, g)
        dirs = dir_pairs(g)
        rw = Rewriter(current, moves, dirs, lean_roots, drop)
        stages.append((g, moves, dirs, rw))
        current = apply_moves(current, moves)
    return stages


def never(path, data):
    """A frozen file keeps its bytes: the map, this script and its tests, hash-bound inputs (`*.zig`),
    and records of a past state. An entry is a path, a directory (trailing `/`) or a glob."""
    return any(path == p or (p.endswith("/") and path.startswith(p)) or ("*" in p and fnmatch.fnmatchcase(path, p))
               for p in data.get("never_rewrite", ()))


def run_plan(tree, data, stages):
    """Walk every tracked text file through the stages. Returns the per-file results."""
    results = {}  # original path -> {"final", "text", "changed": {gid: n}, "manual": {gid: [..]}}
    for path in tree.files:
        cur, text = path, None
        loaded = False
        orig_text = None
        res = {"final": path, "changed": {}, "manual": {}, "depth": []}
        for g, moves, dirs, rw in stages:
            new = rw.map_path(cur)
            if not never(cur, data) and not never(path, data):
                if not loaded:
                    text, loaded = tree.read(path), True
                    orig_text = text
                if text is not None:
                    new_text, n, manual = rw.rewrite(text, cur, new)
                    if n:
                        res["changed"][g["id"]] = n
                    if manual:
                        res["manual"][g["id"]] = manual
                    text = new_text
                    if new != cur and posixpath.dirname(new).count("/") != posixpath.dirname(cur).count("/") \
                            and not cur.endswith((".md", ".lean")) and "../" in text:
                        res["depth"].append(new)
            if new != cur:
                res["moved"] = res.get("moved", set()) | {g["id"]}
            cur = new
        res["final"], res["text"] = cur, text
        res["orig_text"] = orig_text
        results[path] = res
    return results


# ---------------------------------------------------------------- reports

def report(tree, data, stages, results, verbose):
    def p(*a):
        print(*a)
    total_moves = total_touched = total_repl = 0
    for g, moves, dirs, rw in stages:
        p(f'== {g["id"]}: {g.get("title", "")}')
        ops = describe_moves(g, moves, stages_files_before(tree, stages, g["id"]))
        for line in ops if verbose or len(ops) <= 60 else ops[:60] + [f"  ... {len(ops) - 60} more (use -v)"]:
            p(" ", line)
        rewritten = {orig: r for orig, r in results.items() if g["id"] in r["changed"]}
        touched = {o for o, r in results.items() if g["id"] in r.get("moved", ())} | set(rewritten)
        cats = {}
        for orig, r in rewritten.items():
            c = category(r["final"])
            cats[c] = cats.get(c, [0, 0])
            cats[c][0] += 1
            cats[c][1] += r["changed"][g["id"]]
        repl = sum(v[1] for v in cats.values())
        p(f'  moves: {len(moves)}; files rewritten: {len(rewritten)} ({repl} replacements); '
          f'files the PR touches: {len(touched)}')
        for c in sorted(cats):
            p(f"    {c:<10} {cats[c][0]:>5} files {cats[c][1]:>6} replacements")
        total_moves += len(moves)
        total_touched += len(touched)
        total_repl += repl
        if verbose:
            for orig in sorted(rewritten):
                p(f'    rewrite {orig}' + (f' -> {results[orig]["final"]}' if results[orig]["final"] != orig else "")
                  + f' ({rewritten[orig]["changed"][g["id"]]})')
    p(f"== total: {total_moves} moves, {total_touched} file touches, {total_repl} replacements")
    manual = [(o, r["manual"]) for o, r in sorted(results.items()) if r["manual"]]
    depth = sorted(n for r in results.values() for n in r["depth"])
    if manual:
        p("== manual hits (a pathlib join whose length changes; rewrite by hand):")
        for o, m in manual:
            p(f'  {results[o]["final"]}: ' + ", ".join(sorted({x for v in m.values() for x in v})))
    if depth:
        p("== moved files with `../` whose directory depth changes (check relative paths):")
        for n in depth:
            p(" ", n)
    return total_moves, total_touched, total_repl, len(manual), len(depth)


def stages_files_before(tree, stages, gid):
    files = list(tree.files)
    for g, moves, dirs, rw in stages:
        if g["id"] == gid:
            return files
        files = apply_moves(files, moves)
    return files


def describe_moves(g, moves, files):
    """Whole-directory moves as one line, the rest one line per file."""
    lines, covered = [], set()
    for src, dst in dir_pairs(g):
        below = [f for f in files if f.startswith(src + "/")]
        if below and all(moves.get(f) == dst + f[len(src):] for f in below) and not any(
                f.startswith(dst + "/") for f in files):
            lines.append(f"git mv {src} {dst}   ({len(below)} files)")
            covered.update(below)
    for old in sorted(moves):
        if old not in covered:
            lines.append(f"git mv {old} {moves[old]}")
    return lines


POST_STEPS = """post steps:
  python3 scripts/lean-deps.py --precompiled write      # lakefile FsymDeps globs, sorted again
  python3 scripts/proof-framework.py --write            # paths in the allow-list, sorted again
  scripts/regen.sh                                      # generated files, goldens, hash-bound manifests
  scripts/full-build.sh                                 # then the light merge gate of CLAUDE.md"""


# ---------------------------------------------------------------- apply and check

def apply(root, tree, data, stages, results, allow_multi):
    if len(stages) != 1 and not allow_multi:
        raise RenameError("--apply takes one group (one PR); --allow-multi composes several")
    if git(root, "status", "--porcelain", "--untracked-files=no").strip():
        raise RenameError("the working tree has uncommitted changes to tracked files")
    for orig, r in results.items():
        if r["text"] is not None and r["text"] != r["orig_text"]:
            (root / orig).write_text(r["text"])
    if len(stages) == 1:
        g, moves, dirs, rw = stages[0]
        files = list(tree.files)
        ops = []
        for src, dst in dir_pairs(g):
            below = [f for f in files if f.startswith(src + "/")]
            if below and all(moves.get(f) == dst + f[len(src):] for f in below) and not any(
                    f.startswith(dst + "/") for f in files) and not (root / dst).exists():
                ops.append((src, dst))
                files = [f for f in files if f not in set(below)]
        ops += [(f, moves[f]) for f in sorted(moves) if f in set(files)]
    else:
        ops = [(o, r["final"]) for o, r in sorted(results.items()) if r["final"] != o]
    for src, dst in ops:
        (root / dst).parent.mkdir(parents=True, exist_ok=True)
        git(root, "mv", src, dst)
        d = (root / src).parent
        while d != root:
            try:
                d.rmdir()
            except OSError:
                break
            d = d.parent
    print(f"applied {len(ops)} git mv operations; {sum(1 for r in results.values() if r['text'] != r['orig_text'] and r['text'] is not None)} files rewritten")
    print(POST_STEPS)


def check(root, data, group_ids, old_rev):
    old = Tree(root, old_rev)
    stages = build_plan(old, data, group_ids)
    cur = Tree(root)
    cur_files = set(cur.files)
    problems = []
    final = list(old.files)
    for g, moves, dirs, rw in stages:
        final = apply_moves(final, moves)
    for g, moves, dirs, rw in stages:
        for o, n in moves.items():
            if o in cur_files and o not in final:
                problems.append(f"old file remains: {o}")
    for f in sorted(set(final) - cur_files):
        problems.append(f"new file missing: {f}")
    leftovers = {}
    for path in cur.files:
        if never(path, data):
            continue
        text = cur.read(path)
        if text is None:
            continue
        for g, moves, dirs, rw in stages:
            n = rw.sub(text)[1]
            if path.endswith(".py"):
                n += sum(len(rx.findall(text)) for rx, _, _ in rw.joins)
            if n:
                leftovers[path] = leftovers.get(path, 0) + n
        if path.endswith(".md"):  # a relative link that points at a path of the old tree and nowhere now
            old_files = set(old.files)
            for rx in (INLINE_LINK, REF_LINK):
                for m in rx.finditer(text):
                    t = m.group(2).partition("#")[0]
                    if is_relative_link(t) and t:
                        r = posixpath.normpath(posixpath.join(posixpath.dirname(path), t))
                        if r not in cur_files and r in old_files and not (root / r).exists():
                            problems.append(f"{path}: relative link {t} points at the old path {r}")
    for path, n in sorted(leftovers.items()):
        problems.append(f"{path}: {n} reference(s) to an old path or module")
    return problems


# ---------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=str(ROOT))
    ap.add_argument("--map", default=MAP)
    ap.add_argument("--groups", default="all", help="comma-separated group ids, or all")
    ap.add_argument("--tree", help="dry run over this revision instead of the working tree")
    ap.add_argument("--old", default="origin/main", help="--check: the revision before the apply")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="print what would change (the default)")
    mode.add_argument("--apply", action="store_true")
    mode.add_argument("--check", action="store_true")
    ap.add_argument("--allow-multi", action="store_true")
    ap.add_argument("--diff", nargs="+", metavar="PATH", help="dry run: the diff of these files (paths before the move)")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args(argv)
    root = Path(a.root)
    ids = None if a.groups == "all" else a.groups.split(",")
    try:
        data = load_map(root, a.map)
        if a.check:
            problems = check(root, data, ids, a.old)
            for p in problems[:200]:
                print(p)
            print(f"tree-rename check: {'FAILED, ' + str(len(problems)) + ' problem(s)' if problems else 'ok'}")
            return 1 if problems else 0
        if a.apply and a.tree:
            raise RenameError("--apply works on the working tree, not --tree")
        tree = Tree(root, a.tree)
        stages = build_plan(tree, data, ids)
        results = run_plan(tree, data, stages)
        if a.apply:
            apply(root, tree, data, stages, results, a.allow_multi)
            return 0
        for path in a.diff or ():
            r = results.get(path)
            if r is None or r["text"] is None:
                print(f"--diff {path}: not a tracked text file", file=sys.stderr)
                continue
            sys.stdout.writelines(difflib.unified_diff(r["orig_text"].splitlines(True), r["text"].splitlines(True),
                                                       f"a/{path}", f'b/{r["final"]}', n=0))
        if not a.diff:
            report(tree, data, stages, results, a.verbose)
        return 0
    except RenameError as e:
        print(f"tree-rename: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
