#!/usr/bin/env python3
"""Ratchet: one proof framework (docs/proof-framework.md, CLAUDE.md "One proof framework").

Proofs use the full-state logic (`FTriple`, `FTotalTriple`, `CTriple`) and the symbolic executor
`fsym`; the library grows by lemmas and `@[fsym]` rules only. `assurance/proof-framework.json`
lists what exists today, so that nothing parallel is added:

* `judgments`: every definition of a program judgment in a tracked Lean file: a `def`, `abbrev`,
  `structure`, `class`, `inductive` or `opaque` whose name ends in one of `SUFFIXES` (`Triple`,
  `Returns`, `Within`, `Template`, `Spec`, …), with its module and status;
* `tactics`: every tactic declaration (`syntax`/`macro`/`elab` … `: tactic` or
  `declare_simp_like_tactic`, kind `syntax`) and every extension of a tactic declared elsewhere
  (`macro_rules`/`elab_rules` alternatives for `` `(tactic| kw …) ``, kind `rules`), by keyword,
  module and status; likewise every command (`… : command`, kind `command`;
  `` `(command| kw …) `` or `elab_rules : command`, kind `command-rules`), since a command
  elaborator can add, hide or rewrite declarations;
* `registries`: every declaration of an attribute or a simp set (`scan_registries`): a command
  `register_simp_attr`, `register_label_attr`, … (`REGISTRY_COMMAND`) or a call of a registration
  function, `registerBuiltinAttribute`, `registerTagAttribute`, … (`REGISTRY_CALL`), by registry
  name, kind (`attribute`, `simp-set`, `rule-set`) and module. Applying one (`@[fsym]`,
  `attribute [fsym] …`, `simp [fsym_norm]`, `simproc [fsym_norm] …`) is not a declaration. A
  registry is a second way to add automation, so a new one is reviewed like a new tactic;
* `legacy_users`: every Lean file that uses the legacy separation logic (imports a module of
  `LEGACY_MODULES` or names a legacy triple, `LEGACY_NAMES`), by path.

Status is `target` (the framework) or `legacy-to-retire` (to be migrated and deleted). The check
fails on an entry that the tree has and the file lacks (a new judgment, tactic, registry or legacy
user), on an entry that the file has and the tree lacks (delete it), and, with a base revision
(`--base`; in CI the pull request's base branch or `main`), on an entry that the base's file lacks
unless it records the coordinator's approval (`"approved": "<who, date, where>"`): the file only
shrinks except by an explicit, reviewed decision.

A judgment is recognised by name (`SUFFIXES`) and by structure (`structural_judgment`: a Prop-valued
declaration over a program and an assertion, a contract structure with program and assertion
fields, a step relation over two memories), so a new judgment with any name is reported. A registry
is recognised by the syntax form that declares it, never by the name it declares.

Usage: scripts/proof-framework.py [--root DIR] [--base REV] [--write [--approve WHO]]
  --write   rewrite the file from the tree (keeps statuses and approvals; a new entry gets a
            default status and no approval, which the base comparison then refuses, unless
            `--approve WHO` records the coordinator's approval on the new entries)
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
            "Halts", "Template", "Spec", "WP")

# The structural gate: a name does not make a judgment, a type does. A new top-level declaration is a
# judgment candidate when
#  (program)  it is Prop-valued and takes a program (a `Result`, `MemM`, `ConcM`, `CoN`, `StateT`
#             computation or a `Proto`) together with an assertion or a postcondition
#             (`Assn`, `FAssn`, `Res`, a `… → Prop` argument);
#  (contract) it is a structure or class with such a program field and such an assertion field
#             (`MutexImpl`: `lock : … → ConcM …` with `lock_wp : … P.WP …`), or with a field of
#             separation-logic assertions (`ResetLedger`: `B : W → FAssn`);
#  (step)     it is a Prop-valued structure relating two memories (`FStepIn hF m m'`), the step
#             relation of a program logic.
PROGRAM_TYPE = re.compile(r"\b(?:Result|MemM|ConcM|CoN|StateT|ExceptT|Proto)\b")
ASSERTION_TYPE = re.compile(r"\b(?:F?Assn|Res)\b|→\s*Prop\b")
SEP_ASSERTION = re.compile(r"\bF?Assn\b")
MEM_BINDER = re.compile(r"((?:[\w']+\s+)+):\s*Mem\b")
DECL_START = re.compile(
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(def|abbrev|structure|class|inductive|opaque)\s+([A-Za-z_][\w.]*)")
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|structure|class|inductive|opaque)\s+([A-Za-z_][\w.]*)", re.M)
TACTIC_DECL = re.compile(r"(?:@\[[^\]]*\]\s*)*(?:(?:scoped|local)\s+)?(?:syntax|macro|elab)\b")
TACTIC_RULES = re.compile(r"(?:@\[[^\]]*\]\s*)*(?:(?:scoped|local)\s+)?(?:macro_rules|elab_rules)\b")
TACTIC_RULE = re.compile(r"^\s*(?:macro_rules|elab_rules[^|]*)?\s*\|\s*`\((?:(tactic|command)\|)?\s*([^\s$)\]]+)", re.M)
# The syntax category of a declaration (before its `=>`) or of a rules block (`elab_rules : command`).
# A command elaborator can add, hide or rewrite declarations (`if_decl … end_if` drops theorems when
# its condition fails), so new commands are gated like new tactics.
CATEGORY = re.compile(r":\s*(tactic|command)\b")
DECL_KIND = {"tactic": "syntax", "command": "command"}
RULES_KIND = {"tactic": "rules", "command": "command-rules"}
STRING = re.compile(r'"([^"\\]*(?:\\.[^"\\]*)*)"')
# `declare_simp_like_tactic [(all := true)] name "kw " cfg` declares the tactic `kw` (a macro of
# Lean core that expands to `syntax … : tactic`).
SIMP_LIKE_TACTIC = re.compile(r"declare_simp_like_tactic\b")

# The registry gate: an attribute or a simp set is declared by a command (`register_simp_attr foo`)
# or by a call of a registration function, in an `initialize`/`builtin_initialize` or a helper they
# call (`registerBuiltinAttribute { name := `foo … }`, `registerTagAttribute `foo "…"`). Applying one
# (`@[foo]`, `attribute [foo] …`, `simp [foo]`, `simproc [foo] …`) is not a declaration. An
# environment extension alone adds no automation: it is filled through an attribute, a command or
# a tactic, and each of them is gated. A wrapper `def` around a registration call is recorded
# at its call, with the wrapper's parameter as the registry name.
REGISTRY_COMMANDS = {  # command keyword -> kind of the registries it declares
    "register_simp_attr": "simp-set", "register_sym_simp_attr": "simp-set",
    "register_sym_simp": "simp-set", "register_sym_dsimp": "simp-set",
    "register_label_attr": "attribute", "register_grind_attr": "attribute",
    "declare_aesop_rule_sets": "rule-set"}
REGISTRY_COMMAND = re.compile(
    r"(?<![\w'.])(" + "|".join(sorted(REGISTRY_COMMANDS, key=len, reverse=True)) + r")\b\s*"
    r"(\[[^\]]*\]|[^\s()\[\]{}]+)")
# `Lean.registerBuiltinAttribute`, `registerTagAttribute`, `registerParametricAttribute`,
# `registerEnumAttributes`, `registerAttributeImplBuilder`, `registerSimpAttr`, `registerSimprocAttr`,
# `registerLabelAttr`, … and `KeyedDeclsAttribute.init`.
REGISTRY_CALL = re.compile(r"(?<![\w'])(?:[\w']+\.)*(register\w*Attr\w*|KeyedDeclsAttribute\.init)(?![\w'])")
DEFINITION_BEFORE = re.compile(r"\b(?:def|abbrev|opaque|theorem|instance)\s+$")

# The legacy separation logic, deleted in Plan A's last phase. The base vocabulary that stays
# (`Sep/Heap`, `Sep/Assert`, `Sep/AllocSpec/{Region,Norm,Ops}`) is not listed. `Sep/Triple` also
# holds the vocabulary (`pts`, `arr`): until that is split out, its importers count as users.
LEGACY_MODULES = re.compile(
    r"^ZigLean\.Sep(\.(Triple|Total|Bounded|Loop|LoopTemplate|DispatchTemplate|Step|Automation"
    r"|Array|Array\.\w+|Block|Try|TryAlias|Discard|Sentinel|SentinelRealloc|Remap|RawAlloc|Alloc"
    r"|Owned|OsMalloc|ArenaClient|AddrReuse|Cost|Witness|Mmap|AllocSpec"
    r"|AllocSpec\.(Wrap|Wrappers|Dispatch|Toy)|Full\.Pinned))?$"
    r"|^ZigLean\.Conc\.(Own|Csl|TlsLemmas|Witness|Lock|LockBase|LockRules)$")
LEGACY_NAMES = re.compile(r"\b(Triple|TotalTriple|TotalTripleIn|TTriple|TTripleIn|TotalTripleWithin)\b")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
IMPORT_LINE = re.compile(r"^[ \t]*(?:public\s+|meta\s+)*import\b[^\n]*", re.M)
# The framework's own judgments and automation (tactics and registries).
TARGET_JUDGMENTS = {"FTriple", "FTotalTriple", "FReturns", "CTriple", "FAllocSpec"}
TARGET_AUTOMATION = re.compile(r"^fsym")


def strip_comments_and_strings(text, keep_strings=False):
    """`text` without `--` line comments and nestable `/- … -/` blocks (newlines kept; a block
    becomes a space, as Lean lexes it, so `kw/- c -/name` is not one word), and without string
    literals unless `keep_strings`."""
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
            out.append(" ")
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


def signature(chunk):
    """The declaration's head: `chunk` up to the first `:=`, `where` or `deriving` outside brackets."""
    depth, i = 0, 0
    while i < len(chunk):
        c = chunk[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth <= 0 and (chunk.startswith(":=", i) or re.match(r"(?:where|deriving)\b", chunk[i:])
                             and not chunk[i - 1].isalnum()):
            break
        i += 1
    return chunk[:i]


def prop_valued(head):
    """Whether the head's result type (after its last outermost `:`) is `Prop` or `… → Prop`."""
    depth, colon = 0, -1
    for i, c in enumerate(head):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and not head.startswith(":=", i):
            colon = i
    return colon >= 0 and re.search(r"\bProp\s*$", head[colon + 1:]) is not None


def structural_judgment(kind, chunk):
    """Whether the declaration `chunk` of the given kind is a judgment candidate (see PROGRAM_TYPE)."""
    head = signature(chunk)
    prop = prop_valued(head)
    if prop and PROGRAM_TYPE.search(head) and ASSERTION_TYPE.search(head):
        return True
    if kind not in ("structure", "class"):
        return False
    if SEP_ASSERTION.search(chunk) or PROGRAM_TYPE.search(chunk) and ASSERTION_TYPE.search(chunk):
        return True
    return prop and sum(len(m.split()) for m in MEM_BINDER.findall(head)) >= 2


def module_of(path):
    return path[:-len(".lean")].replace("/", ".")


def call_names(rest):
    """The registries declared by a registration call whose text after the function is `rest`: the
    `name := `x` of a structure argument, the leading `` `x `` of a name argument, the
    `` (`x, …) `` entries of a list argument. An argument that names none (a variable) is itself
    the registry, so that the entry shows what to review."""
    rest = re.sub(r"^\s*(?:<\||\$)?\s*", "", rest)
    arg = rest.split("\n", 1)[0]
    if rest[:1] in ("(", "[", "{"):  # the whole bracketed argument, over lines
        depth = 0
        for end, c in enumerate(rest):
            depth += (c in "([{") - (c in ")]}")
            if depth == 0:
                break
        arg = rest[:end + 1]
    if arg.startswith("["):
        names = re.findall(r"\(\s*`+([^\s,()]+)", arg)
    else:
        m = re.match(r"`+([^\s,()]+)", arg) or re.search(r"\bname\s*:=\s*`*([^\s,(){}]+)", arg)
        names = [m[1]] if m else []
    return names or [" ".join(arg.split())[:80] or "?"]


def scan_registries(text):
    """The attribute and simp-set declarations of one file, as (kind, registry): kind `simp-set`,
    `attribute` or `rule-set` (see REGISTRY_COMMANDS and REGISTRY_CALL)."""
    found = set()
    # Stripping comments and strings only removes text: a file without a match has no declaration.
    if not (REGISTRY_COMMAND.search(text) or REGISTRY_CALL.search(text)):
        return found
    code = strip_comments_and_strings(text)
    for m in REGISTRY_COMMAND.finditer(code):
        found.update((REGISTRY_COMMANDS[m[1]], name) for name in re.findall(r"[^\s,\[\]]+", m[2]))
    for m in REGISTRY_CALL.finditer(code):
        if not DEFINITION_BEFORE.search(code[:m.start()]):
            kind = "simp-set" if re.search(r"Simp(?!le)", m[1]) else "attribute"
            found.update((kind, name) for name in call_names(code[m.end():]))
    return found


def scan_file(path, text):
    """(judgments, tactics, legacy reason) of one file."""
    code = strip_comments_and_strings(text, keep_strings=True)
    judgments, tactics = set(), set()
    for name in DECL.findall(code):
        if name.split(".")[-1].endswith(SUFFIXES) and name.split(".")[-1][:1].isupper():
            judgments.add(name)
    for chunk in chunks(code, DECL_START):
        m = DECL_START.match(chunk)
        if m[2].split(".")[-1][:1].isupper() and structural_judgment(m[1], chunk):
            judgments.add(m[2])
    for chunk in chunks(code, TACTIC_DECL):
        s = STRING.search(chunk)
        cat = CATEGORY.findall(chunk.split("=>", 1)[0])
        if s and cat:
            tactics.add((DECL_KIND[cat[-1]], s.group(1).strip()))
    for chunk in chunks(code, SIMP_LIKE_TACTIC):
        if s := STRING.search(chunk):
            tactics.add(("syntax", s.group(1).strip()))
    for chunk in chunks(code, TACTIC_RULES):
        block = CATEGORY.findall(chunk.split("|", 1)[0])
        for cat, kw in TACTIC_RULE.findall(chunk):
            if cat or block:
                tactics.add((RULES_KIND[cat or block[-1]], kw))
    # Rules for a tactic or command declared in the same file are its implementation, not an
    # extension.
    tactics -= {(RULES_KIND[cat], kw) for cat, kind in DECL_KIND.items() for k, kw in tactics if k == kind}
    legacy = None
    for module in IMPORT.findall(text):
        if LEGACY_MODULES.match(module):
            legacy = f"imports {module}"
            break
    if legacy is None:
        # Names are declarations and uses; an `import …Full.Triple` line names a module.
        m = LEGACY_NAMES.search(IMPORT_LINE.sub("", strip_comments_and_strings(text)))
        legacy = f"names {m.group(1)}" if m else None
    return judgments, tactics, legacy


def tracked_lean(root):
    out = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
                         check=True, capture_output=True).stdout.decode()
    return sorted(p for p in out.split("\0") if p)


def scan(root):
    """The tree's entries, keyed for comparison."""
    judgments, tactics, registries, users = {}, {}, {}, {}
    for path in tracked_lean(root):
        text = (root / path).read_text(encoding="utf-8")
        js, ts, legacy = scan_file(path, text)
        mod = module_of(path)
        for name in js:
            judgments[(name, mod)] = {"name": name, "module": mod}
        for kind, kw in ts:
            tactics[(kw, kind, mod)] = {"tactic": kw, "kind": kind, "module": mod}
        for kind, name in scan_registries(text):
            registries[(name, kind, mod)] = {"registry": name, "kind": kind, "module": mod}
        if legacy:
            users[path] = legacy
    return judgments, tactics, registries, users


def entry_keys(data):
    """Every entry of the file by its key, with the entry."""
    out = {}
    for e in data.get("judgments", []):
        out[("judgment", e["name"], e["module"])] = e
    for e in data.get("tactics", []):
        out[("tactic", e["tactic"], e["kind"], e["module"])] = e
    for e in data.get("registries", []):
        out[("registry", e["registry"], e["kind"], e["module"])] = e
    for e in data.get("legacy_users", []):
        out[("legacy user", e["path"])] = e
    return out


def keys(data):
    """The file's judgment, tactic, registry and legacy user keys (without their category)."""
    k = entry_keys(data)
    return ({x[1:] for x in k if x[0] == "judgment"}, {x[1:] for x in k if x[0] == "tactic"},
            {x[1:] for x in k if x[0] == "registry"}, {x[1] for x in k if x[0] == "legacy user"})


def syntax_kind(kind):
    """`tactic syntax`, `tactic rules`, `command` or `command rules` for a `tactics` entry kind."""
    return kind.replace("-", " ") if kind.startswith("command") else f"tactic {kind}"


def default_status(entry):
    if "name" in entry:
        if entry["name"].split(".")[-1] in TARGET_JUDGMENTS:
            return "target"
        # Structural candidates: the legacy layer's and the hand-written sync specs' are to retire.
        legacy = LEGACY_MODULES.match(entry["module"]) or entry["module"].startswith("ZigLean.Conc.Spec.")
        return "legacy-to-retire" if legacy or entry["name"].endswith(SUFFIXES) else "target"
    # A tactic or registry that is not `fsym`'s is a candidate for a parallel automation; the
    # review of its approval sets `target` when it belongs to the framework.
    return "target" if TARGET_AUTOMATION.match(entry.get("tactic") or entry["registry"]) else "legacy-to-retire"


def render(judgments, tactics, registries, users, old, approved=None):
    known = entry_keys(old)

    def keep(key, e):
        prev = known.get(key, {})
        out = dict(e)
        if "path" not in e:
            out["status"] = prev.get("status", default_status(e))
        if "approved" in prev:
            out["approved"] = prev["approved"]
        elif approved and key not in known:
            out["approved"] = approved
        return out

    js = [keep(("judgment", *k), e) for k, e in sorted(judgments.items())]
    ts = [keep(("tactic", *k), e) for k, e in sorted(tactics.items())]
    rs = [keep(("registry", *k), e) for k, e in sorted(registries.items())]
    us = [keep(("legacy user", p), {"path": p}) for p in sorted(users)]
    return {
        "description": "One proof framework (docs/proof-framework.md): the program judgments, "
                       "tactics, attribute and simp-set registries and legacy-logic users that "
                       "exist. Only shrinks; additions need the coordinator "
                       "(scripts/proof-framework.py).",
        "judgments": js,
        "tactics": ts,
        "registries": rs,
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
    ap.add_argument("--approve", metavar="WHO", help="with --write: record WHO as the approval of every new entry")
    args = ap.parse_args(argv)
    root, path = args.root, args.root / FILE
    old = json.loads(path.read_text()) if path.exists() else {}
    judgments, tactics, registries, users = scan(root)
    if args.write:
        path.write_text(json.dumps(render(judgments, tactics, registries, users, old, args.approve),
                                   indent=2) + "\n")
        old = json.loads(path.read_text())
    errors = []
    for e in old.get("judgments", []) + old.get("tactics", []) + old.get("registries", []):
        if e.get("status") not in STATUSES:
            errors.append(f"{FILE}: {e} has no status among {STATUSES}")
    fj, ft, fr, fu = keys(old)
    hint = "use the full-state logic and fsym (docs/proof-framework.md); a new one is a coordinator decision"
    for name, mod in sorted(set(judgments) - fj):
        errors.append(f"{mod}: new program judgment `{name}`; {hint}")
    for kw, kind, mod in sorted(set(tactics) - ft):
        errors.append(f"{mod}: new {syntax_kind(kind)} `{kw}`; {hint}")
    for name, kind, mod in sorted(set(registries) - fr):
        errors.append(f"{mod}: new {kind} declaration `{name}`; extend fsym's registries instead "
                      "(docs/proof-framework.md); a new one is a coordinator decision")
    for p in sorted(set(users) - fu):
        errors.append(f"{p}: uses the legacy logic ({users[p]}); {hint}")
    for name, mod in sorted(fj - set(judgments)):
        errors.append(f"{FILE}: judgment `{name}` ({mod}) is gone; delete its entry")
    for kw, kind, mod in sorted(ft - set(tactics)):
        errors.append(f"{FILE}: {syntax_kind(kind)} `{kw}` ({mod}) is gone; delete its entry")
    for name, kind, mod in sorted(fr - set(registries)):
        errors.append(f"{FILE}: {kind} declaration `{name}` ({mod}) is gone; delete its entry")
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
        print(f"proof-framework: {len(fj)} judgments, {len(ft)} tactic entries, {len(fr)} registries, "
              f"{len(fu)} legacy users; nothing new")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
