#!/usr/bin/env python3
"""The repository's Lean modules that Lean files import, built before the files are checked.

    python3 -B scripts/lean-deps.py [--build] FILE_OR_DIR...
    python3 -B scripts/lean-deps.py --all
    python3 -B scripts/lean-deps.py --files
    python3 -B scripts/lean-deps.py --elaborate [--jobs N] [--mem-mib M]

Prints the imports of the given `.lean` files (a directory: every `.lean` file below it) that are
modules of this package's libraries (`lakefile.toml`; `import ZigLean.Sep.Full.Auto` with
`ZigLean/Sep/Full/Auto.lean` present), one per line, sorted. Imports of other modules (Lean's own,
a fixture's own modules, generated files under a check's work directory) are left out. `--build`
runs `lake build` on them instead (nothing if there are none). `--all` prints every target of the
full build (`all_targets`; scripts/full-build.sh builds them).

`--files` prints the standalone Lean files (`standalone_files`): every tracked `.lean` file outside
the libraries' directories whose imports are Lean's own or modules of this package. `lake env lean
FILE` elaborates each of them with no extra setup (the strength logs, the proof-client fixtures,
the tutorials), so the build alone does not cover them. `--elaborate` does (scripts/full-build.sh
runs it): it elaborates every one, in parallel, and fails when a file that should check does not,
when a file listed under `reject` in `assurance/lean-files.json` (a negative control: a false
theorem Lean must refuse) checks after all, or when a tracked file imports a library module that
does not exist (a renamed or split module). A result is remembered under the key of the file, its
library imports' sources (transitively), the toolchain and the lakefile (`$AIR2LEAN_CAS_DIR/
lean-files/`, else `.lake/lean-files/`), so only files whose inputs changed are elaborated again.
A file with imports of a fixture's own modules is elaborated by the check of that fixture.

A check that runs `lake env lean` on test files builds their imports first with `--build`: the
modules are derived from the files, so the list cannot drift, and a stale `.olean` (a merge that
changed a library module without a rebuild) is never tested silently.
"""

import argparse
import fnmatch
import functools
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "assurance" / "lean-files.json"
BUILTIN = {"Init", "Std", "Lean", "Lake"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9'!?]*(?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*")
CHAR_LITERAL = re.compile(r"'(?:\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^\\'])'")
RAW_STRING = re.compile(r'r(#+)?"')


@functools.cache
def generated_normalizer():
    spec = importlib.util.spec_from_file_location("air2lean_normalize_generated",
                                                pathlib.Path(__file__).resolve().with_name("normalize-generated.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def control_path(value):
    """Registry identities are literal repository-relative paths, never aliases or traversals."""
    if (not isinstance(value, str) or not value or value.startswith("/") or
            any(p in {"", ".", ".."} for p in value.split("/")) or "\\" in value):
        raise ValueError(f"invalid control registry path: {value!r}")
    return value


def control_registry(root=None):
    """One policy for unconditional rejections and fixture-owned contextual controls."""
    root = ROOT if root is None else pathlib.Path(root)
    registry = root / "assurance/lean-files.json"
    raw = registry.read_bytes()
    record = generated_normalizer().parse_json(raw.decode("utf-8"))
    if (not isinstance(record, dict) or type(record.get("schema_version")) is not int or record["schema_version"] != 2 or
            set(record) != {"schema_version", "description", "owners", "reject", "contextual"} or
            not isinstance(record["reject"], dict) or not isinstance(record["contextual"], dict) or
            not isinstance(record["owners"], dict)):
        raise ValueError(f"{registry}: unsupported Lean control registry")
    for owner, descriptor in record["owners"].items():
        if (not isinstance(owner, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", owner) or
                not isinstance(descriptor, dict) or set(descriptor) != {"script", "part", "step", "env"} or
                not all(isinstance(descriptor[k], str) and descriptor[k] for k in ("part", "step")) or
                not isinstance(descriptor["env"], dict) or any(
                    not isinstance(k, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", k) or
                    not isinstance(v, str) or "\0" in v for k, v in descriptor["env"].items())):
            raise ValueError(f"{owner}: invalid contextual owner descriptor")
        control_path(descriptor["script"])
        if not (root / descriptor["script"]).is_file():
            raise ValueError(f"{owner}: missing contextual owner script: {descriptor['script']}")
    controls = {}
    for file, reason in record["reject"].items():
        control_path(file)
        if not isinstance(reason, str) or not reason:
            raise ValueError(f"{file}: rejection requires a reason")
        controls[file] = {"reason": reason}
    fields = generated_normalizer().RAW_FIELDS | {"schema"}
    for file, control in record["contextual"].items():
        control_path(file)
        if (file in controls or not isinstance(control, dict) or
                set(control) != {"reason", "owner", "generated", "outcomes"} or
                not isinstance(control["reason"], str) or not control["reason"]):
            raise ValueError(f"{file}: invalid contextual control")
        if not isinstance(control["owner"], str) or control["owner"] not in record["owners"]:
            raise ValueError(f"{file}: missing contextual owner: {control['owner']}")
        control_path(control["generated"])
        if not (root / control["generated"]).is_file():
            raise ValueError(f"{file}: missing contextual generated: {control['generated']}")
        if not isinstance(control["outcomes"], list) or not control["outcomes"]:
            raise ValueError(f"{file}: contextual control requires expected outcomes")
        for rule in control["outcomes"]:
            if (not isinstance(rule, dict) or set(rule) != {"profile", "expect"} or
                    not isinstance(rule["expect"], str) or rule["expect"] not in {"check", "reject"} or
                    not isinstance(rule["profile"], dict) or not rule["profile"] or
                    not set(rule["profile"]) <= fields or
                    any(not isinstance(v, (str, int, bool)) for v in rule["profile"].values())):
                raise ValueError(f"{file}: invalid contextual outcome rule")
        controls[file] = control
    for file in controls:
        if not (root / file).is_file():
            raise ValueError(f"{file}: registered control is missing")
    unused = set(record["owners"]) - {c["owner"] for c in controls.values() if "owner" in c}
    if unused:
        raise ValueError(f"contextual owners have no controls: {sorted(unused)}")
    return dict(owners=record["owners"], controls=controls, sha256=hashlib.sha256(raw).hexdigest())


def control_outcome(control, *, report=None, selected_root=None):
    """Resolve only a fixture's checked selected artifact; standalone callers explicitly defer."""
    if "owner" not in control:
        return "reject", None
    if report is None:
        return "defer", None
    if selected_root is None:
        raise ValueError("contextual control requires the selected source tree")
    selected = pathlib.Path(selected_root) / control["generated"]
    binding = generated_normalizer().checked_selection(report, selected)
    profile = binding["metadata"]["profile"]
    matches = [r["expect"] for r in control["outcomes"] if all(
        fnmatch.fnmatchcase(profile[k], value) if isinstance(profile[k], str) and isinstance(value, str)
        else type(profile[k]) is type(value) and profile[k] == value
        for k, value in r["profile"].items())]
    if len(matches) != 1:
        raise ValueError("contextual control has no unique outcome for the selected export profile")
    return matches[0], binding


def expected_error(source):
    """The existing marker anchors its diagnostic to the immediately following source line.

    This is explicit control metadata, not an approximation of Lean command spans.
    """
    markers = list(re.finditer(r"^-- expect-error: (.+)$", source, re.M))
    if not markers:
        raise ValueError('missing "-- expect-error: <text>" anchor')
    if len(markers) != 1:
        raise ValueError('duplicate "-- expect-error:" anchors')
    marker = markers[0]
    line = source.count("\n", 0, marker.start()) + 2
    lines = source.splitlines()
    if line > len(lines) or not lines[line - 1].strip():
        raise ValueError("expect-error must immediately precede its diagnostic source line")
    return marker[1].strip(), line


def rejection_error(file, source, status, text):
    """A negative control must fail at its explicit diagnostic source anchor."""
    theorems = [i for i, text in enumerate(source.splitlines(), 1) if text.startswith("theorem ")]
    if not theorems:
        return f"{file}: no theorem to reject"
    try:
        expected, line = expected_error(source)
    except ValueError as error:
        return f"{file}: {error}"
    if line < theorems[-1]:
        return f"{file}: expected diagnostic precedes its final theorem"
    lines = [int(n) for n in re.findall(
        rf"{re.escape(pathlib.Path(file).name)}:(\d+):\d+: error: {re.escape(expected)}", text)]
    if status == 0:
        return f"{file}: Lean accepted the rejection control"
    if line not in lines:
        return f"{file}: rejection did not report its expected diagnostic at source line {line}"
    return None


def control_completion(record, owner, *, root=None):
    """Revalidate the existing fixture cache's contextual result before discharging its owner.

    Like other fixture-cache entries this is a trusted-runner index, not a proof receipt. The
    positive check's actual compiled audit and kernel replay remain required and retained.
    """
    root = ROOT if root is None else pathlib.Path(root)
    registry = control_registry(root)
    controls = {f: c for f, c in registry["controls"].items() if c.get("owner") == owner}
    if (not controls or not isinstance(record, dict) or record.get("owner") != owner or
            record.get("root") != str(root.resolve()) or record.get("status") != "pass" or
            record.get("registry_sha256") != registry["sha256"] or
            not isinstance(record.get("controls"), dict) or set(record["controls"]) != set(controls)):
        raise ValueError(f"owner {owner}: missing or stale contextual completion")
    for file, control in controls.items():
        result = record["controls"][file]
        if (not isinstance(result, dict) or result.get("status") != "pass" or
                result.get("source_sha256") != hashlib.sha256((root / file).read_bytes()).hexdigest()):
            raise ValueError(f"{file}: missing or changed contextual control result")
        outcome, binding = control_outcome(control, report=result.get("report"), selected_root=root)
        if (outcome not in {"check", "reject"} or binding is None or
                outcome != result.get("expect") or binding != result.get("selection")):
            raise ValueError(f"{file}: contextual completion belongs to another selected artifact")
        if outcome == "check":
            import theorem_universe
            module = theorem_universe.staged_module(file)
            audit = pathlib.Path(result["audit"])
            raw = audit.read_bytes()
            checked = generated_normalizer().parse_json(raw.decode("utf-8"))
            if (hashlib.sha256(raw).hexdigest() != result.get("audit_sha256") or
                    checked.get("status") != "pass" or not checked.get("theorem_count") or
                    module not in checked.get("modules", []) or
                    not any(t.get("module") == module for t in checked.get("theorems", [])) or
                    (checked.get("kernel_replay") or {}).get("status") != "pass"):
                raise ValueError(f"{file}: positive control has no matching compiled kernel audit")
    return record


def check_owned_controls(owner, reports, output):
    """The owning fixture calls this only after producing context and building selected imports."""
    import theorem_universe
    registry = control_registry()
    controls = {f: c for f, c in registry["controls"].items() if c.get("owner") == owner}
    if not controls:
        raise ValueError(f"unknown or unused contextual owner: {owner}")
    missing = {c["generated"] for c in controls.values()} - set(reports)
    if missing:
        raise ValueError(f"owner {owner}: missing selected producer reports: {sorted(missing)}")
    output = pathlib.Path(output).resolve()
    work = output.with_suffix(".d")
    work.mkdir(parents=True, exist_ok=True)
    results, errors = {}, []
    # Resolve every context before compiling anything; a missing second input is never implicit.
    contexts = {f: control_outcome(c, report=reports[c["generated"]], selected_root=ROOT)
                for f, c in controls.items()}
    modules = repo_modules(ROOT / f for f in controls)
    if modules:
        subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
    for file, (outcome, binding) in contexts.items():
        source = (ROOT / file).read_bytes()
        result = dict(expect=outcome, source_sha256=hashlib.sha256(source).hexdigest(),
                      report=str(pathlib.Path(reports[controls[file]["generated"]]).resolve()), selection=binding)
        if outcome == "reject":
            child = subprocess.run(["lake", "env", "lean", file], cwd=ROOT,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            error = rejection_error(file, source.decode("utf-8"), child.returncode, child.stdout)
        else:
            module = theorem_universe.staged_module(file)
            unit = theorem_universe.Unit(file, None, module, (), (), None)
            failures = theorem_universe.compile_all([unit], {file: unit}, work)
            error = "; ".join(failures) if failures else None
            lib = theorem_universe.lib_of(work, None)
            if error is None:
                artifacts = work / "reports" / module.replace(".", "/")
                artifacts.parent.mkdir(parents=True, exist_ok=True)
                sources = artifacts.with_suffix(".sources.json")
                sources.write_text(json.dumps({module: file}) + "\n")
                audit = artifacts.with_suffix(".audit.json")
                checked = theorem_universe.audit_modules([module], [lib], audit, sources=sources)
                error = None if (checked["status"] == "pass" and not checked["exit_code"] and
                                 checked["theorem_count"] and checked["kernel_replay"] == "pass") else \
                    f"{file}: positive control failed its compiled kernel audit"
                result.update(audit=str(audit), audit_sha256=hashlib.sha256(audit.read_bytes()).hexdigest())
        # Recheck both source and selected context after actual compilation/audit.
        if source != (ROOT / file).read_bytes() or contexts[file] != control_outcome(
                controls[file], report=result["report"], selected_root=ROOT):
            error = f"{file}: control or selected producer context changed while checking"
        result["status"] = "fail" if error else "pass"
        results[file] = result
        if error:
            errors.append(error)
    record = dict(owner=owner, root=str(ROOT.resolve()), registry_sha256=registry["sha256"],
                  controls=results, status="fail" if errors else "pass", errors=errors)
    if not errors:
        control_completion(record, owner)
    output.write_text(json.dumps(record, sort_keys=True, indent=2) + "\n")
    return errors


def block_comment_end(text: str, start: int) -> int:
    """End of a nested block comment, shared by header discovery and source masking."""
    depth, i = 1, start + 2
    while i < len(text) and depth:
        if text.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif text.startswith('-/', i):
            depth, i = depth - 1, i + 2
        else:
            i += 1
    if depth:
        raise ValueError('Lean source: unterminated block comment')
    return i


def header_tokens(text: str):
    """Lazy header words. A consumer that stops at a body command never lexes its body."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith('/-', i):
            i = block_comment_end(text, i)
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = n if end < 0 else end
        else:
            start = i
            while i < n and not text[i].isspace() and not text.startswith(('/-', '--'), i):
                i += 1
            yield text[start:i]


def strip_comments(text: str) -> str:
    """Limited offline mask, preserving positions and newlines; not a complete Lean parser.

    Used only for source indexing/defense in depth. Interpolation is syntax-dependent; this
    mask cannot qualify a claim or determine compiled-audit eligibility. Quoted identifiers
    remain tokens, not comments. Import discovery uses only the independently read header.
    """
    out = list(text)
    i, n = 0, len(text)

    def mask(start, end, literal=False):
        for k in range(start, end):
            if text[k] != '\n':
                out[k] = ' '
        if literal:
            out[start], out[end - 1] = '"', '"'

    while i < n:
        start = i
        if text.startswith('/-', i):
            i = block_comment_end(text, i)
            mask(start, i)
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = n if end < 0 else end
            mask(start, i)
        elif text[i] == '«':
            end = text.find('»', i + 1)
            if end < 0:
                raise ValueError('Lean source: unterminated quoted identifier')
            i = end + 1
        elif text[i] == 'r' and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")) \
                and (raw := RAW_STRING.match(text, i)):
            terminator = '"' + (raw.group(1) or '')
            end = text.find(terminator, raw.end())
            if end < 0:
                raise ValueError('Lean source: unterminated raw string')
            i = end + len(terminator)
            mask(start, i, literal=True)
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            if i >= n:
                raise ValueError('Lean source: unterminated string')
            i += 1
            mask(start, i, literal=True)
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!?")):
            char = CHAR_LITERAL.match(text, i)
            if char:
                i = char.end()
                mask(start, i, literal=True)
            else:
                i += 1  # Syntax quotations and identifier apostrophes are not character literals.
        else:
            i += 1
    return ''.join(out)


def import_names(text: str) -> list[str]:
    """Lean 4.34 module header: [module] [prelude] ([public] [meta] import [all] NAME)*.

    Validate the complete header only. The first body command ends discovery; the actual
    compiler, never this header reader or the offline mask, decides body validity.
    Directives are separated by whitespace, not necessarily newlines. The existing module
    path APIs represent ordinary ASCII dotted names; quoted/escaped/path spellings fail
    explicitly rather than being silently split or omitted. One directive imports one name.
    """
    words = iter(enumerate(header_tokens(text)))
    i, word = next(words, (0, None))
    names = []
    if word == 'module':
        i, word = next(words, (i + 1, None))
    if word == 'prelude':
        i, word = next(words, (i + 1, None))
    while word is not None:
        start = i
        if word == 'public':
            i, word = next(words, (i + 1, None))
        if word == 'meta':
            i, word = next(words, (i + 1, None))
        if word != 'import':
            break  # The first body command ends the header, e.g. public section or meta def.
        i, word = next(words, (i + 1, None))
        if word == 'all':
            i, word = next(words, (i + 1, None))
        if word is None or MODULE_NAME.fullmatch(word) is None \
                or word in {'module', 'prelude', 'public', 'meta', 'import', 'all'}:
            spelling = word if word is not None else '<missing>'
            raise ValueError(f'Lean import: unsupported module spelling {spelling!r} after token {start}; '
                             'expected one ordinary ASCII dotted module name')
        names.append(word)
        i, word = next(words, (i + 1, None))
    return names


def lean_files(args: list[str]) -> list[pathlib.Path]:
    out = []
    for a in args:
        p = pathlib.Path(a)
        out.extend(sorted(f for f in p.rglob("*.lean") if f.is_file()) if p.is_dir() else [p])
    return out


def imports(path: pathlib.Path) -> set[str]:
    try:
        return set(import_names(path.read_text(encoding='utf-8')))
    except ValueError as error:
        raise ValueError(f'{path}: {error}') from error


def lib_roots() -> set[str]:
    """The first components of the package's library modules (`lakefile.toml`: names, roots)."""
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    roots = set()
    for lib in lake.get("lean_lib", []):
        for r in lib.get("roots", [lib.get("root", lib["name"])]):
            roots.add(r.split(".")[0])
    return roots


def all_targets() -> list[str]:
    """Every target of the full build: the package's libraries and executables (`lakefile.toml`)
    and every tracked module under a library's directory (ZigLean/, Air2Lean/, Proofs/), whether
    or not a library root imports it; a library with explicit `roots` by those roots."""
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    out = [lib["name"] for lib in lake.get("lean_lib", [])]
    out += [exe["name"] for exe in lake.get("lean_exe", [])]
    dirs = [lib["name"] for lib in lake.get("lean_lib", []) if "roots" not in lib]
    tracked = subprocess.run(["git", "ls-files", "-z", "--", *(f"{d}/*.lean" for d in dirs)],
                             cwd=ROOT, check=True, capture_output=True, text=True).stdout
    out += sorted(f[:-5].replace("/", ".") for f in tracked.split("\0") if f)
    return out


def repo_modules(files: list[pathlib.Path]) -> list[str]:
    mods = set().union(*(imports(f) for f in files))
    roots = lib_roots()
    return sorted(m for m in mods if m.split(".")[0] in roots
                  and (ROOT / (m.replace(".", "/") + ".lean")).is_file())


def module_file(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def library_files() -> list[str]:
    """The tracked files of the libraries' directories (`all_targets` names their modules)."""
    return [t.replace(".", "/") + ".lean" for t in all_targets() if "." in t]


def classify() -> tuple[list[str], list[str]]:
    """(standalone files, errors): the tracked `.lean` files outside the libraries, split by their
    imports (see the module docstring). An import of a library root that names no file is an error
    for every file, standalone or not."""
    roots = lib_roots()
    owned = set(library_files())
    tracked = subprocess.run(["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT, check=True,
                             capture_output=True, text=True).stdout.split("\0")
    files, errors = [], []
    for f in sorted(t for t in tracked if t and t not in owned and (ROOT / t).is_file()):
        mods = imports(ROOT / f)
        missing = sorted(m for m in mods if m.split(".")[0] in roots and not module_file(m).is_file())
        errors += [f"{f}: imports {m}, which is no module of this package" for m in missing]
        if mods and not missing and all(m.split(".")[0] in BUILTIN | roots for m in mods):
            files.append(f)
    return files, errors


def standalone_files() -> list[str]:
    files, errors = classify()
    if errors:
        raise SystemExit("\n".join(errors))
    return files


def input_key(f: str, toolchain: bytes, memo: dict[str, bytes]) -> str:
    """Hash of everything that decides whether `lake env lean f` checks: the file, the sources of
    the library modules it imports (transitively), the lakefile and the toolchain."""
    roots = lib_roots()
    h = hashlib.sha256(toolchain)
    h.update((ROOT / f).read_bytes())
    seen, todo = set(), sorted(imports(ROOT / f))
    while todo:
        m = todo.pop()
        if m in seen or m.split(".")[0] not in roots:
            continue
        seen.add(m)
        if m not in memo:
            memo[m] = module_file(m).read_bytes() if module_file(m).is_file() else b""
        todo += sorted(imports(module_file(m))) if module_file(m).is_file() else []
    for m in sorted(seen):
        h.update(m.encode() + b"\0" + hashlib.sha256(memo[m]).digest())
    return h.hexdigest()


def elaborate(jobs: int | None, mem_mib: int) -> int:
    sys.path.insert(0, str(ROOT / "scripts"))
    import par
    registry = control_registry()
    controls = registry["controls"]
    reject = {f for f, c in controls.items() if "owner" not in c}
    deferred = {f for f, c in controls.items() if "owner" in c}
    files, errors = classify()
    errors += [f"{f}: registered in {REGISTRY.relative_to(ROOT)} but not a standalone file"
               for f in sorted(set(controls) - set(files))]
    files = [f for f in files if f not in deferred]
    store = pathlib.Path(os.environ["AIR2LEAN_CAS_DIR"]).expanduser() / "lean-files" \
        if os.environ.get("AIR2LEAN_CAS_DIR") else ROOT / ".lake" / "lean-files"
    toolchain = (ROOT / "lean-toolchain").read_bytes() + (ROOT / "lakefile.toml").read_bytes()
    memo: dict[str, bytes] = {}
    todo, keys = [], {}
    for f in files:
        keys[f] = input_key(f, toolchain, memo) + ("-reject" if f in reject else "")
        if not (store / keys[f]).exists():
            todo.append(f)
    if todo:
        logs = pathlib.Path(tempfile.mkdtemp(prefix="air2lean-lean-files."))
        names = {f: f"{i}-{par.safe_name(f)[-100:]}" for i, f in enumerate(todo)}
        with open(os.devnull, "wb") as null:
            statuses = par.run([par.Job(names[f], ["lake", "env", "lean", f], cwd=str(ROOT)) for f in todo],
                               par.workers(jobs, mem_mib, len(todo)), out=null, err=null, log_dir=logs)
        store.mkdir(parents=True, exist_ok=True)
        for f, status in zip(todo, statuses):
            if (status != 0) == (f in reject):
                (store / keys[f]).touch()
                continue
            log = logs / (names[f] + ".log")
            tail = log.read_text(errors="replace").strip().splitlines()[:12] if log.is_file() else []
            errors.append(f"{f}: " + ("checks, but is listed under reject" if f in reject
                                      else "does not check") + "".join("\n    " + l for l in tail))
        shutil.rmtree(logs, ignore_errors=True)
    print(f"lean-deps: {len(files)} standalone Lean files, {len(todo)} elaborated, "
          f"{len(files) - len(todo)} unchanged since their last pass")
    for file in sorted(deferred):
        print(f"lean-deps: DEFER {file}: owner {controls[file]['owner']} must check its selected producer context")
    if deferred:
        print("lean-deps: NOT QUALIFIED: contextual control owners remain outstanding")
    for e in errors:
        print("lean-deps: " + e, file=sys.stderr)
    return 1 if errors else 0


def main(argv: list[str]) -> int:
    if argv[:1] == ["--check-rejection"]:
        parser = argparse.ArgumentParser(description="Check a compiler rejection at its declared source line")
        parser.add_argument("file", type=pathlib.Path)
        parser.add_argument("--status", type=int, required=True)
        parser.add_argument("--log", type=pathlib.Path, required=True)
        args = parser.parse_args(argv[1:])
        error = rejection_error(args.file, args.file.read_text(), args.status, args.log.read_text())
        if error:
            print("lean-deps: " + error, file=sys.stderr)
        return 1 if error else 0
    if argv[:1] == ["--controls"]:
        parser = argparse.ArgumentParser(description="Check one fixture-owned contextual control family")
        parser.add_argument("owner")
        parser.add_argument("--report", action="append", default=[], metavar="SOURCE=REPORT")
        parser.add_argument("--output", type=pathlib.Path, required=True)
        args = parser.parse_args(argv[1:])
        reports = {}
        for value in args.report:
            source, separator, report = value.partition("=")
            if not separator or not report or control_path(source) in reports:
                raise ValueError(f"invalid or duplicate selected-source report: {value!r}")
            reports[source] = pathlib.Path(report)
        errors = check_owned_controls(args.owner, reports, args.output)
        for error in errors:
            print("lean-deps: " + error, file=sys.stderr)
        return 1 if errors else 0
    if argv == ["--all"]:
        print("\n".join(all_targets()))
        return 0
    if argv == ["--files"]:
        print("\n".join(standalone_files()))
        return 0
    if argv[:1] == ["--elaborate"]:
        opts = dict(zip(argv[1::2], argv[2::2]))
        if set(opts) - {"--jobs", "--mem-mib"} or len(argv) % 2 == 0:
            print("usage: lean-deps.py --elaborate [--jobs N] [--mem-mib M]", file=sys.stderr)
            return 2
        return elaborate(int(opts["--jobs"]) if "--jobs" in opts else None,
                         int(opts.get("--mem-mib", 3000)))
    build = bool(argv) and argv[0] == "--build"
    args = argv[1:] if build else argv
    if not args:
        print(__doc__.strip().splitlines()[2].strip(), file=sys.stderr)
        return 2
    mods = repo_modules(lean_files(args))
    if not build:
        print("\n".join(mods))
        return 0
    if not mods:
        return 0
    return subprocess.call(["lake", "build", *mods], cwd=ROOT)


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except (OSError, ValueError) as error:
        print(f'lean-deps: {error}', file=sys.stderr)
        sys.exit(2)
