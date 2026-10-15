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

import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "assurance" / "lean-files.json"
BUILTIN = {"Init", "Std", "Lean", "Lake"}
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+?)\s*$")


def lean_files(args: list[str]) -> list[pathlib.Path]:
    out = []
    for a in args:
        p = pathlib.Path(a)
        out.extend(sorted(f for f in p.rglob("*.lean") if f.is_file()) if p.is_dir() else [p])
    return out


def imports(path: pathlib.Path) -> set[str]:
    mods = set()
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if m := IMPORT.match(line):
            mods.update(m.group(1).split())
    return mods


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
    reject = json.loads(REGISTRY.read_text(encoding="utf-8"))["reject"]
    files, errors = classify()
    errors += [f"{f}: listed under reject in {REGISTRY.relative_to(ROOT)} but not a standalone file"
               for f in sorted(set(reject) - set(files))]
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
    print(f"lean-deps: {len(files)} standalone Lean files, {len(todo)} elaborated, "
          f"{len(files) - len(todo)} unchanged since their last pass")
    for e in errors:
        print("lean-deps: " + e, file=sys.stderr)
    return 1 if errors else 0


def main(argv: list[str]) -> int:
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
    sys.exit(main(sys.argv[1:]))
