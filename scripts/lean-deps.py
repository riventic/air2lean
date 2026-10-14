#!/usr/bin/env python3
"""The repository's Lean modules that Lean files import, built before the files are checked.

    python3 -B scripts/lean-deps.py [--build] FILE_OR_DIR...
    python3 -B scripts/lean-deps.py --all

Prints the imports of the given `.lean` files (a directory: every `.lean` file below it) that are
modules of this package's libraries (`lakefile.toml`; `import ZigLean.Sep.Full.Auto` with
`ZigLean/Sep/Full/Auto.lean` present), one per line, sorted. Imports of other modules (Lean's own,
a fixture's own modules, generated files under a check's work directory) are left out. `--build`
runs `lake build` on them instead (nothing if there are none). `--all` prints every target of the
full build (`all_targets`; scripts/full-build.sh builds them).

A check that runs `lake env lean` on test files builds their imports first with `--build`: the
modules are derived from the files, so the list cannot drift, and a stale `.olean` (a merge that
changed a library module without a rebuild) is never tested silently.
"""

import pathlib
import re
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
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


def main(argv: list[str]) -> int:
    if argv == ["--all"]:
        print("\n".join(all_targets()))
        return 0
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
