#!/usr/bin/env python3
"""The proof-fixture Lake package (tests/roadmap/lakefile.toml, docs/build-cache.md#proof-fixtures).

    python3 -B scripts/fixtures.py build [TARGET...]
    python3 -B scripts/fixtures.py audit MODULE... [--theorem NAME]... [--output FILE]
    python3 -B scripts/fixtures.py mutant NAME --src DIR --fails MODULE [--expect TEXT]...
    python3 -B scripts/fixtures.py files

Every Lean file of a converted fixture is elaborated by Lake, in one mode:

- `build`: `lake build TARGET...` (fixture libraries or modules, or modules of the root package;
  no target: every library) in the fixtures package, through the shared artifact cache
  (`scripts/cas.py run`). Lake's trace decides what is elaborated again; nothing else is reused.
  Lake builds only one of two modules with the same name, silently (both libraries "pass"), so
  the build first checks that every module-name root (the first component, and each library's
  `roots`) belongs to one library and is no root of the root package's libraries.
- `audit`: the axioms of the built modules, read from the compiled environment by
  `scripts/assumptions.py` (kernel replay included), not from a message log. Fails unless every
  theorem of the modules depends on the standard axioms only (propext, Classical.choice,
  Quot.sound), no audited declaration depends on `sorry`, and each `--theorem` is among them.
- `mutant`: a negative check. DIR holds a fixture's sources with one mutation (module paths as in
  the fixture). They are built as a workspace of their own (`tests/roadmap/.lake/mutants/NAME`)
  with the fixture package's name, so an unchanged copy has the same Lake trace as the fixture's
  module (an artifact-cache hit), while the mutated module and its dependents have their own.
  `lake build MODULE` must fail on MODULE itself: Lake's list of failed targets is exactly
  MODULE (so its imports built) and an error is reported in MODULE's source; each `--expect`
  text must occur in the output. A failed import, a missing module or a killed process is not a
  rejection of the mutant.
- `files`: the repository paths of the package's modules (scripts/lean-deps.py: they are not
  standalone files).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
PACKAGE = ROOT / "tests" / "roadmap"
NAME = "fixtures"


def libraries(package: Path) -> list[dict]:
    return tomllib.loads((package / "lakefile.toml").read_text(encoding="utf-8")).get("lean_lib", [])


def lake_modules(package: Path, libs: list[dict]) -> dict[str, list[str]]:
    """Each library's modules, as Lake enumerates them (`lake query LIB:modules`)."""
    if not libs:
        return {}
    done = subprocess.run(["lake", "query", "--json", *(f"{lib['name']}:modules" for lib in libs)],
                          cwd=package, text=True, capture_output=True)
    lines = done.stdout.splitlines()
    if done.returncode or len(lines) != len(libs):
        raise SystemExit(f"fixtures: lake query failed in {package}:\n{done.stdout}{done.stderr}")
    return {lib["name"]: json.loads(line) for lib, line in zip(libs, lines)}


def check_names(package: Path, root: Path | None = None) -> dict[str, list[str]]:
    """Fail unless every module-name root belongs to one library of `package` and is no root of
    the root package's (`root`, default ROOT) libraries; returns each library's modules."""
    reserved = {"Init", "Std", "Lean", "Lake"} | {r.split(".")[0] for lib in libraries(root or ROOT)
                                                  for r in lib.get("roots", [lib.get("root", lib["name"])])}
    libs = libraries(package)
    modules = lake_modules(package, libs)
    owner, problems = {}, []
    for lib in libs:
        name = lib["name"]
        for first in sorted({r.split(".")[0] for r in lib.get("roots", [name])}
                            | {m.split(".")[0] for m in modules[name]}):
            if first in reserved:
                problems.append(f"{name}: module root {first} is a root of the root package")
            elif owner.setdefault(first, name) != name:
                problems.append(f"module root {first} is in libraries {owner[first]} and {name}")
    if problems:
        raise SystemExit("fixtures: Lake would build only one of two same-named modules:\n  "
                         + "\n  ".join(problems))
    return modules


def lake(package: Path, args: list[str], capture: bool = False) -> subprocess.CompletedProcess:
    """`lake ARGS` in `package` through the shared artifact cache (scripts/cas.py run)."""
    command = [sys.executable, "-B", str(Path(__file__).with_name("cas.py")), "run", "--", "lake", *args]
    if not capture:
        return subprocess.run(command, cwd=package)
    return subprocess.run(command, cwd=package, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def build(targets: list[str]) -> int:
    check_names(PACKAGE)
    return lake(PACKAGE, ["build", *(targets or [lib["name"] for lib in libraries(PACKAGE)])]).returncode


def files(root: Path | None = None) -> list[str]:
    """The `root`-relative (default ROOT) paths of the fixture package's modules (none without
    the package)."""
    root = root or ROOT
    package = root / PACKAGE.relative_to(ROOT)
    if not (package / "lakefile.toml").is_file():
        return []
    out, modules = [], check_names(package, root)
    for lib in libraries(package):
        src = package / lib.get("srcDir", ".")
        for module in modules[lib["name"]]:
            out.append((src / (module.replace(".", "/") + ".lean")).relative_to(root).as_posix())
    return sorted(out)


def audit(modules: list[str], theorems: list[str], output: Path | None, lib: Path | None = None) -> int:
    """`lib`: the directory of the built modules (default: the fixture package's)."""
    if str(Path(__file__).resolve().parent) not in sys.path:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
    from assumptions import STANDARD_AXIOMS  # Lazy: scripts/lean-deps.py loads this file for `files`.
    work = Path(tempfile.mkdtemp(prefix="air2lean-fixtures-audit."))
    try:
        report_path = output or work / "assurance.json"
        lib = lib or PACKAGE / ".lake" / "build" / "lib" / "lean"
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(filter(None, [str(lib), os.environ.get("LEAN_PATH")])))
        command = [sys.executable, "-B", str(ROOT / "scripts" / "assumptions.py"), "--no-build",
                   "--replay-cache", str(work / "replay-cache.json"), "--output", str(report_path)]
        for module in modules:
            command += ["--module", module]
        report_path.unlink(missing_ok=True)
        done = subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        report = json.loads(report_path.read_text()) if report_path.is_file() else {"status": "error"}
        problems = []
        if report.get("status") == "error":
            problems.append(f"assumptions.py exited {done.returncode}: {report.get('error')}")
        else:
            if (report.get("kernel_replay") or {}).get("status") != "pass":
                problems.append("kernel replay did not pass: "
                                + json.dumps((report.get("kernel_replay") or {}).get("rejected"))[:2000])
            # The audited oleans are the built ones: `lake env` puts the root build directory
            # first on LEAN_PATH, where a stray same-named olean would shadow a fixture module.
            oleans = {row["module"]: (ROOT / row["olean"]).resolve() for row in report["freshness"]["artifacts"]}
            problems += [f"{m}: audited {oleans.get(m)}, not the built {lib.resolve() / m.replace('.', '/')}.olean"
                         for m in modules if oleans.get(m) != lib.resolve() / (m.replace(".", "/") + ".olean")]
            audited = [t for t in report["theorems"] if t["module"] in modules]
            names = {t["name"] for t in audited}
            problems += [f"{t['name']}: axioms {sorted(set(t['axioms']) - STANDARD_AXIOMS)}"
                         for t in audited if not set(t["axioms"]) <= STANDARD_AXIOMS]
            problems += [f"{v['name']} ({v['module']}): {v['reason']}" for v in report["violations"]
                         if v["trust_class"] == "sorry"]
            problems += [f"{name}: no such theorem in {', '.join(modules)}" for name in theorems if name not in names]
        if problems:
            sys.stdout.write(done.stdout[-4000:])
            print("fixtures audit: FAILED\n  " + "\n  ".join(problems), file=sys.stderr)
            return 1
        print(f"fixtures audit: {len(audited)} theorems of {', '.join(modules)}: standard axioms only "
              f"(kernel replay of {len(report['kernel_replay']['modules'])} modules passed)")
        return 0
    finally:
        shutil.rmtree(work, ignore_errors=True)


MANIFEST = """# Generated by scripts/fixtures.py mutant: a fixture's sources with one mutation, built apart.
# The package name is the fixture package's, so an unchanged copy has the fixture module's trace.
name = "{name}"

[[require]]
name = "air2lean"
path = {root}

[[lean_lib]]
name = "Mutant"
srcDir = "src"
globs = {globs}
"""


def mutant(name: str, src: Path, fails: list[str], expect: list[str]) -> int:
    if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
        raise SystemExit(f"fixtures mutant: invalid name {name!r}")
    workspace = PACKAGE / ".lake" / "mutants" / name
    shutil.rmtree(workspace / "src", ignore_errors=True)
    shutil.copytree(src, workspace / "src")
    modules = sorted(".".join(p.relative_to(workspace / "src").with_suffix("").parts)
                     for p in (workspace / "src").rglob("*.lean"))
    (workspace / "lakefile.toml").write_text(MANIFEST.format(
        name=NAME, root=json.dumps(str(ROOT)), globs=json.dumps(modules)))
    check_names(workspace)
    problems = []
    for module in fails:
        if module not in modules:
            raise SystemExit(f"fixtures mutant: {module} is not among {modules}")
        done = lake(workspace, ["build", module], capture=True)
        out = done.stdout
        source = "src/" + module.replace(".", "/") + ".lean"
        failed = re.search(r"^Some required targets logged failures:\n((?:- .*\n?)*)", out, re.M)
        failed = {line[2:].strip() for line in failed.group(1).splitlines()} if failed else set()
        if done.returncode == 0:
            problems.append(f"{module} still builds")
        elif failed != {module}:
            problems.append(f"{module}: failed targets {sorted(failed)}, not {module} alone (an import or the build failed)")
        elif not re.search(r"^error: " + re.escape(source) + r":\d+:\d+:", out, re.M):
            problems.append(f"{module}: no error reported in {source}")
        problems += [f"{module}: no {text!r} in the build output" for text in expect if text not in out]
        if problems:
            sys.stdout.write(out[-6000:])
            break
        print(f"fixtures mutant {name}: {module} rejected")
    if problems:
        print(f"fixtures mutant {name}: FAILED\n  " + "\n  ".join(problems), file=sys.stderr)
        return 1
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("build")
    p.add_argument("targets", nargs="*")
    p = sub.add_parser("audit")
    p.add_argument("modules", nargs="+")
    p.add_argument("--theorem", action="append", default=[])
    p.add_argument("--output", type=Path)
    p = sub.add_parser("mutant")
    p.add_argument("name")
    p.add_argument("--src", type=Path, required=True)
    p.add_argument("--fails", action="append", required=True)
    p.add_argument("--expect", action="append", default=[])
    sub.add_parser("files")
    a = parser.parse_args(argv)
    if a.command == "build":
        return build(a.targets)
    if a.command == "audit":
        return audit(a.modules, a.theorem, a.output)
    if a.command == "mutant":
        return mutant(a.name, a.src, a.fails, a.expect)
    print("\n".join(files()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
