#!/usr/bin/env python3
"""One theorem universe for the premise index, the assumptions audit and the source scan (F2).

The universe is every module that docs/premise-index.md indexes (`premises.theorem_files`:
`theorem_roots` minus `excluded` in assurance/premises.json) together with the shipped
ZigLean/Proofs modules that receipts cover (`assumptions.shipped_modules`). Lean exits 0 on
`declaration uses 'sorry'`, so compiling a theorem file proves nothing by itself: every
indexed module is compiled to an olean and audited by scripts/assumptions.py (axiom policy,
`sorryAx`, kernel replay).

  theorem_universe.py list                     indexed files, module roots and auditing gates
  theorem_universe.py scan                     sources: no sorry/admit/native_decide, no kernel
                                               escape hatch outside assurance/kernel-escapes.json
  theorem_universe.py audit --output-dir DIR   compile every indexed module outside the Lake
       [--shipped REPORT] [--no-build]         targets, audit it, and check the shipped report
  theorem_universe.py gate FILE --root DIR --lean-path DIR --output-dir DIR
                                               the same for a file that imports a gate-time
                                               generated module (run by that gate's script)
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import assumptions  # noqa: E402
from assumptions import LAKE_ROOTS, ROOT, TOOLCHAIN_ROOTS, shipped_modules, write_report  # noqa: E402

RESERVED = {*LAKE_ROOTS, *TOOLCHAIN_ROOTS}
ESCAPES = Path("assurance/kernel-escapes.json")
# Files that import a module generated at gate time, and the gate script that compiles and
# audits them with `theorem_universe.py gate`.
GATES = {
    "tests/roadmap/bitops/GeneratedBitset.lean": "tests/roadmap/bitops/check.sh",
    "tests/roadmap/dispatch/CountdownProof.lean": "tests/roadmap/dispatch/check.sh",
    "tests/roadmap/global-payload-pointers/GeneratedProofs.lean":
        "tests/roadmap/global-payload-pointers/check-generated.sh",
    "tests/roadmap/indirect-calls/Bridge.lean": "tests/roadmap/indirect-calls/check.sh",
    "tests/roadmap/dispatch-templates/TokenizerProof.lean": "tests/roadmap/dispatch-templates/check.sh",
    "tests/roadmap/env-boundaries/StdIo.lean": "tests/roadmap/env-boundaries/check.sh",
    "tests/roadmap/packed-casts/Model.lean": "tests/roadmap/packed-casts/check.sh",
    "tests/roadmap/packed-casts/ModelLogical.lean": "tests/roadmap/packed-casts/check.sh",
    "tests/roadmap/packed-casts/ModelVector.lean": "tests/roadmap/packed-casts/check.sh",
    "tests/roadmap/packed-casts/ModelAuto.lean": "tests/roadmap/packed-casts/check.sh",
    "tests/roadmap/nan-bits/Model.lean": "tests/roadmap/nan-bits/check.sh",
    "tests/roadmap/enc-exactness/Model.lean": "tests/roadmap/enc-exactness/check.sh",
    "tests/roadmap/try-pointers/lifetimes/Lifetimes.lean":
        "tests/roadmap/try-pointers/lifetimes/check.sh",
}
PLACEHOLDER = re.compile(r"\b(sorry|admit|native_decide)\b")
# Never acceptable: the elaborator would write declarations the kernel did not check.
FORBIDDEN = re.compile(r"\bdebug\.skipKernelTC\b|\bset_option\s+debug\.")
# Acceptable only where reviewed: environment mutation, unsafe code, compiler replacement.
ESCAPE = re.compile(r"\b(addDecl|addAndCompile|addDeclCore|addDeclWithoutChecking|modifyEnv|setEnv"
                    r"|unsafe|implemented_by)\b|@\[(extern)\b")
SORRY_WARNING = "declaration uses 'sorry'"


def premises_module():
    import premises  # Lazy: premises imports assumptions, which this module imports first.
    return premises


@dataclass(frozen=True)
class Unit:
    file: str            # repository-relative source
    root: str | None     # `lean -R` source root; None: compiled as a staged copy named `module`
    module: str
    deps: tuple          # files of the local (non-Lake) modules it imports
    lake: tuple          # Lake-built modules it imports
    gate: str | None     # gate script for a file that needs a gate-time generated module
    names: tuple         # declaration names (source parse): units sharing one cannot share an environment


MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*")


def module_of(file: str, root: str) -> str:
    relative = Path(file).relative_to(root) if root != "." else Path(file)
    return ".".join(relative.with_suffix("").parts)


def is_lake(module: str, target: Path, root: Path) -> bool:
    return module.split(".")[0] in LAKE_ROOTS and target == root / (module.replace(".", "/") + ".lean")


def universe(root: Path = ROOT) -> tuple[list[str], list[Unit]]:
    """Shipped Lake modules and every indexed file outside them, with its module root."""
    premises = premises_module()
    config = premises.load_config(root / premises.CONFIG)
    repo = premises.load_repository(root, config)
    if repo.errors:
        raise ValueError("; ".join(repo.errors))
    shipped = shipped_modules(root)
    edges: dict[str, list] = {}   # file -> [(module, target file | None, kind)]
    named: dict[str, str] = {}    # imported file -> module name it is imported as
    pending = [f.rel for f in premises.theorem_files(repo) if module_of(f.rel, ".") not in shipped]
    indexed = list(pending)
    while pending:
        rel = pending.pop()
        if rel in edges:
            continue
        lean = repo.files[rel]
        edges[rel] = []
        for module in lean.imports:
            target = premises.resolve_import(module, lean, root, config["import_roots"])
            if target is None:
                kind = "gate" if module in config["generated_imports"] else "external"
                edges[rel].append((module, None, kind))
                continue
            if is_lake(module, target, root):
                edges[rel].append((module, None, "lake"))
                continue
            dep = target.relative_to(root).as_posix()
            if module.split(".")[0] in RESERVED:
                raise ValueError(f"{rel}: import {module} resolves to {dep}, shadowing a Lake or toolchain module")
            if named.setdefault(dep, module) != module:
                raise ValueError(f"{dep} is imported as both {named[dep]} and {module}")
            edges[rel].append((module, dep, "local"))
            pending.append(dep)

    def root_of(rel: str) -> str:
        if rel in named:
            return rel[:-len(named[rel].replace(".", "/") + ".lean")].rstrip("/") or "."
        # Not imported: the shallowest source root of its own local imports above it.
        bases = [root_of(dep) for _, dep, kind in edges[rel] if kind == "local"]
        bases = [b for b in bases if b == "." or rel.startswith(b + "/")]
        return min(bases, key=len) if bases else str(Path(rel).parent)

    gated: dict[str, str | None] = {}

    def gate_of(rel: str, seen=()) -> str | None:
        if rel not in gated:
            if any(kind == "gate" for _, _, kind in edges[rel]):
                if rel not in GATES:
                    raise ValueError(f"{rel} imports a gate-time module; add its auditing gate to GATES")
                gated[rel] = GATES[rel]
            else:
                gated[rel] = next((g for _, dep, kind in edges[rel] if kind == "local"
                                   if dep not in seen and (g := gate_of(dep, (*seen, rel)))), None)
        return gated[rel]

    units = []
    for rel in sorted(edges):
        base = root_of(rel)
        module = module_of(rel, base)
        # A top-level name it shares with a module it imports from another root
        # (`strength-log/GlobalInit.lean` importing `GlobalInit.Proofs`): Lean resolves an import
        # in the first library holding its top-level name, which may be this file's own library.
        clash = rel not in named and any(
            m.split(".")[0] == module.split(".")[0] for m, dep, kind in edges[rel]
            if kind == "local" and root_of(dep) != base)
        if not MODULE.fullmatch(module) or module.split(".")[0] in RESERVED or clash:
            # Not imported, so its name is free: `local-parent/Proofs.lean` must neither be an
            # invalid name nor the Lake library root `Proofs`, nor shadow its own imports.
            base, module = None, "Universe." + re.sub(r"\W", "_", str(Path(rel).with_suffix("")))
        units.append(Unit(rel, base, module, tuple(dep for _, dep, kind in edges[rel] if kind == "local"),
                          tuple(m for m, _, kind in edges[rel] if kind == "lake"), gate_of(rel),
                          tuple(sorted({d.name for d in repo.files[rel].decls if d.name}))))
    stale = set(GATES) - {u.file for u in units if u.gate and u.file in GATES}
    if stale:
        raise ValueError(f"GATES lists files that import no gate-time module: {sorted(stale)}")
    unaudited = sorted(g for g in set(GATES.values()) if "theorem_universe.py gate" not in (root / g).read_text())
    if unaudited:
        raise ValueError(f"gate scripts do not run `theorem_universe.py gate`: {unaudited}")
    missing = set(indexed) - {u.file for u in units}
    if missing:
        raise ValueError(f"indexed files outside the universe: {sorted(missing)}")
    return shipped, units


# ----------------------------------------------------------------------------- source scan

def scan_files(root: Path, units: list[Unit]) -> list[str]:
    shipped = sorted(p.relative_to(root).as_posix() for d in ("ZigLean", "Proofs") for p in (root / d).rglob("*.lean"))
    return sorted({"ZigLean.lean", *shipped, *(u.file for u in units)})


def scan_source(rel: str, text: str) -> tuple[list[str], dict[str, int]]:
    """Placeholders and kernel bypasses in one comment-stripped source, and its escape-hatch counts."""
    errors, found = [], {}
    for number, line in enumerate(premises_module().strip_comments(text).split("\n"), 1):
        errors += [f"{rel}:{number}: {m.group(0)}" for m in PLACEHOLDER.finditer(line)]
        if bypass := FORBIDDEN.search(line):
            errors.append(f"{rel}:{number}: kernel-check bypass ({bypass.group(0)})")
        for match in ESCAPE.finditer(line):
            token = match.group(1) or "@[" + match.group(2)
            found[token] = found.get(token, 0) + 1
    return errors, found


def scan(root: Path = ROOT) -> list[str]:
    _, units = universe(root)
    reviewed = json.loads((root / ESCAPES).read_text())
    if set(reviewed) != {"schema_version", "reviewed"} or reviewed["schema_version"] != 1:
        raise ValueError(f"{ESCAPES}: unsupported schema")
    errors, found = [], {}
    for rel in scan_files(root, units):
        problems, tokens = scan_source(rel, (root / rel).read_text())
        errors += problems
        if tokens:
            found[rel] = tokens
    for rel in sorted(set(found) | set(reviewed["reviewed"])):
        entry = dict(reviewed["reviewed"].get(rel, {}))
        reason = entry.pop("reason", "")
        if entry and not reason.strip():
            errors.append(f"{ESCAPES}: {rel} needs a review reason")
        if found.get(rel, {}) != entry:
            errors.append(f"{rel}: kernel escape hatches {found.get(rel, {})} differ from the reviewed {entry} "
                          f"in {ESCAPES}")
    return errors


# ----------------------------------------------------------------------------- compile and audit

def run(command: list[str], env: dict | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def base_paths(output: Path) -> list[Path]:
    """Expose only the authoritative Lake roots; foreign fixture outputs stay untouched."""
    output.mkdir(parents=True, exist_ok=True)
    view = Path(tempfile.mkdtemp(prefix="lake-view-", dir=output))
    built = ROOT / ".lake/build/lib/lean"
    roots = runpy.run_path(str(Path(__file__).with_name('lean-deps.py')))['lib_roots'](ROOT)
    if roots != set(LAKE_ROOTS):
        raise ValueError('Lake library roots differ from the assurance-owned roots')
    for name in sorted(roots):
        for suffix in ('', *assumptions.COMPILED_SUFFIXES):
            target = built / (name + suffix)
            if target.exists():
                (view / target.name).symlink_to(target.resolve(strict=True), target_is_directory=target.is_dir())
    view.chmod(0o555)
    return [view, Path(assumptions.lake_env("LEAN_SYSROOT")) / "lib/lean"]


def path_text(paths) -> str:
    return os.pathsep.join(str(p) for p in paths)


def compile_unit(file: str, root: str, olean: Path, lean_path, log: Path) -> str | None:
    olean.parent.mkdir(parents=True, exist_ok=True)
    assumptions.remove_module_outputs(olean)  # Never reuse an old proof or companion file.
    result = run(assumptions.lean_command(["-R", root, "-o", str(olean), file], path_text(lean_path)))
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout)
    if result.returncode:
        return f"{file}: Lean exited {result.returncode} (log {log})"
    # Examples never reach the olean, so the axiom audit cannot see a sorry inside one.
    if SORRY_WARNING in result.stdout:
        return f"{file}: {SORRY_WARNING} (log {log})"
    module = module_of(file, root)
    try:
        if assumptions.locate(module, lean_path) != olean.resolve(strict=True):
            return f"{file}: compiled module {module} is shadowed on the audit search path"
    except (OSError, ValueError) as error:
        return f"{file}: missing fresh compiled module {module}: {error}"
    return None


def audit_modules(modules: list[str], lean_path, output: Path, cache: Path | None = None,
                  sources: Path | None = None, expected_artifacts: dict | None = None) -> dict:
    started = time.monotonic()
    result = run([sys.executable, "-B", str(ROOT / "scripts/assumptions.py"), "--no-build", "--allow-no-theorems",
                  "--output", str(output), *(["--replay-cache", str(cache)] if cache else []),
                  *(["--sources", str(sources)] if sources else []),
                  "--lean-path", path_text(lean_path),
                  *(a for m in modules for a in ("--module", m))])
    sys.stderr.write(result.stdout)
    report = json.loads(output.read_text())
    if report.get('status') == 'pass' and expected_artifacts is not None:
        actual = {row['module']: row for row in report['freshness']['artifacts']}
        selected = set(modules)
        for module, (path, digest) in expected_artifacts.items():
            if assumptions.locate(module, lean_path) != path or assumptions.file_sha256(path) != digest:
                raise ValueError(f'private module {module} changed during its audit')
            row = actual.get(module)
            if module in selected and row is None:
                raise ValueError(f'private module {module} is absent from its audit')
            if row is not None and ((ROOT / row['olean']).resolve(strict=True), row['olean_sha256']) != (path, digest):
                raise ValueError(f'private module {module} audit resolved to a different artifact')
    return {"modules": modules, "report": str(output), "status": report.get("status"),
            "exit_code": result.returncode, "theorem_count": report.get("theorem_count", 0),
            "seconds": round(time.monotonic() - started, 1),
            "kernel_replay": (report.get("kernel_replay") or {}).get("status"),
            # Two test modules may declare the same name (`main`): they cannot share one environment.
            "collision": "environment already contains" in result.stdout,
            "violations": [v["name"] + ": " + v["reason"] for v in report.get("violations", [])] or
                          ([report["error"]] if report.get("error") else [])}


def lib_of(output: Path, root: str | None) -> Path:
    if root is None:
        return output / "lib" / "staged"
    return output / "lib" / (hashlib.sha256(root.encode()).hexdigest()[:12] + "-" + Path(root).name)


def staged(output: Path, u: Unit) -> tuple[str, str]:
    """Source path and `-R` root to compile; a renamed unit compiles as a byte-identical copy."""
    if u.root is not None:
        return u.file, u.root
    copy = output / "staged" / (u.module.replace(".", "/") + ".lean")
    copy.parent.mkdir(parents=True, exist_ok=True)
    copy.write_bytes((ROOT / u.file).read_bytes())
    return str(copy), str(output / "staged")


def closure(units, by_file: dict[str, Unit]) -> list[Unit]:
    seen, pending = {}, list(units)
    while pending:
        current = pending.pop()
        if current.file not in seen:
            seen[current.file] = current
            pending.extend(by_file[d] for d in current.deps)
    return list(seen.values())


def bundles(local: list[Unit], by_file, output) -> list[list[Unit]]:
    """Pack units into extractor runs that share no declaration name and whose libraries expose
    no module name twice; a collision the source parse misses splits the run (`audit`)."""
    exposed_roots: dict[Path, set] = {}
    for u in local:
        exposed_roots.setdefault(lib_of(output, u.root), set()).add(u.module.split('.')[0])
    packed: list[tuple[list[Unit], set, dict]] = []
    for u in local:
        units = closure([u], by_file)
        libs = {lib_of(output, c.root) for c in units}
        names = {n: c.file for c in units for n in c.names}
        for bundle, bundle_libs, bundle_names in packed:
            merged = bundle_libs | libs
            if (all(bundle_names.get(n, f) == f for n, f in names.items())
                    and sum(len(exposed_roots.get(lib, ())) for lib in merged)
                    == len(set().union(*(exposed_roots.get(lib, set()) for lib in merged)))):
                bundle.append(u)
                bundle_libs |= libs
                bundle_names |= names
                break
        else:
            packed.append(([u], libs, names))
    return [bundle for bundle, _, _ in packed]


def compile_all(local: list[Unit], by_file, output: Path, extra_paths=(), overrides=None,
                base=()) -> list[str]:
    """Compile in topological levels: a module after every local module it imports."""
    errors, done, remaining = [], set(), list(local)
    jobs = max(1, int(os.environ.get("AIR2LEAN_UNIVERSE_JOBS") or os.environ.get("AIR2LEAN_JOBS")
                      or min(4, os.cpu_count() or 1)))

    def build_one(u):
        libs = [*base, *sorted({lib_of(output, c.root) for c in closure([u], by_file)}), *extra_paths]
        olean = lib_of(output, u.root) / (u.module.replace(".", "/") + ".olean")
        source, root = (overrides or {}).get(u.file) or staged(output, u)
        return compile_unit(source, root, olean, libs, output / "logs" / (u.file.replace("/", "__") + ".log"))

    with ThreadPoolExecutor(jobs) as pool:
        while remaining:
            ready = [u for u in remaining if set(u.deps) <= done]
            if not ready:
                raise ValueError(f"import cycle among {[u.file for u in remaining]}")
            errors += [e for e in pool.map(build_one, ready) if e]
            done |= {u.file for u in ready}
            remaining = [u for u in remaining if u.file not in done]
    return errors


def audit_bundles(local: list[Unit], by_file, output: Path, replay_cache: Path | None,
                  extra_paths=(), base=()) -> tuple[list[dict], list[str]]:
    """The same collision-safe extraction and source classification for ordinary and gate units."""
    errors = []
    runs, pending = [], bundles(local, by_file, output)
    while pending:
        bundle = pending.pop(0)
        units = closure(bundle, by_file)
        libs = [*base, *sorted({lib_of(output, u.root) for u in units}), *extra_paths]
        expected = {}
        for unit in units:
            path = (lib_of(output, unit.root) / (unit.module.replace(".", "/") + ".olean")).resolve(strict=True)
            if assumptions.locate(unit.module, libs) != path:
                raise ValueError(f"private module {unit.module} is shadowed on the audit search path")
            expected[unit.module] = (path, assumptions.file_sha256(path))
        # The audit classifies generated declarations by their module's metadata (assumptions.py
        # `generated_premises`): every unit's source, the run's own closure winning a name clash.
        sources = output / f"sources-{len(runs)}.json"
        write_report(sources, {**{u.module: u.file for u in by_file.values()},
                               **{u.module: u.file for u in units}})
        result = audit_modules(sorted(u.module for u in bundle), libs, output / f"audit-{len(runs)}.json",
                               replay_cache, sources, expected)
        runs.append(result)
        if result["collision"] and len(bundle) > 1:
            result["status"] = "split"
            pending += [bundle[:len(bundle) // 2], bundle[len(bundle) // 2:]]
        elif result["status"] != "pass" or result["exit_code"]:
            errors += result["violations"] or [f"audit {result['report']} exited {result['exit_code']}"]
    return runs, errors


def audit(output: Path, build: bool, shipped_report: Path | None, replay_cache: Path | None) -> dict:
    shipped, units = universe()
    by_file = {u.file: u for u in units}
    local = [u for u in units if u.gate is None]
    if build:
        result = run(["lake", "build", *sorted({m for u in local for m in u.lake})])
        if result.returncode:
            raise RuntimeError(f"lake build failed:\n{result.stdout[-4000:]}")
    started = time.monotonic()
    base = base_paths(output)
    errors = compile_all(local, by_file, output, base=base)
    compile_seconds = round(time.monotonic() - started, 1)
    if errors:
        return {"schema_version": 1, "status": "fail", "errors": errors}
    runs, errors = audit_bundles(local, by_file, output, replay_cache, base=base)
    if shipped_report is not None:
        report = json.loads(shipped_report.read_text())
        if (report.get("status") != "pass" or report.get("scope") != "all-shipped-modules"
                or report.get("modules") != shipped or (report.get("kernel_replay") or {}).get("status") != "pass"):
            errors.append(f"{shipped_report}: not a passing, kernel-replayed audit of every shipped module")
        else:
            try:  # CI's selected translation may rewrite tracked Gen.lean files; digests still bind.
                assumptions.verify_fresh(report, allow_dirty=True)
            except ValueError as error:
                errors.append(f"{shipped_report}: {error}")
    return {"schema_version": 1, "status": "fail" if errors else "pass", "errors": errors,
            "shipped_modules": shipped, "shipped_report": str(shipped_report) if shipped_report else None,
            "units": [{"file": u.file, "root": u.root, "module": u.module, "gate": u.gate} for u in units],
            "compile_seconds": compile_seconds,
            "audits": runs}


def gate_units(units: list[Unit], roots) -> list[Unit]:
    """Every dependent of a registered gate root, including transitive strength-log clients."""
    clients: dict[str, list[str]] = {}
    for unit in units:
        for dependency in unit.deps:
            clients.setdefault(dependency, []).append(unit.file)
    reached, pending = set(roots), list(roots)
    while pending:
        for client in clients.get(pending.pop(), ()):
            if client not in reached:
                reached.add(client)
                pending.append(client)
    return [unit for unit in units if unit.file in reached]


def gate(source: Path, root: Path, lean_path: Path, output: Path) -> dict:
    """Audit a gate's copied root and all theorem units that transitively import it."""
    roots = [f for f in GATES if Path(f).name == source.name and (ROOT / f).read_bytes() == source.read_bytes()]
    if not roots:
        raise ValueError(f"{source} is not a copy of a gate-audited file {sorted(GATES)}")
    _, units = universe()
    by_file = {u.file: u for u in units}
    module = module_of(str(source), str(root))
    if any(by_file[f].module != module for f in roots):
        raise ValueError(f"gate copy {module} does not preserve its registered module identity")
    selected = gate_units(units, roots)
    local = closure(selected, by_file)
    base = base_paths(output)
    errors = compile_all(local, by_file, output, [lean_path],
                         {f: (str(source), str(root)) for f in roots}, base=base)
    if errors:
        return {"schema_version": 1, "status": "fail", "errors": errors}
    runs, errors = audit_bundles(selected, by_file, output, output / "replay-cache.json", [lean_path], base=base)
    if not any(r.get("theorem_count", 0) for r in runs if r["status"] == "pass"):
        errors.append("no audited theorem")
    return {"schema_version": 1, "status": "fail" if errors else "pass", "audits": runs,
            "units": [u.file for u in selected], "errors": errors}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("list")
    sub.add_parser("scan")
    audit_cmd = sub.add_parser("audit")
    audit_cmd.add_argument("--output-dir", type=Path, required=True)
    audit_cmd.add_argument("--shipped", type=Path, help="all-shipped-modules scripts/assumptions.py report")
    audit_cmd.add_argument("--no-build", action="store_true", help="do not build the imported Lake modules")
    audit_cmd.add_argument("--replay-cache", type=Path,
                           help="kernel-replay cache shared with the shipped audit of the same build")
    gate_cmd = sub.add_parser("gate")
    gate_cmd.add_argument("file", help="the gate's copy of a GATES file")
    gate_cmd.add_argument("--root", required=True, help="`lean -R` root of the copied file")
    gate_cmd.add_argument("--lean-path", type=Path, required=True, help="directory with the generated oleans")
    gate_cmd.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "list":
            shipped, units = universe()
            print(json.dumps({"shipped_modules": shipped, "units": [u.__dict__ for u in units]}, indent=1))
            return 0
        if args.command == "scan":
            errors = scan()
            for error in errors:
                print(f"error: {error}", file=sys.stderr)
            print(f"theorem universe scan {'fail' if errors else 'pass'}", file=sys.stderr)
            return 1 if errors else 0
        output = args.output_dir.resolve()
        output.mkdir(parents=True, exist_ok=True)
        if args.command == "audit":
            cache = args.replay_cache or output / "replay-cache.json"
            if args.replay_cache is None:
                cache.unlink(missing_ok=True)  # The default cache serves this run only.
            report = audit(output, not args.no_build, args.shipped, cache)
        else:
            report = gate(Path(args.file).resolve(), Path(args.root).resolve(), args.lean_path.resolve(), output)
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print(f"theorem universe error: {error}", file=sys.stderr)
        return 2
    write_report(output / "universe.json", report)
    for error in report["errors"]:
        print(f"  {error}", file=sys.stderr)
    print(f"theorem universe {report['status']}: report {output / 'universe.json'}", file=sys.stderr)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
