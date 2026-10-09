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
import subprocess
import sys
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
        if not MODULE.fullmatch(module) or module.split(".")[0] in RESERVED:
            # Not imported, so its name is free: `local-parent/Proofs.lean` must neither be an
            # invalid name nor the Lake library root `Proofs`.
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


def with_lean_path(paths) -> dict:
    # `lake env` appends a caller's LEAN_PATH after the package and toolchain libraries.
    return {**os.environ, "LEAN_PATH": os.pathsep.join(str(p) for p in paths)}


def compile_unit(file: str, root: str, olean: Path, lean_path, log: Path) -> str | None:
    olean.parent.mkdir(parents=True, exist_ok=True)
    result = run(["lake", "env", "lean", "-R", root, "-o", str(olean), file], with_lean_path(lean_path))
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout)
    if result.returncode:
        return f"{file}: Lean exited {result.returncode} (log {log})"
    # Examples never reach the olean, so the axiom audit cannot see a sorry inside one.
    if SORRY_WARNING in result.stdout:
        return f"{file}: {SORRY_WARNING} (log {log})"
    return None


def audit_modules(modules: list[str], lean_path, output: Path, cache: Path | None = None) -> dict:
    started = time.monotonic()
    result = run([sys.executable, "-B", str(ROOT / "scripts/assumptions.py"), "--no-build", "--allow-no-theorems",
                  "--output", str(output), *(["--replay-cache", str(cache)] if cache else []),
                  *(a for m in modules for a in ("--module", m))], with_lean_path(lean_path))
    sys.stderr.write(result.stdout)
    report = json.loads(output.read_text())
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
    exposed: dict[Path, set] = {}
    for u in local:
        exposed.setdefault(lib_of(output, u.root), set()).add(u.module)
    packed: list[tuple[list[Unit], set, dict]] = []
    for u in local:
        units = closure([u], by_file)
        libs = {lib_of(output, c.root) for c in units}
        names = {n: c.file for c in units for n in c.names}
        for bundle, bundle_libs, bundle_names in packed:
            merged = bundle_libs | libs
            if (all(bundle_names.get(n, f) == f for n, f in names.items())
                    and sum(len(exposed.get(lib, ())) for lib in merged)
                    == len(set().union(*(exposed.get(lib, set()) for lib in merged)))):
                bundle.append(u)
                bundle_libs |= libs
                bundle_names |= names
                break
        else:
            packed.append(([u], libs, names))
    return [bundle for bundle, _, _ in packed]


def compile_all(local: list[Unit], by_file, output: Path) -> list[str]:
    """Compile in topological levels: a module after every local module it imports."""
    # `lake env` puts its own library first on LEAN_PATH, so a top-level name present there
    # (e.g. `tests/` from fixture scripts that compile into it) would shadow a universe module.
    built = ROOT / ".lake/build/lib/lean"
    shadowed = sorted({top for u in local if (top := u.module.split(".")[0]) not in LAKE_ROOTS
                       and ((built / top).exists() or (built / (top + ".olean")).exists())})
    if shadowed:
        raise ValueError(f"{built} contains {shadowed}, which would shadow theorem-universe modules; "
                         "remove those stray fixture outputs")
    errors, done, remaining = [], set(), list(local)
    jobs = max(1, int(os.environ.get("AIR2LEAN_UNIVERSE_JOBS") or min(4, os.cpu_count() or 1)))

    def build_one(u):
        libs = sorted({lib_of(output, c.root) for c in closure([u], by_file)})
        olean = lib_of(output, u.root) / (u.module.replace(".", "/") + ".olean")
        source, root = staged(output, u)
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


def audit(output: Path, build: bool, shipped_report: Path | None, replay_cache: Path | None) -> dict:
    shipped, units = universe()
    by_file = {u.file: u for u in units}
    local = [u for u in units if u.gate is None]
    if build:
        result = run(["lake", "build", *sorted({m for u in local for m in u.lake})])
        if result.returncode:
            raise RuntimeError(f"lake build failed:\n{result.stdout[-4000:]}")
    started = time.monotonic()
    errors = compile_all(local, by_file, output)
    compile_seconds = round(time.monotonic() - started, 1)
    if errors:
        return {"schema_version": 1, "status": "fail", "errors": errors}
    runs, pending = [], bundles(local, by_file, output)
    while pending:
        bundle = pending.pop(0)
        libs = sorted({lib_of(output, u.root) for u in closure(bundle, by_file)})
        result = audit_modules(sorted(u.module for u in bundle), libs, output / f"audit-{len(runs)}.json",
                               replay_cache)
        runs.append(result)
        if result["collision"] and len(bundle) > 1:
            result["status"] = "split"
            pending += [bundle[:len(bundle) // 2], bundle[len(bundle) // 2:]]
        elif result["status"] != "pass" or result["exit_code"]:
            errors += result["violations"] or [f"audit {result['report']} exited {result['exit_code']}"]
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


def gate(source: Path, root: Path, lean_path: Path, output: Path) -> dict:
    """Compile and audit a gate's copy of a GATES file against its gate-time generated modules."""
    if not any((ROOT / f).read_bytes() == source.read_bytes() for f in GATES if Path(f).name == source.name):
        raise ValueError(f"{source} is not a copy of a gate-audited file {sorted(GATES)}")
    lib = output / "lib"
    module = module_of(str(source), str(root))
    error = compile_unit(str(source), str(root), lib / (module.replace(".", "/") + ".olean"), [lib, lean_path],
                         output / "compile.log")
    if error:
        return {"schema_version": 1, "status": "fail", "errors": [error]}
    result = audit_modules([module], [lib, lean_path], output / "assurance.json")
    ok = result["status"] == "pass" and not result["exit_code"] and result["theorem_count"] > 0
    return {"schema_version": 1, "status": "pass" if ok else "fail", "audits": [result],
            "errors": [] if ok else result["violations"] or ["no audited theorem"]}


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
