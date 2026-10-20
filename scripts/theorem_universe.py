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
import contextlib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import hashlib
import io
import json
import os
from pathlib import Path
import re
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


def with_lean_path(paths) -> dict:
    # `lake env` appends a caller's LEAN_PATH after the package and toolchain libraries.
    return {**os.environ, "LEAN_PATH": os.pathsep.join(str(p) for p in paths)}


def compile_unit(file: str, root: str, olean: Path, lean_path, log: Path, *,
                 resolved_path: str | None = None) -> str | None:
    olean.parent.mkdir(parents=True, exist_ok=True)
    arguments = ['-R', root, '-o', str(olean), file]
    result = (run(assumptions.lean_command(arguments, resolved_path)) if resolved_path is not None else
              run(["lake", "env", "lean", *arguments], with_lean_path(lean_path)))
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout)
    if result.returncode:
        return f"{file}: Lean exited {result.returncode} (log {log})"
    # Examples never reach the olean, so the axiom audit cannot see a sorry inside one.
    if SORRY_WARNING in result.stdout:
        return f"{file}: {SORRY_WARNING} (log {log})"
    if resolved_path is not None and not olean.is_file():
        return f'{file}: missing fresh compiler-owned Unit output {olean}'
    return None


def audit_modules(modules: list[str], lean_path, output: Path, cache: Path | None = None,
                  sources: Path | None = None, *, all_declarations: bool = False,
                  compiled_units: dict | None = None) -> dict:
    """Audit this exact module set; optional declaration evidence stays in the same full report."""
    started = time.monotonic()
    arguments = ["--no-build", "--allow-no-theorems", "--output", str(output),
                 *(["--replay-cache", str(cache)] if cache else []),
                 *(["--sources", str(sources)] if sources else []),
                 *(["--all-declarations"] if all_declarations else []),
                 *(a for m in modules for a in ("--module", m))]
    if compiled_units is None:
        result = run([sys.executable, "-B", str(ROOT / "scripts/assumptions.py"), *arguments],
                     with_lean_path(lean_path))
    else:
        # The compiler owner calls the SAME CLI orchestration with an internal run context.
        # There is deliberately no public --compiled/--sources-to-freshness promotion.
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured), contextlib.redirect_stderr(captured):
            code = assumptions.main(arguments, compiled_units=compiled_units)
        result = subprocess.CompletedProcess(arguments, code, captured.getvalue())
    sys.stderr.write(result.stdout)
    report = json.loads(output.read_text())
    if compiled_units is not None and report.get('status') == 'pass':
        if (report.get('freshness') or {}).get('compiled_units') != compiled_units:
            raise ValueError('compiler-owned Unit audit omitted its exact run binding')
        verify_compilation(compiled_units)
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


def compiler_paths(output: Path, u: Unit) -> tuple[str, str]:
    """The existing source/staging plan, without writing or refreshing any input."""
    if u.root is not None:
        return u.file, u.root
    copy = output / "staged" / (u.module.replace(".", "/") + ".lean")
    return str(copy), str(output / "staged")


def staged(output: Path, u: Unit) -> tuple[str, str]:
    """Source path and `-R` root to compile; a renamed unit compiles as a byte-identical copy."""
    source, root = compiler_paths(output, u)
    if u.root is not None:
        return source, root
    copy = Path(source)
    copy.parent.mkdir(parents=True, exist_ok=True)
    copy.write_bytes((ROOT / u.file).read_bytes())
    return source, root


def closure(units, by_file: dict[str, Unit]) -> list[Unit]:
    seen, pending = {}, list(units)
    while pending:
        current = pending.pop()
        if current.file not in seen:
            seen[current.file] = current
            pending.extend(by_file[d] for d in current.deps)
    return list(seen.values())


def input_identity(path: Path) -> dict:
    """Actual compiler file bytes and the identities of aliases on its selected path."""
    path = path.absolute()
    if not path.is_file():
        raise ValueError(f'missing compiler-owned Unit input/output: {path}')
    return {'path': assumptions.display(path), 'resolved': str(path.resolve(strict=True)),
            'sha256': assumptions.file_sha256(path),
            'links': [[str(part), os.readlink(part)] for part in (path, *path.parents)
                      if part.is_symlink()]}


def input_digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def unit_plan(units: list[Unit]) -> dict:
    records = {}
    for unit in units:
        if unit.module in records:
            raise ValueError(f'ambiguous compiler-owned Unit module: {unit.module}')
        records[unit.module] = {'file': unit.file, 'root': unit.root,
                                'deps': list(unit.deps), 'lake': list(unit.lake)}
    return records


def prepare_compilation(selected: list[Unit], by_file: dict[str, Unit], output: Path, *,
                        witness_registry: dict | None = None) -> dict:
    """Snapshot actual inputs BEFORE the existing compiler writes any Unit output."""
    output = output.absolute()
    local = closure(selected, by_file)
    # Prepare the SAME extractor first: its build cannot legitimately change a later frozen
    # compiler/auditor input. extract() still validates it under its ordinary lock.
    with assumptions.prepared_tool():
        pass
    libraries = sorted({lib_of(output, unit.root) for unit in local})
    resolved = run(['lake', 'env', 'printenv', 'LEAN_PATH'], with_lean_path(libraries))
    if resolved.returncode or not resolved.stdout.strip() or len(resolved.stdout.strip().splitlines()) != 1:
        raise ValueError('cannot resolve the compiler-owned Unit lookup path: ' + resolved.stdout)
    entries = resolved.stdout.strip().split(os.pathsep)
    if any(not path for path in entries):
        raise ValueError('compiler-owned Unit lookup roots must be nonempty')
    paths = [(ROOT / path).absolute() for path in entries]
    lean_path = os.pathsep.join(map(str, paths))
    # Lean chooses the first library holding a TOP-LEVEL name, not the first matching file.
    # Refuse ambiguous private roots instead of compiling one artifact and auditing another.
    tops = {}
    for unit in local:
        library = lib_of(output, unit.root)
        top = unit.module.split('.')[0]
        if tops.setdefault(top, library) != library:
            raise ValueError(f'ambiguous private lookup roots for {top}')
    records = unit_plan(local)
    for unit in local:
        original = input_identity(ROOT / unit.file)
        source, source_root = staged(output, unit)
        compiler_source = input_identity(ROOT / source)
        if original['sha256'] != compiler_source['sha256']:
            raise ValueError(f'compiler-owned Unit staged source differs: {unit.module}')
        olean = lib_of(output, unit.root) / (unit.module.replace('.', '/') + '.olean')
        # These are this run's expected private outputs only. Never fall back to an old copy
        # or a leftover loaded companion after a compiler failure.
        for suffix in assumptions.COMPILED_SUFFIXES:
            olean.with_name(olean.name[:-len('.olean')] + suffix).unlink(missing_ok=True)
        records[unit.module].update(source=original, compiler_source=compiler_source,
                                    compiler_root=source_root, output_path=str(olean.absolute()))
    private_roots = {path.resolve() for path in libraries}
    base = [path for path in paths if path.resolve() not in private_roots]
    if not base:
        raise ValueError('compiler-owned Unit path has no existing Lake/toolchain inputs')
    toolchain = Path(assumptions.lake_env('LEAN_SYSROOT')).resolve()
    context = {'selected_files': sorted(unit.file for unit in selected),
               'selected_modules': sorted(unit.module for unit in selected),
               'units': records, 'output_dir': str(output), 'lean_path': lean_path,
               'base_path': os.pathsep.join(map(str, base)),
               'base_inputs': assumptions.lean_path_binding(ROOT, os.pathsep.join(map(str, base))),
               'lean_sysroot': str(toolchain),
               'toolchain_runtime_sha256': assumptions.toolchain_runtime_sha256(toolchain),
               'library_sources_sha256': input_digest(assumptions.library_source_inputs(ROOT))}
    if witness_registry is not None:
        context['witness_registry'] = witness_registry
    verify_compiler_inputs(context)
    return context


def compilation_plan(context: dict) -> list[Unit]:
    """Re-derive the source plan; a saved context cannot choose different source paths."""
    if (not isinstance(context, dict) or not isinstance(context.get('units'), dict)
            or not isinstance(context.get('selected_files'), list)
            or not isinstance(context.get('selected_modules'), list)
            or not isinstance(context.get('output_dir'), str)
            or not Path(context['output_dir']).is_absolute()):
        raise ValueError('missing compiler-owned Unit run binding')
    _, units = universe()
    by_file = {unit.file: unit for unit in units}
    if 'witness_registry' in context:
        if input_identity(ROOT / assumptions.WITNESS_FIXTURES) != context['witness_registry']:
            raise ValueError('assurance report is stale: witness registry changed')
        registered = assumptions.witness_fixtures()
        if any(file not in by_file or by_file[file].gate is not None for file in registered):
            raise ValueError('registered witness selection changed or needs a gate')
        expected = sorted(unit.file for unit in closure([by_file[file] for file in registered], by_file))
        if context['selected_files'] != expected:
            raise ValueError('compiled witness closure differs from the registry')
        if context['output_dir'] != str((ROOT / '.lake/assurance/witness-fixtures').absolute()):
            raise ValueError('compiled witness output differs from its registered producer')
    elif not context['units'] or not context['selected_files']:
        raise ValueError('missing compiler-owned Unit run binding')
    if any(file not in by_file or by_file[file].gate is not None for file in context['selected_files']):
        raise ValueError('compiler-owned Unit source selection changed or needs a gate')
    selected = [by_file[file] for file in context['selected_files']]
    local = closure(selected, by_file)
    planned = unit_plan(local)
    recorded = {module: {key: unit[key] for key in ('file', 'root', 'deps', 'lake')}
                for module, unit in context['units'].items()}
    if (planned != recorded or sorted(unit.module for unit in selected) != context['selected_modules']
            or sorted(set(context['selected_files'])) != context['selected_files']):
        raise ValueError('compiler-owned Unit import/source resolution changed')
    return local


def verify_compiler_inputs(context: dict) -> None:
    local = compilation_plan(context)
    output = Path(context['output_dir'])
    for planned in local:
        module, unit = planned.module, context['units'][planned.module]
        source, root = compiler_paths(output, planned)
        expected_output = str((lib_of(output, planned.root) / (module.replace('.', '/') + '.olean')).absolute())
        if unit['compiler_root'] != root or unit['output_path'] != expected_output:
            raise ValueError(f'compiler-owned Unit compiler/output path differs from its source plan: {module}')
        for kind, path in (('source', ROOT / planned.file), ('compiler_source', ROOT / source)):
            if input_identity(path) != unit[kind]:
                raise ValueError(f'assurance report is stale: {module} {kind} changed')
        if unit['source']['sha256'] != unit['compiler_source']['sha256']:
            raise ValueError(f'compiler-owned Unit staged source differs: {module}')
    toolchain = Path(assumptions.lake_env('LEAN_SYSROOT')).resolve()
    if (str(toolchain) != context['lean_sysroot'] or
            assumptions.toolchain_runtime_sha256(toolchain) != context['toolchain_runtime_sha256']):
        raise ValueError('compiler-owned Unit runtime changed')
    if input_digest(assumptions.library_source_inputs(ROOT)) != context['library_sources_sha256']:
        raise ValueError('compiler-owned Unit library sources changed')
    if assumptions.lean_path_binding(ROOT, context['base_path']) != context['base_inputs']:
        raise ValueError('compiler-owned Unit imported inputs changed')


def compiled_output(path: Path) -> list:
    """Loaded output companions, including their absence, at compiler completion."""
    records = []
    for suffix in assumptions.COMPILED_SUFFIXES:
        companion = path.with_name(path.name[:-len('.olean')] + suffix)
        if companion.is_symlink() and not companion.is_file():
            raise ValueError(f'missing compiler-owned Unit output target: {companion}')
        records.append([suffix, input_identity(companion) if companion.exists() else None])
    if records[0][1] is None:
        raise ValueError(f'missing compiler-owned Unit output: {path}')
    return records


def verify_compilation(context: dict) -> None:
    """Validate the SAME compiler-owned correspondence at audit and report admission."""
    verify_compiler_inputs(context)
    paths = [Path(path) for path in context['lean_path'].split(os.pathsep)]
    for module, unit in context['units'].items():
        path = Path(unit['output_path'])
        if assumptions.locate(module, paths).resolve(strict=True) != path.resolve(strict=True):
            raise ValueError(f'compiler-owned Unit output is shadowed: {module}')
        if compiled_output(path) != unit.get('outputs'):
            raise ValueError(f'compiler-owned Unit output changed: {module}')
    if assumptions.lean_path_binding(ROOT, context['lean_path']) != context.get('lookup_inputs'):
        raise ValueError('compiler-owned Unit lookup inputs changed')


def seal_compilation(context: dict) -> None:
    """Seal only outputs captured at each successful compiler completion."""
    context['lookup_inputs'] = assumptions.lean_path_binding(ROOT, context['lean_path'])
    verify_compilation(context)


def verify_compiled_report(report: dict) -> None:
    """Known non-gated Unit selections require their exact compiler-owned run evidence.

    Inventory membership only demands evidence. It never grants source or artifact authority
    to a name, an arbitrary external module, a gate, or the classification-only --sources map.
    """
    context = report['freshness'].get('compiled_units')
    selected = report.get('modules', [])
    artifacts = {}
    for row in report['freshness']['artifacts']:
        artifacts.setdefault(row['module'], []).append(row)
    if context is None:
        if report.get('scope') == 'all-shipped-modules' or report.get('witness_modules'):
            raise ValueError('shipped witness audit carries no compiler-owned run binding')
        _, units = universe()
        known = {unit.module for unit in units if unit.gate is None}
        headers = report.get('module_imports') or {}
        represented = set(selected) | artifacts.keys() | headers.keys()
        for dependencies in headers.values():
            represented.update(dependencies or [])
        for key in ('nodes', 'theorems', 'witness_theorems'):
            represented.update(row.get('module') for row in report.get(key, []))
        required = known.intersection(represented)
        if required:
            raise ValueError('known non-gated Unit audit carries no compiler-owned run binding')
        return
    verify_compilation(context)
    if 'witness_registry' in context:
        if (report.get('scope') != 'all-shipped-modules' or selected != shipped_modules()
                or report.get('witness_modules') != context['selected_modules']):
            raise ValueError('compiled witness context differs from the shipped report selection')
    elif (selected != context['selected_modules'] or report.get('witness_modules')
          or report.get('scope') == 'all-shipped-modules'):
        raise ValueError('compiled Unit context differs from the report selection')
    for module, unit in context['units'].items():
        rows = artifacts.get(module, [])
        expected = {'module': module, 'olean': assumptions.display(Path(unit['output_path'])),
                    'olean_sha256': unit['outputs'][0][1]['sha256'],
                    'source': unit['source']['path'], 'source_sha256': unit['source']['sha256']}
        if rows != [expected]:
            raise ValueError(f'compiler-owned Unit report source/output differs from its run binding: {module}')
    compiled_imports(report, context, [Path(path) for path in context['lean_path'].split(os.pathsep)],
                     Path(context['lean_sysroot']))


def compiled_imports(raw: dict, context: dict, paths: list[Path], toolchain: Path) -> set[str]:
    """Actual header closure, independently of whether a declaration references an import."""
    headers = raw.get('module_imports')
    if not isinstance(headers, dict):
        raise ValueError('compiler-owned Unit audit has no actual import headers')
    seen, pending = set(), list({*raw.get('modules', []), *context['selected_modules']})
    built, standard = ROOT / '.lake/build/lib/lean', toolchain / 'lib/lean'
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        actual = assumptions.locate(module, paths).resolve(strict=True)
        relative = module.replace('.', '/') + '.olean'
        if module in context['units']:
            expected = Path(context['units'][module]['output_path']).resolve(strict=True)
        elif module.split('.')[0] in TOOLCHAIN_ROOTS:
            expected = (standard / relative).resolve(strict=True)
        elif module.split('.')[0] in LAKE_ROOTS:
            expected = (built / relative).resolve(strict=True)
            if (not actual.is_relative_to(built.resolve())
                    or not (ROOT / (module.replace('.', '/') + '.lean')).is_file()):
                raise ValueError(f'compiler-owned Unit has unverified Lake import: {module}')
        else:
            raise ValueError(f'compiler-owned Unit has unowned private import: {module}')
        if actual != expected:
            raise ValueError(f'compiler-owned Unit import resolves to a different artifact: {module}')
        imports = headers.get(module)
        if module.split('.')[0] in TOOLCHAIN_ROOTS and imports is None:
            continue  # The complete pinned installation is independently runtime-bound.
        if not isinstance(imports, list) or not all(isinstance(dep, str) for dep in imports):
            raise ValueError(f'compiler-owned Unit has incomplete import headers: {module}')
        pending.extend(imports)
    if set(context['units']) - seen:
        raise ValueError('compiler-owned Unit planned closure differs from actual import headers')
    return seen


def bundles(local: list[Unit], by_file, output) -> list[list[Unit]]:
    """Pack units into extractor runs that share no declaration name and whose libraries expose
    no module name twice; a collision the source parse misses splits the run (`audit`)."""
    exposed: dict[Path, set] = {}
    for u in local:
        exposed.setdefault(lib_of(output, u.root), set()).add(u.module.split('.')[0])
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


def compile_all(local: list[Unit], by_file, output: Path, *, compiled_units: dict | None = None) -> list[str]:
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
    jobs = assumptions.stage_jobs("AIR2LEAN_UNIVERSE_JOBS")

    def build_one(u):
        olean = lib_of(output, u.root) / (u.module.replace(".", "/") + ".olean")
        if compiled_units is not None:
            libs = []  # The SAME explicit ordered path is already frozen in this context.
            record = compiled_units['units'][u.module]
            source, root = record['compiler_source']['path'], record['compiler_root']
        else:
            libs = sorted({lib_of(output, c.root) for c in closure([u], by_file)})
            source, root = staged(output, u)
        error = compile_unit(source, root, olean, libs, output / "logs" / (u.file.replace("/", "__") + ".log"),
                             **({'resolved_path': compiled_units['lean_path']}
                                if compiled_units is not None else {}))
        if error is None and compiled_units is not None:
            record['outputs'] = compiled_output(olean)
        return error

    with ThreadPoolExecutor(jobs) as pool:
        while remaining:
            ready = [u for u in remaining if set(u.deps) <= done]
            if not ready:
                raise ValueError(f"import cycle among {[u.file for u in remaining]}")
            errors += [e for e in pool.map(build_one, ready) if e]
            done |= {u.file for u in ready}
            remaining = [u for u in remaining if u.file not in done]
    return errors


def compile_witness_fixtures(files: list[str], output: Path, build: bool) -> tuple[dict, dict]:
    """Compile the registered witness-fixture files (assurance/witness-fixtures.json) and the
    local modules they import into `output`, for the shipped audit (scripts/assumptions.py).
    Returns the classification source map and the SAME compiler-owned run context. The
    registry and actual inputs precede compilation, including an empty registered closure."""
    registry = input_identity(ROOT / assumptions.WITNESS_FIXTURES)
    if files != assumptions.witness_fixtures():
        raise ValueError('registered witness selection changed before compilation')
    _, units = universe()
    by_file = {u.file: u for u in units}
    missing = [f for f in files if f not in by_file]
    if missing:
        raise ValueError(f"witness fixtures outside the theorem universe (docs/premise-index.md): {missing}")
    gated = [f for f in files if by_file[f].gate is not None]
    if gated:
        raise ValueError(f"witness fixtures that need a gate-time generated module: {gated}")
    local = closure([by_file[f] for f in files], by_file)
    imports = sorted({m for u in local for m in u.lake})
    if build and imports:
        result = run(["lake", "build", *imports])
        if result.returncode:
            raise RuntimeError(f"lake build failed:\n{result.stdout[-4000:]}")
    context = prepare_compilation(local, by_file, output, witness_registry=registry)
    errors = compile_all(local, by_file, output, compiled_units=context)
    if errors:
        raise RuntimeError("; ".join(errors))
    seal_compilation(context)
    return {u.module: u.file for u in local}, context


def audit(output: Path, build: bool, shipped_report: Path | None, replay_cache: Path | None) -> dict:
    shipped, units = universe()
    by_file = {u.file: u for u in units}
    local = [u for u in units if u.gate is None]
    if build:
        result = run(["lake", "build", *sorted({m for u in local for m in u.lake})])
        if result.returncode:
            raise RuntimeError(f"lake build failed:\n{result.stdout[-4000:]}")
    errors, compile_seconds = [], 0.0
    runs, pending = [], bundles(local, by_file, output)
    output.mkdir(parents=True, exist_ok=True)
    while pending:
        bundle = pending.pop(0)
        private = Path(tempfile.mkdtemp(prefix=f'bundle-{len(runs)}-', dir=output))
        compiled = closure(bundle, by_file)
        started = time.monotonic()
        context = prepare_compilation(bundle, by_file, private)
        failures = compile_all(compiled, by_file, private, compiled_units=context)
        compile_seconds += time.monotonic() - started
        if failures:
            errors += failures
            runs.append({'modules': sorted(u.module for u in bundle), 'status': 'fail',
                         'violations': failures, 'exit_code': 2})
            continue
        seal_compilation(context)
        # The audit classifies generated declarations by their module's metadata (assumptions.py
        # `generated_premises`): every unit's source, the run's own closure winning a name clash.
        sources = output / f"sources-{len(runs)}.json"
        write_report(sources, {**{u.module: u.file for u in units},
                               **{u.module: u.file for u in compiled}})
        result = audit_modules(sorted(u.module for u in bundle), [], output / f"audit-{len(runs)}.json",
                               replay_cache, sources, compiled_units=context)
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
            "compile_seconds": round(compile_seconds, 1),
            "audits": runs}


def gate(source: Path, root: Path, lean_path: Path, output: Path, replay_cache: Path | None = None) -> dict:
    """Compile and audit a gate's copy of a GATES file against its gate-time generated modules.

    The gates of one script run re-audit the same Lake-built library: `replay_cache` (a file in the
    run's own temporary directory, so nothing outlives the run) shares their replays, keyed as
    `assumptions.kernel_replay` keys it (byte-identical Lake-built oleans, same leanchecker)."""
    if not any((ROOT / f).read_bytes() == source.read_bytes() for f in GATES if Path(f).name == source.name):
        raise ValueError(f"{source} is not a copy of a gate-audited file {sorted(GATES)}")
    lib = output / "lib"
    module = module_of(str(source), str(root))
    error = compile_unit(str(source), str(root), lib / (module.replace(".", "/") + ".olean"), [lib, lean_path],
                         output / "compile.log")
    if error:
        return {"schema_version": 1, "status": "fail", "errors": [error]}
    result = audit_modules([module], [lib, lean_path], output / "assurance.json", replay_cache)
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
    gate_cmd.add_argument("--replay-cache", type=Path,
                          help="kernel-replay cache shared by the gates of one script run (a fresh file in its "
                               "temporary directory; default: none)")
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
            report = gate(Path(args.file).resolve(), Path(args.root).resolve(), args.lean_path.resolve(), output,
                          args.replay_cache and args.replay_cache.resolve())
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
