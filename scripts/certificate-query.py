#!/usr/bin/env python3
"""Prepare the exact rendered Gen and read compiler facts for certificate construction.

This is the existing certificate workflow's automatic preparation, not an assurance
admission or a generator of proof rules. The final certificate is checked by Lean.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

import assumptions
from theorem_universe import compile_unit, compiled_output, input_identity

ROOT = Path(__file__).resolve().parents[1]
MARKER = 'AIR2LEAN_FIXPOINT_JSON:'
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*')


def plan(request: dict) -> tuple[str, list[dict]]:
    """The caller supplies the renderer's actual module plan, never a call graph."""
    if not isinstance(request, dict) or set(request) != {'module', 'modules', 'translator', 'runtime'}:
        raise ValueError('expected the rendered module and its exact module plan')
    target, modules = request['module'], request['modules']
    if not isinstance(target, str) or MODULE.fullmatch(target) is None:
        raise ValueError('invalid generated certificate module')
    if not isinstance(modules, list) or not modules:
        raise ValueError('empty rendered module plan')
    seen = set()
    for item in modules:
        if not isinstance(item, dict) or set(item) != {'name', 'source', 'imports'}:
            raise ValueError('invalid rendered module record')
        name = item['name']
        if not isinstance(name, str) or MODULE.fullmatch(name) is None or name in seen:
            raise ValueError('invalid or duplicate rendered module name')
        if not isinstance(item['source'], str) or not isinstance(item['imports'], list):
            raise ValueError(f'invalid rendered module source/imports: {name}')
        if any(not isinstance(m, str) or MODULE.fullmatch(m) is None for m in item['imports']):
            raise ValueError(f'invalid rendered import: {name}')
        seen.add(name)
    if target not in seen:
        raise ValueError('requested certificate module is not a rendered output')
    ready = set()
    for item in modules:
        if any(m in seen and m not in ready for m in item['imports']):
            raise ValueError(f'rendered modules are not in compiler dependency order: {item["name"]}')
        ready.add(item['name'])
    return target, modules


def revision_inputs(request: dict) -> dict:
    """Bind the workspace selected for preparation to the invoking binary's sources."""
    selected = {}
    for label in ('translator', 'runtime'):
        revision = request[label]
        if (not isinstance(revision, dict) or set(revision) != {'lean', 'revision', 'modules'}
                or not isinstance(revision['lean'], str) or not isinstance(revision['modules'], list)):
            raise ValueError(f'invalid {label} source revision')
        listing = revision['lean'] + '\n'
        names = []
        seen = set()
        for row in revision['modules']:
            if (not isinstance(row, list) or len(row) != 2 or not all(isinstance(v, str) for v in row)
                    or MODULE.fullmatch(row[0]) is None or re.fullmatch(r'[0-9a-f]{64}', row[1]) is None):
                raise ValueError(f'invalid {label} source module')
            name, expected = row
            if name in seen:
                raise ValueError(f'duplicate {label} source module')
            seen.add(name)
            names.append(name)
            path = ROOT / (name.replace('.', '/') + '.lean')
            actual = input_identity(path)
            if actual['sha256'] != expected:
                raise ValueError(f'certificate workspace differs from the invoking binary: {name}')
            selected[name] = actual
            listing += f'{name} {expected}\n'
        if not names or names != sorted(names) or hashlib.sha256(listing.encode()).hexdigest() != revision['revision']:
            raise ValueError(f'invalid {label} revision digest')
    return selected


def query(request: dict) -> dict:
    target, modules = plan(request)
    invoked_sources = revision_inputs(request)
    names = {item['name'] for item in modules}
    external = sorted({m for item in modules for m in item['imports'] if m not in names})
    run = lambda command: assumptions.run(command, root=ROOT)
    # These are the actual rendered imports, not a whole-tree build. Prepare before
    # freezing the extractor/lookup inputs, as in the existing compiled-unit workflow.
    if external:
        run(['lake', '--rehash', 'build', *external])
    with assumptions.prepared_tool(ROOT, run) as tool, tempfile.TemporaryDirectory(
            prefix='air2lean-certificate-') as directory:
        base = Path(directory)
        source_root, library = base / 'src', base / 'lib'
        source_root.mkdir()
        library.mkdir()
        sources, outputs = {}, {}
        for item in modules:
            relative = Path(*item['name'].split('.'))
            source = (source_root / relative).with_suffix('.lean')
            output = (library / relative).with_suffix('.olean')
            source.parent.mkdir(parents=True, exist_ok=True)
            output.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(item['source'].encode('utf-8'))
            sources[item['name']] = source
            outputs[item['name']] = output
        source_binding = {name: input_identity(path) for name, path in sources.items()}
        config = {name: input_identity(ROOT / name) for name in
                  ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')}
        tools = {str(path): input_identity(path) for path in
                 (Path(__file__), Path(assumptions.__file__), ROOT / 'scripts/theorem_universe.py')}
        base_path = run(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
        if not base_path or len(base_path.splitlines()) != 1:
            raise ValueError('cannot resolve the existing Lean lookup path')
        lean_path = os.pathsep.join([str(library), base_path])
        paths = [Path(p) if Path(p).is_absolute() else ROOT / p for p in lean_path.split(os.pathsep)]
        base_paths = paths[1:]
        # A top-level private namespace can hide an imported library even when it
        # does not contain that particular file. Preserve the existing fail-closed
        # resolver; never fall back to an ambient copy after a private lookup fails.
        for name in [*external, 'tools.Assurance']:
            expected = assumptions.locate(name, base_paths).resolve(strict=True)
            if assumptions.locate(name, paths).resolve(strict=True) != expected:
                raise ValueError(f'private generated module shadows an imported library: {name}')
        mutable = {output.with_name(output.name[:-len('.olean')] + suffix)
                   for output in outputs.values() for suffix in assumptions.COMPILED_SUFFIXES}
        before = assumptions.lean_path_binding(ROOT, lean_path, mutable_outputs=mutable)
        artifacts = {}

        def verify_inputs():
            if {name: input_identity(path) for name, path in sources.items()} != source_binding:
                raise ValueError('rendered Gen source changed during certificate preparation')
            if {name: input_identity(ROOT / name) for name in config} != config:
                raise ValueError('certificate compiler configuration changed')
            if {name: input_identity(Path(name)) for name in tools} != tools:
                raise ValueError('certificate preparation tool inputs changed')
            if {name: input_identity(ROOT / (name.replace('.', '/') + '.lean'))
                    for name in invoked_sources} != invoked_sources:
                raise ValueError('invoking binary source inputs changed during preparation')
            if {name: compiled_output(outputs[name]) for name in artifacts} != artifacts:
                raise ValueError('fresh generated compiler output changed after compilation')

        for index, item in enumerate(modules):
            name = item['name']
            verify_inputs()
            log = base / f'compile-{index}.log'
            failure = compile_unit(str(sources[name]), str(source_root), outputs[name], [], log,
                                   resolved_path=lean_path)
            if failure:
                raise ValueError(f'{failure}\n{log.read_text()}')
            if assumptions.locate(name, paths).resolve(strict=True) != outputs[name].resolve(strict=True):
                raise ValueError(f'fresh generated compiler output is shadowed: {name}')
            artifacts[name] = compiled_output(outputs[name])
        verify_inputs()
        selected = [item['name'] for item in modules]
        quoted = '#[' + ', '.join(json.dumps(name) for name in selected) + ']'
        driver = base / 'Query.lean'
        driver.write_text('import tools.Assurance\nimport ' + target + '\n'
                          'run_meta do\n'
                          '  let result ← Air2Lean.Assurance.partialFixpointData ' + quoted + '\n'
                          '  liftIO <| IO.println (' + json.dumps(MARKER) + ' ++ result.compress)\n')
        response = run(assumptions.lean_command([str(driver)], lean_path))
        verify_inputs()
        if assumptions.lean_path_binding(ROOT, lean_path, mutable_outputs=mutable) != before:
            raise ValueError('prepared compiler lookup inputs changed during compile/query')
        assumptions.verify_extractor_inputs(tool, ROOT, 'certificate compile/query')
        payloads = [line[len(MARKER):] for line in response.splitlines() if line.startswith(MARKER)]
        if len(payloads) != 1:
            raise ValueError('compiler query did not return exactly one factual payload')
        result = json.loads(payloads[0])
        if not isinstance(result, dict) or not isinstance(result.get('fixpoint_groups'), list):
            raise ValueError('compiler query returned an invalid factual payload')
        # Inspectable construction binding only: this is never assurance evidence.
        result['preparation'] = {
            'module': target,
            'sources': {name: row['sha256'] for name, row in source_binding.items()},
            'artifacts': artifacts,
            'toolchain': tool['toolchain_runtime_sha256'],
            'lookup_sha256': before['sha256'],
        }
        return result


def main() -> int:
    try:
        result = query(json.load(sys.stdin))
        print(json.dumps(result, separators=(',', ':')))
        return 0
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        print(f'certificate preparation failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
