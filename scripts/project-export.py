#!/usr/bin/env python3
"""Original-source export (I01): select roots, export their AIR closure, translate.

`project.py export MANIFEST` reads the manifest's optional ``export`` section (Zig
version, verbatim compiler flags, modules with optional SHA-256 pins, a generated
``build_options`` module, optional root references) and runs the patched AIR-only
compiler with ``ZIG_AIR_JSON_FILTER`` covering exactly the requested root functions.
`dependency-closure.py` then classifies each root's closure; every missing function's
filter prefix is added and the source is exported again, until the closure has no
missing function (a fixed point), the compiler writes no new AIR for a covered name
(stalled), or the iteration bound is reached. Only then is each root translated.

A requested root without AIR is reported (with a source hint: inline, generic or
unreferenced) and fails the command: an empty or partial export is never published.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 1
KIND = 'air2lean-project-export'
MAX_ITERATIONS = 16
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\Z')
REFERENCE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+\Z')
OPTION_TYPE = re.compile(r'(?:bool|[iu](?:[1-9][0-9]{0,4})|usize|isize|\[\]const u8)\Z')
EXPORT_WARNING = re.compile(rb'air2lean: (?:cannot open|name too long for a file|no JSON for|incomplete JSON for)')
SHIM = 'air2lean_roots'


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


closure = _load('dependency_closure', Path(__file__).resolve().with_name('dependency-closure.py'))


class Invalid(ValueError):
    pass


def _strings(value, what):
    if not isinstance(value, list) or not all(isinstance(v, str) and v and '\0' not in v for v in value):
        raise Invalid(f'export.{what} must be a list of nonempty strings')
    if len(set(value)) != len(value):
        raise Invalid(f'export.{what} has duplicate entries')


def check_flag(flag):
    """Flags pass through verbatim; reject those that would change what is exported or where."""
    if flag.startswith('@'):
        raise Invalid(f'export flag {flag!r}: response files can hide emission overrides')
    if flag.startswith('--zig-lib-dir'):
        raise Invalid(f'export flag {flag!r}: the std models are audited against the compiler\'s own lib directory')
    if flag.startswith(('-femit-', '-fno-emit-bin', '-M', '--dep', '-o')) or flag in ('--', '--mod'):
        raise Invalid(f'export flag {flag!r}: emission and modules are set by the export section')
    if flag.endswith(('.zig', '.c', '.o', '.a')):
        raise Invalid(f'export flag {flag!r}: sources must be declared as modules')


def option_literal(option_type, value):
    if option_type == 'bool':
        if type(value) is not bool:
            raise Invalid('bool option needs true or false')
        return 'true' if value else 'false'
    if option_type == '[]const u8':
        if not isinstance(value, str) or not all(32 <= ord(c) < 127 for c in value):
            raise Invalid('string option needs printable ASCII')
        return '"' + value.replace('\\', '\\\\').replace('"', '\\"') + '"'
    if type(value) is not int:
        raise Invalid(f'{option_type} option needs an integer')
    return str(value)


def validate(spec):
    """Validate a manifest ``export`` section (called by project.load_manifest)."""
    allowed = {'zig_version', 'flags', 'modules', 'options', 'references', 'filter', 'max_iterations',
               'timeout_seconds'}
    if not isinstance(spec, dict) or set(spec) - allowed or not {'zig_version', 'flags', 'modules'} <= set(spec):
        raise Invalid(f'export must be an object with zig_version, flags, modules and optional {sorted(allowed)}')
    if spec['zig_version'] not in closure.VERSIONS:
        raise Invalid(f'export.zig_version must be one of {", ".join(closure.VERSIONS)}')
    _strings(spec['flags'], 'flags')
    for flag in spec['flags']:
        check_flag(flag)
    modules = spec['modules']
    if not isinstance(modules, list) or not modules:
        raise Invalid('export.modules must be a nonempty list; the first is the main module')
    names = set()
    for module in modules:
        if not isinstance(module, dict) or set(module) - {'name', 'path', 'env', 'deps', 'sha256'} \
                or not {'name', 'path'} <= set(module):
            raise Invalid('export module needs name and path, optional env, deps and sha256')
        if not isinstance(module['name'], str) or not NAME.match(module['name']) or module['name'] in names \
                or module['name'] == SHIM:
            raise Invalid(f'invalid or duplicate export module name {module.get("name")!r}')
        names.add(module['name'])
        if not isinstance(module['path'], str) or not module['path'].endswith('.zig') or '\0' in module['path']:
            raise Invalid(f'export module {module["name"]}: path must name a .zig file')
        if 'env' in module and (not isinstance(module['env'], str) or not NAME.match(module['env'])):
            raise Invalid(f'export module {module["name"]}: env must be an environment variable name')
        if 'sha256' in module and not (isinstance(module['sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', module['sha256'])):
            raise Invalid(f'export module {module["name"]}: sha256 must be 64 lowercase hex digits')
        _strings(module.get('deps', []), 'modules.deps')
    options = spec.get('options')
    if options is not None:
        if not isinstance(options, dict) or set(options) != {'module', 'values'} or not isinstance(options['values'], dict):
            raise Invalid('export.options must be {"module": NAME, "values": {NAME: {"type", "value"}}}')
        if not isinstance(options['module'], str) or not NAME.match(options['module']) or options['module'] in names:
            raise Invalid('export.options.module must be a fresh module name')
        names.add(options['module'])
        for key, entry in options['values'].items():
            if not NAME.match(key) or not isinstance(entry, dict) or set(entry) != {'type', 'value'} \
                    or not isinstance(entry['type'], str) or not OPTION_TYPE.match(entry['type']):
                raise Invalid(f'export option {key!r} needs {{"type": bool|iN|uN|usize|isize|[]const u8, "value"}}')
            option_literal(entry['type'], entry['value'])
    for module in modules:
        unknown = set(module.get('deps', [])) - names
        if unknown:
            raise Invalid(f'export module {module["name"]} depends on undeclared modules {sorted(unknown)}')
    references = spec.get('references', [])
    _strings(references, 'references')
    for ref in references:
        if not REFERENCE.match(ref) or ref.split('.')[0] not in names:
            raise Invalid(f'export reference {ref!r} must be MODULE.decl[.decl...] of a declared module')
    _strings(spec.get('filter', []), 'filter')
    for key, top in (('max_iterations', MAX_ITERATIONS), ('timeout_seconds', 86400)):
        if key in spec and (type(spec[key]) is not int or not 1 <= spec[key] <= top):
            raise Invalid(f'export.{key} must be an integer from 1 through {top}')


def resolve_modules(spec, base, overrides):
    """Module name -> absolute path; precedence: --module, then the module's env variable, then path."""
    unknown = set(overrides) - {m['name'] for m in spec['modules']}
    if unknown:
        raise Invalid(f'--module names undeclared modules {sorted(unknown)}')
    paths = {}
    for module in spec['modules']:
        raw = overrides.get(module['name']) or (os.environ.get(module['env']) if 'env' in module else None) \
            or module['path']
        path = Path(raw) if Path(raw).is_absolute() else base / raw
        if not path.is_file():
            raise Invalid(f'module {module["name"]} source missing: {path}')
        paths[module['name']] = path.resolve()
    return paths


def source_hashes(spec, paths):
    hashes = {}
    for module in spec['modules']:
        actual = hashlib.sha256(paths[module['name']].read_bytes()).hexdigest()
        if 'sha256' in module and actual != module['sha256']:
            raise Invalid(f'module {module["name"]} source {paths[module["name"]]} has sha256 {actual}, '
                          f'manifest pins {module["sha256"]}')
        hashes[module['name']] = actual
    return hashes


def apply_defines(spec, defines):
    """`-D NAME=VALUE` overrides of declared options, parsed by the declared type."""
    values = {k: dict(v) for k, v in (spec.get('options') or {}).get('values', {}).items()}
    for define in defines:
        key, sep, text = define.partition('=')
        if key not in values:
            raise Invalid(f'-D {key}: not a declared export option')
        kind = values[key]['type']
        if kind == 'bool':
            if text not in ('true', 'false', ''):
                raise Invalid(f'-D {key}: expected true or false')
            value = text != 'false'
        elif kind == '[]const u8':
            if not sep:
                raise Invalid(f'-D {key}: expected NAME=VALUE')
            value = text
        else:
            try:
                value = int(text, 0)
            except ValueError:
                raise Invalid(f'-D {key}: expected an integer') from None
        option_literal(kind, value)
        values[key]['value'] = value
    return values


def write_generated(spec, values, work):
    """The build_options module and, with references, the reference root; both contain no code."""
    generated = {}
    if spec.get('options'):
        lines = ['//! Generated by project.py export from the manifest options (build.zig addOptions).']
        lines += [f'pub const {k}: {v["type"]} = {option_literal(v["type"], v["value"])};' for k, v in sorted(values.items())]
        path = work / f'{spec["options"]["module"]}.zig'
        path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
        generated[spec['options']['module']] = path
    if spec.get('references'):
        lines = ['//! Generated by project.py export: references the selected roots; no implementation.', 'comptime {']
        lines += [f'    _ = &@import("{ref.split(".")[0]}").{ref.split(".", 1)[1]};' for ref in spec['references']]
        path = work / f'{SHIM}.zig'
        path.write_text('\n'.join(lines + ['}']) + '\n', encoding='utf-8')
        generated[SHIM] = path
    return generated


def compiler_argv(zig, spec, paths, generated):
    """`build-obj -fno-emit-bin FLAGS...` then the main module and every other module with its deps.
    Flags are copied verbatim and in order; the main module is the reference root when present."""
    modules = [dict(m) for m in spec['modules']]
    if SHIM in generated:
        modules.insert(0, {'name': SHIM, 'deps': sorted({r.split('.')[0] for r in spec['references']})})
    if spec.get('options'):
        modules.append({'name': spec['options']['module'], 'deps': []})
    argv = [str(zig), 'build-obj', '-fno-emit-bin', *spec['flags']]
    for module in modules:
        for dep in module.get('deps', []):
            argv += ['--dep', dep]
        argv.append(f'-M{module["name"]}={generated.get(module["name"]) or paths[module["name"]]}')
    return argv


def source_hints(fqn, paths):
    """Declarations of the root's last name component in the module sources (an explanation, not a proof)."""
    name = fqn.rsplit('.', 1)[-1]
    pattern = re.compile(r'^[ \t]*(?:pub\s+)?(?:export\s+)?(inline\s+)?fn\s+' + re.escape(name) + r'\s*\(([^)]*)\)', re.M)
    hints = []
    for module, path in sorted(paths.items()):
        text = path.read_text(encoding='utf-8', errors='replace')
        for match in pattern.finditer(text):
            hints.append({'module': module, 'line': text.count('\n', 0, match.start()) + 1,
                          'inline': bool(match.group(1)),
                          'generic': bool(re.search(r'\banytype\b|\bcomptime\b', match.group(2)))})
    return hints


def unexported_root(fqn, functions, paths):
    instances = sorted(n for n in functions if n.startswith(fqn + '__anon_'))
    hints = source_hints(fqn, paths)
    if instances:
        reason, why = 'generic_instances_only', 'only generic instances were exported; select a monomorphic wrapper'
    elif any(h['inline'] for h in hints):
        reason, why = 'inline_only', 'an inline fn has no AIR of its own; select the functions it is inlined into'
    elif any(h['generic'] for h in hints):
        reason, why = 'comptime_only_generic', 'a generic fn has AIR only per instantiation; select a monomorphic wrapper'
    elif not hints:
        reason, why = 'not_found', 'no declaration with this name in the module sources; check the fully qualified name'
    else:
        reason, why = 'unreferenced', 'never analyzed: reference it (export.references or comptime { _ = &f; })'
    return {'function': fqn, 'reason': reason, 'message': why, 'instances': instances, 'source_hints': hints}


def load_air(project, directory, limits, zig_version, profile):
    """Every exported file: name -> (path, scan). Version and profile must match the manifest."""
    functions, files = {}, {}
    for path in sorted(directory.glob('*.json')):
        air = project.bounded_json(project.read_bounded(path, limits['max_file_bytes']), limits)
        info = closure.scan(air)
        if info['name'] in functions:
            raise Invalid(f'compiler exported {info["name"]} twice')
        if air.get('zig_version') != zig_version:
            raise Invalid(f'{info["name"]}: AIR zig_version {air.get("zig_version")} differs from export.zig_version')
        if profile and profile.get('name') == 'abi64-le-v1' and air.get('profile') != profile:
            raise Invalid(f'{info["name"]}: exported AIR profile differs from the manifest profile '
                          '(the project flags did not produce the declared target/mode)')
        functions[info['name']] = info
        files[info['name']] = path
    return functions, files


def run_export(project, manifest_path, zig, translator, out, module_overrides=(), defines=(), models=None,
               replace=False):
    manifest, raw, limits = project.load_manifest(manifest_path)
    spec = manifest.get('export')
    if spec is None:
        raise Invalid('manifest has no export section')
    base = manifest_path.parent
    profile = project.bounded_json(project.read_bounded(project.path_under(base, manifest['profile']),
                                                        limits['max_file_bytes']), limits)
    project.validate_profile(profile)
    overrides = {}
    for item in module_overrides:
        name, sep, value = item.partition('=')
        if not sep or not value:
            raise Invalid(f'--module {item!r}: expected NAME=PATH')
        overrides[name] = str(Path(value).resolve())
    paths = resolve_modules(spec, base, overrides)
    hashes = source_hashes(spec, paths)
    values = apply_defines(spec, defines)
    zig = Path(zig).resolve(strict=True)
    translator = Path(translator).resolve(strict=True)
    models = closure.std_models() if models is None else models
    timeout = spec.get('timeout_seconds', 3600)
    run_limits = dict(limits, timeout_seconds=timeout)
    version = project._run_bounded([str(zig), 'version'], base, dict(limits, timeout_seconds=60), merged=False)
    found = version['stdout'].decode('utf-8', errors='replace').strip()
    if version['failure'] or version['returncode'] != 0 or found != spec['zig_version']:
        raise Invalid(f'patched compiler {zig} reports version {found!r}, export.zig_version is {spec["zig_version"]}')
    out = out.resolve()
    if out.exists() and (not out.is_dir() or any(out.iterdir())) and not (replace and previous_export(out)):
        raise Invalid('--out must be a fresh or empty directory (--replace: or a previous export artifact)')
    out.parent.mkdir(parents=True, exist_ok=True)
    roots = [r['function'] for r in manifest['roots']]
    if any(r['id'] == 'air' for r in manifest['roots']):
        raise Invalid('root id "air" collides with the artifact\'s air/ directory')
    report = {'schema': SCHEMA, 'kind': KIND, 'manifest_sha256': project.digest(raw), 'status': 'failed',
              'zig': {'path': str(zig), 'version': found}, 'translator': {'path': str(translator)},
              'flags': list(spec['flags']), 'options': {k: v['value'] for k, v in sorted(values.items())},
              'modules': [{'name': m['name'], 'path': str(paths[m['name']]), 'sha256': hashes[m['name']],
                           'pinned': 'sha256' in m} for m in spec['modules']],
              'requested_roots': roots, 'iterations': [], 'unexported_roots': [], 'roots': [],
              'scope': 'the closure covers exported AIR; calls inside missing functions are unknown until exported. '
                       'Translation trusts Zig semantic analysis, the AIR export patch and the translator.'}
    with tempfile.TemporaryDirectory(prefix='.air2lean-export-', dir=out.parent) as temp:
        stage = Path(temp) / 'artifact'
        work = Path(temp) / 'work'
        stage.mkdir()
        work.mkdir()
        generated = write_generated(spec, values, work)
        prefixes, _ = closure.filter_prefixes([], roots + list(spec.get('filter', [])), {})
        functions = files = None
        bound = spec.get('max_iterations', 8)
        for iteration in range(1, bound + 1):
            air_dir = work / f'air-{iteration}'
            air_dir.mkdir()
            argv = compiler_argv(zig, spec, paths, generated)
            # ZIG_LIB_DIR would swap the std library that the std models are audited against.
            env = {k: v for k, v in os.environ.items() if not k.startswith('ZIG_AIR_JSON_') and k != 'ZIG_LIB_DIR'}
            env.update(ZIG_AIR_JSON_DIR=str(air_dir), ZIG_AIR_JSON_FILTER=','.join(prefixes))
            result = project._run_bounded(argv, base, run_limits, merged=False, env=env)
            shown = [a.replace(str(work), '${EXPORT_WORK}') for a in argv]
            record = {'iteration': iteration, 'filter': list(prefixes), 'argv': shown,
                      'returncode': result['returncode'], 'failure': result['failure']}
            report['iterations'].append(record)
            stderr = result['stdout'] + result['stderr']
            if result['failure'] or result['returncode'] != 0 or EXPORT_WARNING.search(stderr):
                record['stderr'] = stderr.decode('utf-8', errors='replace')[-8192:]
                report['reason'] = 'AIR export failed' if not EXPORT_WARNING.search(stderr) \
                    else 'AIR export incomplete (exporter warning)'
                return finish(report, None)
            try:
                source_hashes(spec, paths)  # the sources must not change while the compiler reads them
                functions, files = load_air(project, air_dir, limits, spec['zig_version'], profile)
            except (OSError, ValueError) as error:
                report['reason'] = f'exported AIR rejected: {error}'
                return finish(report, None)
            record['exported'] = sorted(functions)
            missing, results = set(), {}
            for fqn in roots:
                if fqn not in functions:
                    continue
                results[fqn] = closure.report(closure.Closure(functions, spec['zig_version'], models).run([fqn]),
                                              [fqn], [fqn])
                missing.update(m['fqn'] for m in results[fqn]['missing'])
            record['missing'] = sorted(missing)
            new = sorted({closure.filter_prefix(name) for name in missing
                          if not closure.covered(name, prefixes)})
            record['added_prefixes'] = new
            if not missing:
                record['outcome'] = 'fixed_point'
                break
            if not new:
                record['outcome'] = 'stalled'
                report['reason'] = ('the filter covers missing functions but the compiler wrote no AIR for them '
                                    '(inlined into an unexported caller, comptime-only, or a std model collision)')
                break
            prefixes, _ = closure.filter_prefixes([], prefixes + new, {})
            record['outcome'] = 're-export'
        else:
            report['reason'] = f'closure not closed after {bound} export iterations'
        report['filter'] = {'value': ','.join(prefixes),
                            'std_model_collisions': closure.filter_prefixes([], prefixes, models)[1]}
        report['unexported_roots'] = [unexported_root(fqn, functions, paths) for fqn in roots if fqn not in functions]
        report['exported_outside_closure'] = sorted(set(functions) - {
            n['name'] for r in results.values() for n in r['functions']})
        failed = bool(report['unexported_roots']) or 'reason' in report
        if report['unexported_roots']:
            report['reason'] = 'requested roots have no AIR: ' + ', '.join(r['function'] for r in report['unexported_roots'])
        for root in manifest['roots']:
            result = results.get(root['function'])
            entry = {'id': root['id'], 'function': root['function']}
            if result is not None:
                entry['closure'] = {k: result[k] for k in ('status', 'counts', 'missing', 'unresolvable',
                                                           'model_boundaries', 'indirect_calls')}
                entry['air'] = sorted(n['name'] for n in result['functions'] if n['class'] == 'exported')
            report['roots'].append(entry)
        if failed:
            return finish(report, None)
        shutil.copytree(work / f'air-{len(report["iterations"])}', stage / 'air')
        for root, entry in zip(manifest['roots'], report['roots']):
            entry['translated'] = translate_root(project, manifest, root, entry, files, translator, stage,
                                                 profile, run_limits)
        if any(e['translated']['status'] != 'passed' for e in report['roots']):
            report['reason'] = 'translation failed'
            return finish(report, None)
        report['status'] = 'translated'
        report['closure_status'] = 'closed' if all(e['closure']['status'] == 'closed' for e in report['roots']) \
            else 'boundaries'
        return finish(report, (stage, out))


def translate_root(project, manifest, root, entry, files, translator, stage, profile, limits):
    rootdir = stage / root['id']
    air_dir = rootdir / 'air'
    air_dir.mkdir(parents=True)
    for name in entry['air']:
        shutil.copyfile(files[name], air_dir / files[name].name)
    output = rootdir / 'Gen.lean'
    argv = [str(translator), str(air_dir), '-o', str(output), '--namespace', root['namespace'],
            '--prefix', root['prefix'], '--float-semantics', manifest['float_semantics'],
            '--spawn-policy', project.spawn_policy(manifest), '--profile', profile['name']]
    result = project.run_translation(argv, rootdir, limits)
    shutil.rmtree(air_dir)
    result['argv'] = [a.replace(str(stage), '${EXPORT_OUT}') for a in argv]
    if result['status'] == 'passed':
        data = output.read_bytes() if output.is_file() else b''
        if not data:
            return dict(result, status='failed', code='TRANSLATION_ARTIFACT', message='translator produced no output')
        result['generated'] = {'path': f'{root["id"]}/Gen.lean', 'sha256': project.digest(data), 'bytes': len(data)}
    return result


def previous_export(out):
    try:
        return json.loads((out / 'export.json').read_text(encoding='utf-8')).get('kind') == KIND
    except (OSError, ValueError, AttributeError):
        return False


def finish(report, publish):
    """Write export.json; publish the staged artifact (rename) only when every root translated."""
    encoded = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
    if publish is not None:
        stage, out = publish
        (stage / 'export.json').write_bytes(encoded)
        if out.exists() and not any(out.iterdir()):
            out.rmdir()
        elif out.exists():
            if not previous_export(out):
                raise Invalid(f'{out} changed during the export; refusing replacement')
            os.rename(out, stage.parent / 'previous')  # removed with the staging directory
        os.rename(stage, out)
    return report, encoded


def main(project, argv=None):
    parser = argparse.ArgumentParser(prog='project.py export', description=__doc__.split('\n')[0])
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--out', type=Path, required=True, help='fresh or empty artifact directory')
    parser.add_argument('--replace', action='store_true',
                        help='replace a previous export artifact in --out after a successful export (zig build reruns)')
    parser.add_argument('--translator', type=Path, required=True)
    parser.add_argument('--zig-air', type=Path, help='patched compiler (default AIR2LEAN_ZIG_AIR, '
                        'then zig-air-<export.zig_version>/bin/zig in this repository)')
    parser.add_argument('--module', action='append', default=[], metavar='NAME=PATH',
                        help='override a module source (pins still apply)')
    parser.add_argument('-D', dest='defines', action='append', default=[], metavar='NAME=VALUE',
                        help='override a declared export option')
    parser.add_argument('--report', type=Path, help='also write the export report here (also on failure)')
    parser.add_argument('--format', choices=('json', 'text'), default='json')
    args = parser.parse_args(argv)
    manifest_path = args.manifest.resolve()
    zig = args.zig_air or os.environ.get('AIR2LEAN_ZIG_AIR')
    if zig is None:
        spec = project.load_manifest(manifest_path)[0].get('export') or {}
        zig = ROOT / f'zig-air-{spec.get("zig_version", "0.16.0")}' / 'bin' / 'zig'
    report, encoded = run_export(project, manifest_path, zig, args.translator, args.out, args.module, args.defines,
                                 replace=args.replace)
    if args.report:
        args.report.write_bytes(encoded)
    print(text(report) if args.format == 'text' else encoded.decode(), end='')
    return 0 if report['status'] == 'translated' else 1


def text(report):
    lines = []
    for it in report['iterations']:
        lines.append(f"export {it['iteration']}: filter {','.join(it['filter'])} -> {len(it.get('exported', []))} "
                     f"functions, missing {len(it.get('missing', []))}"
                     + (f", adding {','.join(it['added_prefixes'])}" if it.get('added_prefixes') else '')
                     + (f" ({it['outcome']})" if 'outcome' in it else ''))
    for root in report['unexported_roots']:
        lines.append(f"root {root['function']} NOT EXPORTED ({root['reason']}): {root['message']}")
    for root in report['roots']:
        if 'closure' in root:
            c = root['closure']
            lines.append(f"root {root['id']} {root['function']}: closure {c['status']} "
                         + ' '.join(f'{k}={v}' for k, v in c['counts'].items()))
            for b in c['unresolvable']:
                lines.append(f"  boundary {b['kind']} {b['target']} at {b['function']}: {b['reason']}")
        if 'translated' in root:
            lines.append(f"  translated: {root['translated']['status']}"
                         + (f" -> {root['translated']['generated']['path']}" if 'generated' in root['translated'] else ''))
    lines.append(f"status: {report['status']}" + (f" ({report['reason']})" if report.get('reason') else ''))
    return '\n'.join(lines) + '\n'
