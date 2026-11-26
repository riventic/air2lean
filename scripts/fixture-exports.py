#!/usr/bin/env python3
"""Committed AIR exports of the roadmap fixtures: one manifest format, one lock, one tool.

A fixture whose AIR is a patched-compiler export declares how it is made in
`tests/roadmap/<fixture>/exports.json` (hand-written) and pins the result in
`exports.lock.json` (written by `export`, never by hand):

  exports.json       {"exports": [{"out": "air/{version}", "source": "x.zig", "filter": "x.",
                                   "versions": ["0.16.0", ...], "args": ["-OReleaseSafe", ...],
                                   (`filter` may be omitted when SOURCE is an example,
                                   `examples/x/x.zig`: the filter is then the example's, as
                                   scripts/check.sh builds it for each version: `x.` and the lines
                                   of examples/x/filter and examples/x/filter-VERSION)
                                   "cwd": "fixture" | "repo", "command": "build-obj" | "build-exe",
                                   "closure": ["x.*"], "stop": ["os.linux.read"]}]}
                     Each entry is one `zig COMMAND -fno-emit-bin ARGS SOURCE` per version with
                     ZIG_AIR_JSON_FILTER=FILTER, its files written to OUT ({version} substituted;
                     an entry of one version may omit it; the tool owns OUT: nothing else may
                     live there). SOURCE is relative to the fixture and may lie elsewhere in the
                     repository (`../../../examples/x/x.zig`);
                     `cwd` (default "fixture") is where the compiler runs; `command` defaults to
                     build-obj (build-exe exports a whole program, e.g. for its error numbering).
                     `closure`, if given, keeps only the functions that its roots reach through
                     calls and function values (`"func"` references): the filter also matches
                     std instances that only the compiler's panic and debug code reaches, and how
                     many differs by version. A root is a function name, which must be exported,
                     or a name prefix ending in `*`. `stop` (needs `closure`; names and `*`
                     prefixes) cuts the closure: a stopped function is neither kept nor followed
                     (a primitive the model binds, the panic handlers the translator normalizes).
  exports.lock.json  the manifest's hash, the hash of every .zig file of the fixture and of the
                     directory of each SOURCE outside it (an import may change an export), the
                     identity of each version's patched compiler
                     (the digest of exactly what zig-patch/build.sh reads, scripts/cas.py
                     zig_patch_inputs: host-independent, unlike the binary) and the hash of every
                     exported file.

  fixture-exports.py list                         the fixtures with a manifest
  fixture-exports.py check  [FIXTURE...]          no compiler: the lock equals what the manifest,
                                                  sources, zig-patch/ inputs and OUT dirs give now,
                                                  and every file is its version's export of SOURCE
  fixture-exports.py verify [FIXTURE...]          export into a scratch directory and require the
                                                  committed files byte for byte (nothing written)
  fixture-exports.py export [FIXTURE...]          export, replace each OUT, write the lock

FIXTURE is a directory name under tests/roadmap (default: every fixture with a manifest). The
patched compilers come from scripts/cas.py zig-air (the shared cache with AIR2LEAN_CAS_DIR set,
else <checkout>/zig-air-<version>). `check` is the per-PR gate (fixture checks, preflight); a
`check` failure that names the exporter or a source means `export` (scripts/regen.sh --only
exports), and the export diff is reviewed like any change.
"""
import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/roadmap'
sys.path.insert(0, str(ROOT / 'scripts'))
import cas  # noqa: E402

MANIFEST, LOCK = 'exports.json', 'exports.lock.json'
SCHEMA = 1
ENTRY_KEYS = {'out', 'source', 'versions', 'args'}
OPTIONAL_KEYS = {'filter', 'cwd', 'command', 'closure', 'stop'}
# The exporter's `build_mode` for `-O<mode>` (0.17's `std.lang.Optimize` tags, Dialect.lean
# buildModeRenames, or the 0.16.0 spelling).
BUILD_MODES = {'Debug': {'Debug', 'debug'}, 'ReleaseSafe': {'ReleaseSafe', 'safe'},
               'ReleaseFast': {'ReleaseFast', 'fast'}, 'ReleaseSmall': {'ReleaseSmall', 'small'}}


class Error(Exception):
    pass


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def versions():
    return [v['version'] for v in json.loads((ROOT / 'compatibility.json').read_text())['zig']['versions']]


def fixtures(names):
    found = sorted(p.parent.name for p in FIXTURES.glob('*/' + MANIFEST))
    if not names:
        return found
    missing = [n for n in names if n not in found]
    if missing:
        raise Error('no %s in tests/roadmap/%s' % (MANIFEST, ', tests/roadmap/'.join(missing)))
    return names


def example_of(fixture, entry):
    """The example `examples/<x>/<x>.zig` that the entry's source is, else None."""
    source = (FIXTURES / fixture / entry['source']).resolve()
    example = source.stem
    return example if source == (ROOT / 'examples' / example / (example + '.zig')).resolve() else None


def entry_filter(fixture, entry, version):
    """ZIG_AIR_JSON_FILTER of one export: the entry's `filter`, else the example's, as
    scripts/check.sh builds it (`<x>.`, then the lines of examples/<x>/filter and of
    examples/<x>/filter-<version>), so an example's filter files are the one declaration."""
    if 'filter' in entry:
        return entry['filter']
    example = example_of(fixture, entry)
    out = [example + '.']
    for name in ('filter', 'filter-' + version):
        path = ROOT / 'examples' / example / name
        if path.is_file():
            out += [line.strip() for line in path.read_text().splitlines() if line.strip()]
    return ','.join(out)


def manifest(fixture):
    path = FIXTURES / fixture / MANIFEST
    data = json.loads(path.read_text())
    if set(data) != {'exports'} or not isinstance(data['exports'], list) or not data['exports']:
        raise Error('%s: expected {"exports": [...]} with at least one entry' % path)
    supported = versions()
    outs = []
    for i, entry in enumerate(data['exports']):
        where = '%s: exports[%d]' % (path, i)
        if not ENTRY_KEYS <= set(entry) <= ENTRY_KEYS | OPTIONAL_KEYS:
            raise Error('%s: keys must be %s (optional %s)' % (where, sorted(ENTRY_KEYS), sorted(OPTIONAL_KEYS)))
        if entry['out'].startswith('/') or '..' in Path(entry['out']).parts:
            raise Error('%s: out must be a relative path inside the fixture' % where)
        if not entry['versions'] or any(v not in supported for v in entry['versions']):
            raise Error('%s: versions must be supported Zig versions (%s)' % (where, ', '.join(supported)))
        if '{version}' not in entry['out'] and len(entry['versions']) != 1:
            raise Error('%s: out needs {version} unless the entry exports one version' % where)
        if entry.get('cwd', 'fixture') not in ('fixture', 'repo'):
            raise Error('%s: cwd is "fixture" or "repo"' % where)
        if entry.get('command', 'build-obj') not in ('build-obj', 'build-exe'):
            raise Error('%s: command is "build-obj" or "build-exe"' % where)
        for key in ('closure', 'stop'):
            names = entry.get(key, ['-'])
            if not isinstance(names, list) or not names or not all(isinstance(c, str) and c != '*' and c
                                                                   for c in names):
                raise Error('%s: %s is a non-empty list of function names and `*` prefixes' % (where, key))
        if 'stop' in entry and 'closure' not in entry:
            raise Error('%s: stop cuts a closure: give closure too' % where)
        source = (FIXTURES / fixture / entry['source']).resolve()
        if not source.is_file() or FIXTURES.resolve().parents[1] not in source.parents:  # the repository
            raise Error('%s: no source %s in the repository' % (where, entry['source']))
        if 'filter' not in entry and example_of(fixture, entry) is None:
            raise Error('%s: without a filter the source must be examples/<x>/<x>.zig' % where)
        if not all(isinstance(a, str) for a in entry['args']) or '-fno-emit-bin' in entry['args']:
            raise Error('%s: args are strings (build-obj -fno-emit-bin is implied)' % where)
        outs += [entry['out'].format(version=v) for v in entry['versions']]
    for a in outs:
        for b in outs:
            if a != b and (a + '/').startswith(b + '/'):
                raise Error('%s: output %s lies inside output %s' % (path, a, b))
    if len(set(outs)) != len(outs):
        raise Error('%s: two entries write the same output directory' % path)
    return data


def jobs(fixture, data):
    """(entry, version, out) of every export of the manifest."""
    return [(e, v, e['out'].format(version=v)) for e in data['exports'] for v in e['versions']]


def digests(directory):
    """{file name: sha256} of every file under DIRECTORY (none if it is missing)."""
    files = sorted(directory.rglob('*')) if directory.is_dir() else []
    return {p.relative_to(directory).as_posix(): sha256(p) for p in files if p.is_file()}


def outputs(fixture, data):
    """{out: {file name: sha256}} of the committed OUT directories."""
    return {out: digests(FIXTURES / fixture / out) for _, _, out in jobs(fixture, data)}


def sources(fixture, data):
    """{path relative to the fixture: sha256} of the fixture's .zig files outside its OUTs and of
    the .zig files of the directory of each SOURCE that lies outside the fixture."""
    here = FIXTURES / fixture
    owned = [here / out for _, _, out in jobs(fixture, data)]
    found = {p.relative_to(here).as_posix(): sha256(p) for p in sorted(here.rglob('*.zig'))
             if not any(o in p.parents for o in owned)}
    for entry in data['exports']:
        directory = (here / entry['source']).resolve().parent
        if here.resolve() != directory and here.resolve() not in directory.parents:
            found.update({os.path.relpath(p, here.resolve()): sha256(p) for p in sorted(directory.rglob('*.zig'))})
    return dict(sorted(found.items()))


def compiler_identity(version):
    return hashlib.sha256(canonical(cas.zig_patch_inputs(ROOT, version))).hexdigest()


def lock_of(fixture, data, air):
    used = sorted({v for _, v, _ in jobs(fixture, data)})
    return {'schema': SCHEMA,
            'manifest_sha256': sha256(FIXTURES / fixture / MANIFEST),
            'sources_sha256': sources(fixture, data),
            'compilers': {v: compiler_identity(v) for v in used},
            'air_sha256': {'%s/%s' % (out, name): digest for out, files in sorted(air.items())
                           for name, digest in sorted(files.items())}}


def document_problems(fixture, data):
    """Each committed file is its version's export of SOURCE with the manifest's flags."""
    here = FIXTURES / fixture
    problems = []
    for entry, version, out in jobs(fixture, data):
        directory = here / out
        files = sorted(directory.glob('*.json')) if directory.is_dir() else []
        if not files:
            problems.append('%s: no exported file' % out)
        mode = next((a[2:] for a in entry['args'] if a.startswith('-O')), 'Debug')
        # Without either flag the default follows the build mode; it is not checked then.
        tracing = (True if '-ferror-tracing' in entry['args'] else
                   False if '-fno-error-tracing' in entry['args'] else None)
        target = entry['args'][entry['args'].index('-target') + 1] if '-target' in entry['args'] else None
        # Zig's error integer is as wide as the bit length of --error-limit (16 bits by default).
        limit = entry['args'][entry['args'].index('--error-limit') + 1] if '--error-limit' in entry['args'] else None
        bits = int(limit).bit_length() if limit else 16
        stem = Path(entry['source']).stem + '.'
        text = (here / entry['source']).read_text()
        for path in files:
            document = json.loads(path.read_text())
            name = '%s/%s' % (out, path.name)
            if document.get('zig_version') != version:
                problems.append('%s: zig_version %r, expected %s' % (name, document.get('zig_version'), version))
                continue
            profile = document.get('profile') or {}
            if profile.get('build_mode') not in BUILD_MODES.get(mode, {mode}):
                problems.append('%s: build_mode %r, expected -O%s' % (name, profile.get('build_mode'), mode))
            if tracing is not None and profile.get('error_tracing') not in (tracing, None):
                problems.append('%s: error_tracing %r' % (name, profile.get('error_tracing')))
            if target and not profile.get('target_triple', '').startswith(target.split('-')[0] + '-'):
                problems.append('%s: target %r, expected %s' % (name, profile.get('target_triple'), target))
            if profile.get('error_set_bits', bits) != bits:
                problems.append('%s: error_set_bits %r, expected %d' % (name, profile.get('error_set_bits'), bits))
            function = document.get('name', '')
            if function.startswith(stem):
                local = function[len(stem):]
                if '.' not in local and '__' not in local and not re.search(r'\bfn %s\(' % re.escape(local), text):
                    problems.append('%s: %s is not declared in %s' % (name, function, entry['source']))
    return problems


def check(fixture):
    data = manifest(fixture)
    path = FIXTURES / fixture / LOCK
    if not path.is_file():
        return ['no %s: run scripts/fixture-exports.py export %s' % (LOCK, fixture)]
    recorded = json.loads(path.read_text())
    now = lock_of(fixture, data, outputs(fixture, data))
    problems = []
    for key, what in (('manifest_sha256', 'exports.json changed'), ('sources_sha256', 'a source changed'),
                      ('compilers', 'the exporter (zig-patch/) changed')):
        if recorded.get(key) != now[key]:
            problems.append('%s since the export (%s): run scripts/fixture-exports.py export %s'
                            % (what, key, fixture))
    pinned = recorded.get('air_sha256') or {}
    changed = sorted(k for k in set(pinned) | set(now['air_sha256']) if pinned.get(k) != now['air_sha256'].get(k))
    if changed:
        problems.append('the committed AIR differs from the lock: %s' % ', '.join(changed))
    if recorded.get('schema') != SCHEMA:
        problems.append('lock schema %r, expected %d' % (recorded.get('schema'), SCHEMA))
    return problems + document_problems(fixture, data)


def matches(name, patterns):
    """NAME is one of PATTERNS: a function name, or a name prefix ending in `*`."""
    return any(name.startswith(p[:-1]) if p.endswith('*') else name == p for p in patterns)


def keep_closure(directory, roots, stop=()):
    """Delete every function file of DIRECTORY that no function matching ROOTS reaches through
    `"func"` references (calls, function values) without passing a function matching STOP."""
    texts = {p: p.read_text() for p in directory.glob('*.json')}
    by_name = {}
    for path, text in texts.items():
        name = json.loads(text).get('name')
        if name is not None:
            by_name.setdefault(name, []).append(path)
    missing = [r for r in roots if not r.endswith('*') and r not in by_name]
    if missing:
        raise Error('%s: closure root %s was not exported' % (directory.name, ', '.join(missing)))
    work = [p for name, paths in by_name.items() if matches(name, roots) and not matches(name, stop)
            for p in paths]
    keep = set()
    while work:
        path = work.pop()
        if path not in keep:
            keep.add(path)
            for raw in set(re.findall(r'"func":\s*("(?:[^"\\]|\\.)*")', texts[path])):
                ref = json.loads(raw)
                if not matches(ref, stop):
                    work.extend(by_name.get(ref, []))
    for path, text in texts.items():
        if path not in keep and json.loads(text).get('name') is not None:
            path.unlink()


def run_exports(fixture, data, scratch, only=()):
    """Export every job of FIXTURE (of the versions in ONLY, if given) into SCRATCH/<out>;
    returns {out: {file: sha256}}."""
    here = FIXTURES / fixture
    shim = scratch / '.shim'
    shim.mkdir(parents=True, exist_ok=True)
    (shim / 'xcrun').write_text('#!/bin/sh\nexit 1\n')
    (shim / 'xcrun').chmod(0o755)
    compilers = {}
    for entry, version, out in jobs(fixture, data):
        if only and version not in only:
            continue
        if version not in compilers:
            compilers[version] = patched_compiler(version)
        target = scratch / out
        target.mkdir(parents=True)
        cwd = here if entry.get('cwd', 'fixture') == 'fixture' else ROOT
        source = os.path.relpath(here / entry['source'], cwd)
        filter_ = entry_filter(fixture, entry, version)
        env = dict(os.environ, ZIG_AIR_JSON_DIR=str(target), ZIG_AIR_JSON_FILTER=filter_)
        if platform.system() == 'Darwin' and version in cas.DARWIN_NO_XCRUN:
            env['PATH'] = str(shim) + os.pathsep + env.get('PATH', '')  # zig-patch/README.md
        command = ([str(compilers[version]), entry.get('command', 'build-obj'), '-fno-emit-bin']
                   + entry['args'] + [source])
        done = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
        if done.returncode:
            raise Error('%s %s (%s): export failed (exit %d)\n%s' % (fixture, out, version, done.returncode,
                                                                     done.stderr[-4000:]))
        if 'closure' in entry:
            keep_closure(target, entry['closure'], entry.get('stop', ()))
        if not any(target.glob('*.json')):
            raise Error('%s %s: the export wrote no file (filter %r)' % (fixture, out, filter_))
    return {out: digests(scratch / out) for _, version, out in jobs(fixture, data) if not only or version in only}


def patched_compiler(version):
    """bin/zig of the patched compiler of VERSION: AIR2LEAN_ZIG_AIR/zig-air-<version> when that
    directory holds one (CI's compilers, restored by the key of exactly what zig-patch/build.sh
    reads, scripts/ci-cache.py), else scripts/cas.py zig-air."""
    given = os.environ.get('AIR2LEAN_ZIG_AIR')
    if given and (Path(given) / ('zig-air-' + version) / 'bin/zig').is_file():
        return Path(given) / ('zig-air-' + version) / 'bin/zig'
    return cas.zig_air(ROOT, version)


def verify(fixture, only=()):
    data = manifest(fixture)
    with tempfile.TemporaryDirectory(prefix='air2lean-fixture-exports.') as scratch:
        fresh = run_exports(fixture, data, Path(scratch), only)
    committed = outputs(fixture, data)
    problems = []
    if not fresh:
        return ['no export of version %s' % ', '.join(only)]
    for out in fresh:
        for name in sorted(set(fresh[out]) | set(committed[out])):
            if name not in committed[out]:
                problems.append('%s/%s: exported, not committed' % (out, name))
            elif name not in fresh[out]:
                problems.append('%s/%s: committed, not exported' % (out, name))
            elif fresh[out][name] != committed[out][name]:
                problems.append('%s/%s: differs from a fresh export' % (out, name))
    return problems


def export(fixture):
    data = manifest(fixture)
    here = FIXTURES / fixture
    with tempfile.TemporaryDirectory(prefix='air2lean-fixture-exports.') as scratch:
        run_exports(fixture, data, Path(scratch))
        for _, _, out in jobs(fixture, data):
            shutil.rmtree(here / out, ignore_errors=True)
            (here / out).parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(Path(scratch) / out, here / out)
    lock = lock_of(fixture, data, outputs(fixture, data))
    (here / LOCK).write_text(json.dumps(lock, indent=2, sort_keys=True) + '\n')
    return document_problems(fixture, data)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('action', choices=('list', 'check', 'verify', 'export'))
    parser.add_argument('fixtures', nargs='*')
    parser.add_argument('--version', action='append', default=[],
                        help='verify: only the exports of this Zig version (repeatable)')
    args = parser.parse_args()
    if args.version and args.action != 'verify':
        parser.error('--version is for verify only (export rewrites the whole lock)')
    try:
        names = fixtures(args.fixtures)
        if args.action == 'list':
            print('\n'.join(names))
            return 0
        failed = 0
        for name in names:
            problems = (verify(name, args.version) if args.action == 'verify' else
                        {'check': check, 'export': export}[args.action](name))
            for problem in problems:
                print('fixture-exports: %s: %s' % (name, problem), file=sys.stderr)
            failed += bool(problems)
            if not problems:
                print('fixture-exports: %s: %s ok' % (name, args.action))
        return 1 if failed else 0
    except (Error, cas.CasError, json.JSONDecodeError) as error:
        print('fixture-exports: %s' % error, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
