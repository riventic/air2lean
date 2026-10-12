#!/usr/bin/env python3
"""Exporter equivalence: re-run every recorded AIR export and compare the bytes.

A recorded export is a committed AIR directory and the patched-compiler command that made it:
the goldens (tests/golden; commands derived from examples/ exactly as scripts/check.sh derives
them) and the fixtures listed in tests/roadmap/exporter-equivalence/exports.toml. For each one and
each requested Zig version this script

  1. exports with the current patched compiler (scripts/zig-air.sh <version>, or --zig),
  2. exports with an alternative exporter command (--alt), if given, and requires the two output
     directories to be identical, file for file and byte for byte,
  3. compares the current export with the committed directory: byte for byte ("exact"), as a
     superset of the committed selection ("subset"), or, for the goldens, after the golden
     normalization of scripts/normalize-air.py ("golden").

The alternative command is a drop-in replacement for the patched `zig`: it is run with the same
arguments and the same ZIG_AIR_JSON_DIR/ZIG_AIR_JSON_FILTER environment and must write the same
files. `{zig}` in it is replaced by the current compiler's path and `{version}` by the Zig
version; `--alt self` runs the current compiler a second time (an exporter determinism check).
This is the gate for moving the JSON writer out of the compiler (docs/exporter-split.md): a
renderer is accepted when `--alt '<capture compiler + renderer>'` is identical on every export.

  scripts/exporter-equivalence.py list [--version V ...]
  scripts/exporter-equivalence.py run [--version V ...] [--only REGEX] [--alt CMD] [--zig V=PATH]
                                      [--jobs N] [--report FILE] [--keep DIR] [--require-committed]

Exit status of `run`: 1 when an export fails or the alternative differs from the current export,
or (with --require-committed) when a current export differs from its committed directory; else 0.
"""

import argparse
import concurrent.futures
import dataclasses
import json
import os
import platform
import re
import runpy
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = Path('tests/roadmap/exporter-equivalence/exports.toml')
VERSIONS = ('0.14.1', '0.15.2', '0.16.0', '0.17.0')


class Failure(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Export:
    """One recorded export of one Zig version."""
    id: str
    version: str
    source: str            # repository-relative root source
    args: tuple            # between `build-obj -fno-emit-bin` and the source
    filter: str            # ZIG_AIR_JSON_FILTER; empty: every function
    committed: tuple       # committed directories, later ones overlaying earlier ones (goldens)
    compare: str           # exact | subset | golden

    def argv(self, compiler, cache_dir):
        return [*compiler, 'build-obj', '-fno-emit-bin', *self.args, self.source, '--cache-dir', str(cache_dir)]

    def command(self):
        """The command as a shell line, for listings and reports."""
        env = 'ZIG_AIR_JSON_DIR=<out>' + (' ZIG_AIR_JSON_FILTER=' + shlex.quote(self.filter) if self.filter else '')
        return '%s <zig> build-obj -fno-emit-bin %s' % (env, shlex.join([*self.args, self.source]))


# ------------------------------------------------------------------ recorded exports

def read_filter_file(root, path):
    lines = [line.strip() for line in (root / path).read_text(encoding='utf-8').splitlines()]
    return [line for line in lines if line]


def load_manifest(root, path=MANIFEST):
    """The [[export]] and [[excluded]] tables of the manifest, validated."""
    data = tomllib.loads((root / path).read_text(encoding='utf-8'))
    default_args = data.get('default_args')
    if not (isinstance(default_args, list) and all(isinstance(a, str) for a in default_args)):
        raise Failure('%s: default_args must be a list of strings' % path)
    known = {'id', 'versions', 'dir', 'source', 'filter', 'filter_file', 'args', 'compare'}
    seen = set()
    entries = []
    for entry in data.get('export', []):
        where = '%s: export %r' % (path, entry.get('id'))
        if set(entry) - known:
            raise Failure('%s: unknown keys %s' % (where, sorted(set(entry) - known)))
        for key in ('id', 'dir', 'source'):
            if not isinstance(entry.get(key), str) or not entry[key]:
                raise Failure('%s: %s must be a nonempty string' % (where, key))
        if entry['id'] in seen:
            raise Failure('%s: duplicate id' % where)
        seen.add(entry['id'])
        versions = entry.get('versions')
        if not (isinstance(versions, list) and versions and all(v in VERSIONS for v in versions)):
            raise Failure('%s: versions must be a nonempty list of %s' % (where, ', '.join(VERSIONS)))
        if entry.get('compare') not in ('exact', 'subset'):
            raise Failure('%s: compare must be "exact" or "subset"' % where)
        if len(versions) > 1 and '{version}' not in entry['dir']:
            raise Failure('%s: several versions need {version} in dir' % where)
        args = entry.get('args', default_args)
        if not (isinstance(args, list) and all(isinstance(a, str) for a in args)):
            raise Failure('%s: args must be a list of strings' % where)
        entries.append(dict(entry, args=args, filter=entry.get('filter', '')))
    excluded = data.get('excluded', [])
    for entry in excluded:
        if set(entry) != {'root', 'reason'} or not all(isinstance(v, str) and v for v in entry.values()):
            raise Failure('%s: an [[excluded]] entry has exactly a nonempty root and reason' % path)
    return entries, excluded


def fixture_exports(root, versions, manifest=MANIFEST):
    entries, _ = load_manifest(root, manifest)
    exports = []
    for entry in entries:
        prefixes = [p for p in entry['filter'].split(',') if p]
        if 'filter_file' in entry:
            prefixes += read_filter_file(root, entry['filter_file'])
        for version in entry['versions']:
            if version not in versions:
                continue
            exports.append(Export(entry['id'], version, entry['source'], tuple(entry['args']), ','.join(prefixes),
                                  (entry['dir'].replace('{version}', version),), entry['compare']))
    return exports


def host_identity():
    """`uname -s` in lower case and `uname -m`, as scripts/check.sh names the golden overlays."""
    return platform.system().lower(), platform.machine()


def golden_exports(root, versions, host=None):
    """The golden exports of scripts/check.sh: every example of every requested version."""
    host_os, host_arch = host or host_identity()
    # check.sh: aarch64-linux exports for the baseline CPU; the other hosts keep the native CPU.
    args = ('-OReleaseSafe', '-fno-error-tracing') + (('-mcpu=baseline',) if (host_os, host_arch) == ('linux', 'aarch64') else ())
    exports = []
    for example in sorted(p.name for p in (root / 'examples').iterdir() if p.is_dir()):
        if example == 'asm' and host_arch not in ('x86_64', 'amd64'):
            continue  # check.sh: `asm` only on an x86_64 host
        listed = root / 'examples' / example / 'zig-versions'
        allowed = listed.read_text(encoding='utf-8').split() if listed.is_file() else VERSIONS
        for version in versions:
            if version not in allowed:
                continue
            prefixes = [example + '.']
            for name in ('filter', 'filter-' + version):
                if (root / 'examples' / example / name).is_file():
                    prefixes += read_filter_file(root, 'examples/%s/%s' % (example, name))
            layers = ('tests/golden/%s/air' % example,
                      'tests/golden/%s/%s/air' % (version, example),
                      'tests/golden/%s/%s/air-%s' % (version, example, host_os),
                      'tests/golden/%s/%s/air-%s-%s' % (version, example, host_os, host_arch))
            exports.append(Export('golden/' + example, version, 'examples/%s/%s.zig' % (example, example), args,
                                  ','.join(prefixes), layers, 'golden'))
    return exports


def recorded_exports(root, versions, suites=('golden', 'fixture'), only=None, manifest=MANIFEST):
    exports = []
    if 'golden' in suites:
        exports += golden_exports(root, versions)
    if 'fixture' in suites:
        exports += fixture_exports(root, versions, manifest)
    if only:
        pattern = re.compile(only)
        exports = [e for e in exports if pattern.search('%s@%s' % (e.id, e.version))]
    return exports


# ------------------------------------------------------------------ exporting and comparing

def run_export(root, compiler, export, out, scratch):
    """Run COMPILER (an argv prefix) for EXPORT into the new directory OUT."""
    out.mkdir(parents=True)
    env = dict(os.environ, ZIG_AIR_JSON_DIR=str(out))
    env.pop('ZIG_AIR_JSON_FILTER', None)
    if export.filter:
        env['ZIG_AIR_JSON_FILTER'] = export.filter
    cache = scratch / ('cache-' + out.name)
    result = subprocess.run(export.argv(compiler, cache), cwd=root, env=env, capture_output=True, text=True)
    shutil.rmtree(cache, ignore_errors=True)
    return result.returncode, result.stderr[-4000:]


def tree(directory):
    """name -> bytes of every regular file in DIRECTORY (flat: the exporter writes no subdirectories)."""
    directory = Path(directory)
    if not directory.is_dir():
        return {}
    return {p.name: p.read_bytes() for p in sorted(directory.iterdir()) if p.is_file()}


def compare_trees(expected, actual):
    """Differences of two {name: bytes} maps."""
    return {'same': sum(1 for n in expected if n in actual and expected[n] == actual[n]),
            'differ': sorted(n for n in expected if n in actual and expected[n] != actual[n]),
            'missing': sorted(n for n in expected if n not in actual),
            'extra': sorted(n for n in actual if n not in expected)}


def clean(diff, compare):
    """Is the comparison a match under COMPARE? `subset` allows extra fresh files."""
    return not diff['differ'] and not diff['missing'] and (compare == 'subset' or not diff['extra'])


def normalized_golden(root, layers, fresh, scratch):
    """Golden and fresh trees after scripts/normalize-air.py, as scripts/check.sh compares them.

    check.sh validates the fresh profile against the translator's report first and then drops it;
    here no translator runs, so the profile of the fresh export stands in for that report."""
    normalize = runpy.run_path(str(root / 'scripts/normalize-air.py'))
    context = normalize['ValidationContext']()
    first = next(iter(sorted(fresh.glob('*.json'))), None)
    if first is not None:
        context.profile = context.helpers['profile_for_air'](json.loads(first.read_text(encoding='utf-8')))
    golden, new = scratch / 'golden', scratch / 'new'
    for layer in layers:
        if (root / layer).is_dir():
            normalize['add_directory'](root / layer, golden, context)
    normalize['add_directory'](fresh, new, context)
    return tree(golden), tree(new)


def check_export(root, export, current, alt, scratch, committed=True):
    """Export with CURRENT (and ALT); compare. A JSON-ready result row."""
    work = Path(tempfile.mkdtemp(prefix='%s-%s.' % (export.id.replace('/', '-'), export.version), dir=scratch))
    row = {'id': export.id, 'version': export.version, 'command': export.command(),
           'committed_dirs': list(export.committed), 'compare': export.compare, 'work': str(work)}
    code, err = run_export(root, current, export, work / 'current', work)
    row['files'] = len(tree(work / 'current'))
    if code != 0:
        row.update(status='export-failed', exit=code, stderr=err)
        return row
    if alt is not None:
        alt_code, alt_err = run_export(root, alt, export, work / 'alt', work)
        if alt_code != 0:
            row.update(status='alt-failed', exit=alt_code, stderr=alt_err)
            return row
        row['alt'] = compare_trees(tree(work / 'current'), tree(work / 'alt'))
    if committed:
        if export.compare == 'golden':
            expected, actual = normalized_golden(root, export.committed, work / 'current', work)
        else:
            expected, actual = tree(root / export.committed[0]), tree(work / 'current')
            if not expected:
                row['committed'] = {'error': 'no committed files in ' + export.committed[0]}
        if 'committed' not in row:
            row['committed'] = compare_trees(expected, actual)
    alt_ok = alt is None or clean(row['alt'], 'exact')
    committed_ok = not committed or ('error' not in row['committed'] and clean(row['committed'], export.compare))
    row['status'] = 'alt-differs' if not alt_ok else ('ok' if committed_ok else 'committed-differs')
    return row


def summary(diff):
    if 'error' in diff:
        return diff['error']
    parts = ['%d same' % diff['same']]
    parts += ['%d %s' % (len(diff[k]), k) for k in ('differ', 'missing', 'extra') if diff[k]]
    return ', '.join(parts)


# ------------------------------------------------------------------ compilers

def current_compiler(root, version, overrides):
    if version in overrides:
        return [overrides[version]]
    result = subprocess.run([str(root / 'scripts/zig-air.sh'), version], cwd=root, capture_output=True, text=True)
    if result.returncode != 0:
        raise Failure('scripts/zig-air.sh %s failed:\n%s' % (version, result.stderr[-2000:]))
    return [result.stdout.strip().splitlines()[-1]]


def alt_compiler(template, current, version):
    if template is None:
        return None
    if template == 'self':
        return list(current)
    return [part.replace('{zig}', current[0]).replace('{version}', version) for part in shlex.split(template)]


# ------------------------------------------------------------------ CLI

def parse_overrides(pairs):
    overrides = {}
    for pair in pairs or []:
        version, sep, path = pair.partition('=')
        if not sep or version not in VERSIONS or not path:
            raise Failure('--zig takes VERSION=PATH with VERSION one of ' + ', '.join(VERSIONS))
        overrides[version] = str(Path(path).resolve())
    return overrides


def main(argv=None, root=ROOT):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='cmd', required=True)
    for name in ('list', 'run'):
        p = sub.add_parser(name)
        p.add_argument('--version', action='append', choices=VERSIONS, help='default: every version')
        p.add_argument('--suite', action='append', choices=('golden', 'fixture'), help='default: both')
        p.add_argument('--only', help='regular expression over <id>@<version>')
        p.add_argument('--manifest', type=Path, default=MANIFEST)
    p = sub.choices['run']
    p.add_argument('--alt', help="alternative exporter command ({zig}, {version}), or 'self'")
    p.add_argument('--zig', action='append', metavar='VERSION=PATH', help='current patched compiler of VERSION')
    p.add_argument('--jobs', type=int, default=2, help='exports at once (default 2)')
    p.add_argument('--report', type=Path, help='write the JSON report here')
    p.add_argument('--keep', type=Path, help='keep the exports in this new directory')
    p.add_argument('--no-committed', action='store_true', help='skip the comparison with committed files')
    p.add_argument('--require-committed', action='store_true',
                   help='also fail when a current export differs from its committed directory')
    args = parser.parse_args(argv)
    try:
        versions = tuple(args.version or VERSIONS)
        exports = recorded_exports(root, versions, tuple(args.suite or ('golden', 'fixture')), args.only, args.manifest)
        if args.cmd == 'list':
            for e in exports:
                print('%s@%s [%s] %s' % (e.id, e.version, e.compare, e.command()))
            return 0
        overrides = parse_overrides(args.zig)
        compilers = {v: current_compiler(root, v, overrides) for v in sorted({e.version for e in exports})}
        if args.keep:
            args.keep.mkdir(parents=True)
            scratch = args.keep.resolve()
        else:
            scratch = Path(tempfile.mkdtemp(prefix='air2lean-exporter-equivalence.'))
        try:
            with concurrent.futures.ThreadPoolExecutor(max(1, args.jobs)) as pool:
                rows = list(pool.map(lambda e: check_export(root, e, compilers[e.version],
                                                            alt_compiler(args.alt, compilers[e.version], e.version),
                                                            scratch, not args.no_committed), exports))
        finally:
            if not args.keep:
                shutil.rmtree(scratch, ignore_errors=True)
    except Failure as error:
        print('exporter-equivalence: %s' % error, file=sys.stderr)
        return 2
    failed = 0
    for row in rows:
        line = '%-8s %s@%s: %d files' % (row['status'], row['id'], row['version'], row['files'])
        if 'alt' in row:
            line += '; alt: ' + summary(row['alt'])
        if 'committed' in row:
            line += '; committed (%s): %s' % (row['compare'], summary(row['committed']))
        if 'stderr' in row:
            line += '\n    ' + row['stderr'].strip().replace('\n', '\n    ')
        print(line)
        bad = row['status'] in ('export-failed', 'alt-failed', 'alt-differs') or (
            args.require_committed and row['status'] == 'committed-differs')
        failed += bad
    counts = {}
    for row in rows:
        counts[row['status']] = counts.get(row['status'], 0) + 1
    print('exporter-equivalence: %d exports; %s' % (len(rows), ', '.join('%d %s' % (n, s) for s, n in sorted(counts.items()))))
    if args.report:
        args.report.write_text(json.dumps({'alt': args.alt, 'versions': list(versions), 'rows': rows},
                                          indent=1, sort_keys=True) + '\n', encoding='utf-8')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
