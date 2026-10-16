#!/usr/bin/env python3
"""Every proof-fixture check and Python test that CI runs, run locally (scripts/full-build.sh,
docs/ci.md#full-build).

    scripts/fixture-checks.sh [--logs DIR] [--base REF] [--only TEXT]...   (guarded; full-build.sh)
    python3 -B scripts/fixture-checks.py [--jobs N] [--mem-mib M] [--base REF] [--only TEXT]... [--logs DIR]
    python3 -B scripts/fixture-checks.py --list [--only TEXT]...
    python3 -B scripts/fixture-checks.py --prepare [--only TEXT]...

The checks are derived from the workflow, not listed: a *proof-fixture check* is a
`tests/**/check.sh` whose directory holds tracked `.lean` files, a *Python test* is a tracked
`tests/**/*.py` that a step runs with `python3` or a `tests/` directory it runs `python3 -m
unittest discover -s` on, and a check's *unit* is the CI step that runs it (the whole `run:`
script, with its `env:`), for every job row the step's `if:` may
run for (scripts/ci-reuse.py's `may_run`). The step is rendered for that row (`matrix.*`,
`github.workspace`, `runner.temp`); rows whose rendered step is the same run it once. So a new
check is covered by adding it to CI, and a step's own prerequisites, sibling gates and mode
switches (`check.sh --native`, `--export DIR`, an `if` on the version) run as CI runs them.

Toolchains (`--list` prints each unit's): the CI layout is provided from the shared cache
(docs/build-cache.md). `github.workspace` is a directory of links to the checkout's entries plus
`zig-air-VERSION` (the patched compiler, `scripts/zig-air.sh VERSION`, built on a miss) and
`host-zig` (the stock Zig of the row's version, `scripts/cas.py host-zig`), which also leads PATH
as CI's "Install host zig" puts it there; `runner.temp/host-zig-VERSION` is the stock Zig of
VERSION; a variable set to `github.workspace` itself is a directory of every version's compiler.
On macOS a stock 0.14.1 or 0.15.2 links with a failing `xcrun` first on PATH (as cas.py builds
them). A unit that names a toolchain the host cannot provide fails, naming it.

On a host other than the job's runner (the dev Mac for the x86_64-linux rows) the native-execution
invocations, a tests/ script called with `--native...` (scripts/target-matrix.py's convention),
are no-ops: they run binaries of the runner's target (scripts/local-ci.sh part PART runs them in
the Rosetta container, docs/rosetta.md). `--list` names them; a run prints their count.

Units run in parallel (scripts/par.py: --jobs, else AIR2LEAN_JOBS; at most budget/--mem-mib at
once), after the full build's Lean phases, each in its own worktree of the checkout's content
(scripts/ci-reuse.py `snapshot`) with copy-on-write clones of the Lake builds (`<package>/.lake/
build`) and of the ignored generated files, so that what a unit reads is what it alone read: every
file and directory there starts with an access time before its modification time, which any read,
mmap, exec or listing (not a stat) updates. A pass is a *record* of the unit's inputs, kept under
the unit's *pre-key* (`$AIR2LEAN_CAS_DIR/fixture-checks/traced/`, else `.lake/fixture-checks/`):
  - the pre-key: the rendered step and environment, the host, each toolchain's identity (the stock
    binary's path, size and mtime; a patched compiler's zig-patch/ inputs) and this script's
    staging, tracing and recording code (between the `key-relevant` markers);
  - the record: the content digest of every file the unit read (tracked, new or ignored); for a
    read Lake output (an olean, a trace, the translator binary) the sources of its module and of
    everything that module imports, transitively, with the lakefiles and the toolchain file; the
    names in every directory the unit listed or read a file from.
A unit is unchanged when one of its records matches the checkout. Its key thus covers exactly what
it read: a docs file, a generated inventory or another fixture's sources only when it read them.
The blind spots, as for every CI part: git history and refs (no unit reads them for its result),
files outside the checkout other than the toolchains, and a probe for an absent path in a
directory the unit neither listed nor read a file from; the nightly CI run executes every check on
every tree.

`--prepare` resolves the toolchains of the units that will run (a patched-compiler miss builds it
under its own scripts/build-guard.py); scripts/full-build.sh calls it before its guarded run.
Exit status: 0 when every unit passed or was unchanged, else 1 with each failure's log tail.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import par  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CR = _load('air2lean_ci_reuse', 'scripts/ci-reuse.py')
TM = CR.TM
CAS = _load('air2lean_cas', 'scripts/cas.py')
DEPS = _load('air2lean_lean_deps', 'scripts/lean-deps.py')
CHECK_TREE = _load('air2lean_check_tree', 'scripts/check-tree.py')

SCHEMA = 2
WS, TMP = '@WORKSPACE@', '@RUNNER_TEMP@'  # placeholders: the key does not depend on scratch paths
CHECK = re.compile(r'(?<![\w/.-])(tests/[\w/.-]+/check\.sh)\b')
PY_TEST = re.compile(r'(?<![\w/.-])python3?(?:[ \t]+-[A-Za-z]+)*[ \t]+(tests/[\w/.-]+\.py)\b'
                     r'|(?<![\w/.-])python3?[ \t]+-m[ \t]+unittest[ \t]+discover\b[^\n;&|]*?[ \t]-s[ \t]+(tests/[\w/.-]+)')
ARG = r'(?:[ \t]+(?:\\\n[ \t]*)?[^\s;&|()<>]+)'
NATIVE = re.compile(r'(?<![\w/.:-])(?:bash[ \t]+)?tests/[\w/.-]+\.sh%s*?[ \t]+--native[\w-]*%s*' % (ARG, ARG))
_ARCH = {'arm64': 'aarch64', 'amd64': 'x86_64'}
HOST = '%s-%s' % (_ARCH.get(platform.machine().lower(), platform.machine().lower()),
                  {'Darwin': 'macos'}.get(platform.system(), platform.system().lower()))


# ---- the tree ---------------------------------------------------------------------------------

class Tree:
    """The checkout's files (tracked, and new ones not ignored)."""

    def __init__(self):
        out = subprocess.run(['git', 'ls-files', '-z', '-co', '--exclude-standard'], cwd=ROOT,
                             check=True, capture_output=True, text=True).stdout
        self.files = sorted({f for f in out.split('\0') if f and (ROOT / f).is_file()})
        self.links = sorted({f for f in out.split('\0') if f and (ROOT / f).is_symlink()})
        self.file_set = set(self.files)
        self.dirs = {str(Path(f).parent) for f in self.files}
        self.dirs |= {str(p) for d in list(self.dirs) for p in Path(d).parents if str(p) != '.'}

    def under(self, d):
        prefix = d.rstrip('/') + '/'
        return [f for f in self.files if f.startswith(prefix)]


def is_proof_fixture(tree, script):
    return any(f.endswith('.lean') for f in tree.under(str(Path(script).parent)))


def checks_of(tree, run):
    """The proof-fixture checks and Python tests (files, or directories `unittest discover`s) RUN
    runs (see the module docstring)."""
    fixtures = {s for s in CHECK.findall(run) if is_proof_fixture(tree, s)}
    tests = {f or d.rstrip('/') for f, d in PY_TEST.findall(run)}
    return sorted(fixtures | {t for t in tests if t in tree.file_set or t in tree.dirs})


# ---- discovery --------------------------------------------------------------------------------

class Unsupported(Exception):
    pass


def render(text, row):
    text = re.sub(r'\$\{\{\s*github\.workspace\s*\}\}', WS, str(text))
    text = re.sub(r'\$\{\{\s*runner\.temp\s*\}\}', TMP, text)
    try:
        return TM.interpolate(text, {'matrix': row, 'runner.os': 'Linux'})
    except TM.Unknown as error:
        raise Unsupported(str(error)) from None


def strip_native(run):
    """RUN with every native-execution invocation (a tests/ script called with --native...,
    scripts/target-matrix.py's convention) turned into a no-op `:`; and those invocations."""
    found = NATIVE.findall(run)
    return NATIVE.sub(lambda m: ': ' + m.group(0), run), [' '.join(f.split()) for f in found]


def discover(tree):
    """[unit]: one per distinct rendered CI step that runs a proof-fixture check."""
    workflow = CR.load_workflow(ROOT)
    default = json.loads((ROOT / 'compatibility.json').read_text())['zig']['default'] \
        if (ROOT / 'compatibility.json').is_file() else None
    units = {}
    for job_id, job in (workflow.get('jobs') or {}).items():
        host = TM.runner_host(str(job.get('runs-on', '')))
        runner_os = host and TM.RUNNER_OS[host.split('-', 1)[1]]
        rows = CR.job_rows(job)
        # A step that renders the same for several rows runs once, for the default version's row.
        rows = sorted(rows, key=lambda r: (r or {}).get('zig') != default)
        for row in rows:
            context = {'matrix': row or {}, 'runner.os': runner_os}
            for step in job.get('steps') or []:
                if 'run' not in step or not CR.may_run(step, context):
                    continue
                checks = checks_of(tree, step['run'])
                if not checks:
                    continue
                name = '%s: %s' % (job_id, step.get('name', '?'))
                env = {**(job.get('env') or {}), **(step.get('env') or {})}
                try:
                    run, env, error = render(step['run'], row or {}), \
                        {k: render(v, row or {}) for k, v in env.items()}, None
                except Unsupported as unsupported:  # this unit fails, naming it; the others run
                    run, error = step['run'], 'unsupported expression: %s' % unsupported
                skipped = []
                if host != HOST:
                    run, skipped = strip_native(run)
                ident = json.dumps([job_id, step.get('name'), run, env], sort_keys=True)
                if ident in units:
                    units[ident]['rows'].append(CR.part_id(job_id, row))
                    continue
                units[ident] = {'name': name, 'job': job_id, 'rows': [CR.part_id(job_id, row)],
                                'zig': (row or {}).get('zig') or default, 'checks': checks,
                                'run': run, 'env': env, 'runner': host, 'skipped': skipped,
                                'error': error}
    out = list(units.values())
    shared = {u['name'] for u in out if sum(v['name'] == u['name'] for v in out) > 1}
    for unit in out:
        try:
            unit['toolchains'] = toolchains(unit)
        except Unsupported as unsupported:
            unit['toolchains'], unit['error'] = {'patched': [], 'stock': []}, unit['error'] or str(unsupported)
        if unit['name'] in shared:
            unit['name'] += ' [%s]' % ', '.join(unit['rows'])
    return sorted(out, key=lambda u: u['name'])


def zig_versions():
    """The Zig versions zig-patch/versions.toml supports."""
    data = tomllib.loads((ROOT / 'zig-patch/versions.toml').read_text(encoding='utf-8'))
    return sorted(v for v in data if re.fullmatch(r'\d+\.\d+\.\d+', v))


def toolchains(unit):
    """{'patched': [versions], 'stock': [versions]} the rendered step names. A variable set to
    github.workspace itself names the directory of every version's zig-air-VERSION."""
    text = unit['run'] + '\n' + '\n'.join(unit['env'].values())
    patched = set(re.findall(r'zig-air-(\d+\.\d+\.\d+)', text))
    if WS in unit['env'].values():
        patched.update(zig_versions())
    if len(re.findall(re.escape(WS) + r'/zig-air-\d+\.\d+\.\d+/', text)) != len(re.findall('zig-air-', text)):
        raise Unsupported('a patched compiler not at github.workspace/zig-air-VERSION')
    stock = set(re.findall(r'host-zig-(\d+\.\d+\.\d+)', text))
    if 'host-zig/' in text or any(v.strip() == 'zig' for v in unit['env'].values()):
        stock.add(unit['zig'])
    return {'patched': sorted(patched), 'stock': sorted(stock)}


# ---- key-relevant: begin ----------------------------------------------------------------------
# Everything from here to the `key-relevant: end` marker decides how a unit runs and what its
# record covers; its text is part of every pre-key (RUNNER), so a change here reruns every unit.

# A read Lake output: <package>/.lake/build/(lib/lean|ir)/<module path>.<extension...>, or a binary.
LAKE_OUTPUT = re.compile(r'^(?:(?P<pkg>.+)/)?\.lake/build/(?:(?:lib/lean|ir)/(?P<mod>[^.]+)\..*|bin/(?P<exe>[^.]+).*|.*)$')
LAKE_FILES = ('lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json')
NOISE = {'__pycache__', '.DS_Store'}


class Keyer:
    """Pre-keys, records and their lookup over one state of the checkout (see the docstring)."""

    def __init__(self, tree):
        self.tree = tree
        self.identity, self.digests, self.listings, self.lean = {}, {}, {}, {}

    def digest(self, path):
        """Content digest of a file of the checkout (a symlink: its target path; absent: None); a
        directory (`DIR/`): the digest of its entries' names."""
        if path not in self.digests:
            p = ROOT / path
            if path.endswith('/'):
                value = hashlib.sha256('\0'.join(sorted(set(os.listdir(p)) - NOISE)).encode()).hexdigest() \
                    if p.is_dir() else None
            elif p.is_symlink():
                value = 'link:' + os.readlink(p)
            else:
                value = hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
            self.digests[path] = value
        return self.digests[path]

    def lean_inputs(self, module, pkg):
        """The sources a Lake build of MODULE in package directory PKG ('' for the root package) is
        a function of: its source (PKG's, else the root package's) and those of everything it
        imports, transitively; toolchain modules have none."""
        if (module, pkg) not in self.lean:
            self.lean[module, pkg] = set()  # Lean imports are acyclic
            rel = module.replace('.', '/') + '.lean'
            source = next((p for p in ((pkg + '/' + rel) if pkg else rel, rel) if p in self.tree.file_set), None)
            if source:
                self.lean[module, pkg] = {source}.union(*(self.lean_inputs(m, pkg) for m in DEPS.imports(ROOT / source)))
        return self.lean[module, pkg]

    def lake_inputs(self, path):
        """The sources that a read Lake output PATH is a function of (see lean_inputs), with the
        lakefiles and toolchain of its package and the root; an output this cannot attribute to a
        module: every tracked file of its package."""
        m = LAKE_OUTPUT.match(path)
        pkg = (m and m.group('pkg')) or ''
        lake = {f for d in {'', pkg} for f in ((d + '/' + n) if d else n for n in LAKE_FILES) if f in self.tree.file_set}
        if m and m.group('mod'):
            return lake | self.lean_inputs(m.group('mod').replace('/', '.'), pkg)
        if m and m.group('exe'):
            lakefile = ROOT / pkg / 'lakefile.toml'
            exes = tomllib.loads(lakefile.read_text()).get('lean_exe', []) if lakefile.is_file() else []
            roots = [e.get('root', e['name']) for e in exes if e['name'] == m.group('exe')]
            if roots:
                return lake.union(*(self.lean_inputs(r, pkg) for r in roots))
        return lake | {f for f in self.tree.files if not pkg or f.startswith(pkg + '/')}

    def record(self, unit, reads):
        """The record of a pass that read READS (paths relative to the checkout; a directory listed:
        `DIR/`): {path: digest} of every input it covers (see the docstring)."""
        files = set()
        for path in reads:
            if path.endswith('/'):
                continue
            files |= self.lake_inputs(path) if '.lake/build/' in '/' + path else {path}
        # Listings of the checkout's own directories (an ignored one, a Lake build, holds clones
        # whose reads count above).
        listed = {p for p in reads if p.endswith('/') and (p == './' or p[:-1] in self.tree.dirs)}
        listed |= {str(Path(f).parent) + '/' for f in files if f in self.tree.file_set}
        # A read through a symlink touches its target only: the links themselves are inputs too.
        return {p: self.digest(p) for p in sorted(files | listed | set(self.tree.links))}

    def matches(self, record):
        return all(self.digest(p) == d for p, d in record.items())

    def tool(self, kind, version):
        """A toolchain's identity: the stock Zig's path, size and modification time; a patched
        compiler is a function of its stock bootstrap and its zig-patch/ inputs."""
        if (kind, version) not in self.identity:
            try:
                zig = CAS.host_zig(version)
                info = zig.stat()
                identity = [str(zig), info.st_size, info.st_mtime_ns]
                if kind == 'patched':
                    identity.append(CAS.zig_patch_inputs(ROOT, version))
            except CAS.CasError as error:
                identity = 'unavailable: %s' % error.args[0]
            self.identity[kind, version] = identity
        return [kind, self.identity[kind, version], os.environ.get('AIR2LEAN_OPTIMIZE', '')]

    def prekey(self, unit):
        return hashlib.sha256(json.dumps({
            'schema': SCHEMA, 'runner': RUNNER, 'run': unit['run'], 'env': unit['env'],
            'host': [platform.system(), platform.machine()],
            'tools': {k: {v: self.tool(k, v) for v in vs} for k, vs in unit['toolchains'].items()},
            'path-zig': self.tool('stock', unit['zig']),
        }, sort_keys=True).encode()).hexdigest()

    def records(self, unit):
        """The unit's records, newest first."""
        directory = store_dir() / self.prekey(unit)
        paths = sorted(directory.glob('*.json'), key=lambda p: p.stat().st_mtime, reverse=True) \
            if directory.is_dir() else []
        return [(p, json.loads(p.read_text())) for p in paths]

    def unchanged(self, unit):
        """Whether a record of the unit matches the checkout (it is then marked used)."""
        for path, record in self.records(unit):
            if self.matches(record):
                os.utime(path)
                return True
        return False

    def remember(self, unit, reads, keep=8):
        """Store the record of a pass that read READS; keep the newest KEEP records of the unit."""
        record = self.record(unit, reads)
        directory = store_dir() / self.prekey(unit)
        directory.mkdir(parents=True, exist_ok=True)
        text = json.dumps(record, sort_keys=True)
        staged = directory / ('.%d.tmp' % os.getpid())
        staged.write_text(text)
        os.replace(staged, directory / (hashlib.sha256(text.encode()).hexdigest() + '.json'))
        for path, _ in self.records(unit)[keep:]:
            path.unlink(missing_ok=True)


def store_dir():
    cas = os.environ.get('AIR2LEAN_CAS_DIR')
    return (Path(cas).expanduser() / 'fixture-checks' if cas else ROOT / '.lake' / 'fixture-checks') / 'traced'


def cloned_entries():
    """The ignored entries a unit's worktree gets as copy-on-write clones: every package's Lake
    build (`<package>/.lake/build`) and the ignored files outside `.lake` (the materialized
    generated files); no tool caches or Python bytecode (a unit recomputes them)."""
    out = CR.git(ROOT, 'ls-files', '-z', '-o', '-i', '--exclude-standard', '--directory').decode()
    entries = []
    for entry in (e for e in out.split('\0') if e and not NOISE & set(e.rstrip('/').split('/'))):
        if entry.rstrip('/').endswith('.lake'):
            if (ROOT / entry / 'build').is_dir():
                entries.append(entry.rstrip('/') + '/build')
        elif '/.lake/' not in '/' + entry:
            entries.append(entry.rstrip('/'))
    return entries


def watch(dest):
    """Give every file and directory under DEST (but .git) an access time before its modification
    time, so that a read, mmap, exec or listing updates it; return them (directories as `DIR/`)."""
    watched = []
    for dirpath, dirnames, filenames in os.walk(dest):
        here = Path(dirpath)
        if here == dest:
            dirnames[:] = [d for d in dirnames if d != '.git']
            filenames = [f for f in filenames if f != '.git']
        rel = here.relative_to(dest).as_posix()
        for name in filenames + [d for d in dirnames if (here / d).is_symlink()]:
            path = here / name
            if not path.is_symlink():
                os.utime(path, ns=(0, os.stat(path).st_mtime_ns))
                watched.append(name if rel == '.' else rel + '/' + name)
        os.utime(here, ns=(0, os.stat(here).st_mtime_ns))
        watched.append(rel + '/')
    return watched


def traced(spec):
    """`--traced SPEC`: SPEC's command in a fresh worktree of SPEC's commit at SPEC's `dest` (where
    the CI layout's links point) with the cloned entries; then the watched paths it read go to
    SPEC's `trace`, and the worktree is removed. Exit status: the command's."""
    s = json.loads(Path(spec).read_text())
    dest = Path(s['dest'])
    CR.git(ROOT, 'worktree', 'add', '--quiet', '--detach', str(dest), s['commit'])
    try:
        for rel in s['clone']:
            CHECK_TREE.clone_tree(ROOT / rel, dest / rel)
        watched = watch(dest)
        code = subprocess.run(s['argv'], cwd=dest, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')).returncode
        read = []
        for rel in watched:
            try:
                if os.stat(dest / rel, follow_symlinks=False).st_atime_ns != 0:
                    read.append(rel)
            except FileNotFoundError:
                read.append(rel)  # removed by the run: count it as read
        Path(s['trace']).write_text(json.dumps(read))
        return code
    finally:
        CR.git(ROOT, 'worktree', 'remove', '--force', str(dest), check=False)
        shutil.rmtree(dest, ignore_errors=True)


class Unavailable(Exception):
    pass


def resolve(kind, version):
    """bin/zig of a toolchain; a patched-compiler miss builds it (scripts/build-guard.py)."""
    try:
        return Path(CAS.zig_air(ROOT, version) if kind == 'patched' else CAS.host_zig(version))
    except CAS.CasError as error:
        raise Unavailable('cannot provide the %s Zig %s: %s' % (kind, version, error.args[0])) from None


def stage(unit, scratch):
    """(argv, env) of the unit: the CI layout under SCRATCH, the step's environment; a unit whose
    toolchain this host cannot provide becomes a command that fails with the reason."""
    try:
        if unit['error']:
            raise Unavailable(unit['error'])
        return _stage(unit, scratch)
    except Unavailable as error:
        return ['sh', '-c', 'echo "fixture-checks: $1" >&2; exit 1', 'sh', str(error)], None


def _stage(unit, scratch):
    workspace, temp = scratch / 'workspace', scratch / 'temp'
    workspace.mkdir(parents=True)
    temp.mkdir()
    for entry in ROOT.iterdir():  # the entries of the unit's worktree (traced), made at its start
        if entry.name not in NOISE:
            (workspace / entry.name).symlink_to(scratch / 'tree' / entry.name)
    for version in unit['toolchains']['patched']:
        (workspace / ('zig-air-' + version)).symlink_to(resolve('patched', version).parent.parent)
    for version in unit['toolchains']['stock']:
        (temp / ('host-zig-' + version)).symlink_to(resolve('stock', version).parent)
    env = dict(os.environ, RUNNER_TEMP=str(temp), GITHUB_WORKSPACE=str(workspace))
    path = []
    try:  # CI's "Install host zig": the row's stock Zig, first on PATH, for every unit
        (workspace / 'host-zig').symlink_to(resolve('stock', unit['zig']).parent)
        path.append(str(workspace / 'host-zig'))
    except Unavailable:
        if unit['zig'] in unit['toolchains']['stock']:  # named by the step: required
            raise
    if platform.system() == 'Darwin' and CAS.DARWIN_NO_XCRUN & {unit['zig'], *unit['toolchains']['stock']}:
        # As for building these compilers (scripts/cas.py): a failing `xcrun` makes the stock Zig
        # link against its bundled macOS libc; Apple's current SDK fails its detection.
        shim = scratch / 'no-xcrun'
        shim.mkdir()
        (shim / 'xcrun').write_text('#!/bin/sh\nexit 1\n')
        (shim / 'xcrun').chmod(0o755)
        path.insert(0, str(shim))
    env['PATH'] = os.pathsep.join(path + [env.get('PATH', '')])

    def place(text):
        return text.replace(WS, str(workspace)).replace(TMP, str(temp))

    env.update({name: place(value) for name, value in unit['env'].items()})
    return ['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', place(unit['run'])], env


def staged_job(unit, scratch, name, commit, clone):
    """par.Job of the unit: its staged command run by `--traced` in its own worktree (SCRATCH/tree),
    the trace going to SCRATCH/trace.json; a unit that cannot be staged fails, naming why."""
    command, env = stage(unit, scratch)
    if env is None:
        return par.Job(name, command, cwd=str(ROOT))
    spec = scratch / 'spec.json'
    spec.write_text(json.dumps({'argv': command, 'dest': str(scratch / 'tree'), 'commit': commit,
                                'clone': clone, 'trace': str(scratch / 'trace.json')}))
    return par.Job(name, [sys.executable, '-B', str(Path(__file__).resolve()), '--traced', str(spec)],
                   cwd=str(ROOT), env=env)

# ---- key-relevant: end ------------------------------------------------------------------------


def _runner():
    text = Path(__file__).read_text()
    return hashlib.sha256(text[text.index('# ---- key-relevant: begin'):
                               text.index('# ---- key-relevant: end')].encode()).hexdigest()


RUNNER = _runner()


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ['--traced']:
        return traced(argv[1])
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--list', action='store_true', help='print the units, their checks and toolchains')
    parser.add_argument('--prepare', action='store_true', help='resolve the pending units\' toolchains only')
    parser.add_argument('--pending', action='store_true',
                        help='exit 0 when no unit needs to run (fixture-checks.sh then asks for no admission)')
    parser.add_argument('--only', action='append', default=[], help='units whose name or checks contain TEXT')
    parser.add_argument('--base', help='only the units whose key covers a file changed since REF '
                        '(git diff REF, and new files); all of them when the workflow changed')
    parser.add_argument('--jobs', type=int)
    # A unit's peak: three at once reached 10.4 GiB under the full build's 11000 MiB guard.
    parser.add_argument('--mem-mib', type=int, default=5000, help='peak memory of one unit (default 5000)')
    parser.add_argument('--logs', type=Path, help='keep every unit\'s log here')
    a = parser.parse_args(argv)
    tree = Tree()
    units = [u for u in discover(tree)
             if not a.only or any(t in u['name'] or any(t in c for c in u['checks']) for t in a.only)]
    if a.list:
        for u in units:
            print('%s\n    checks: %s\n    toolchains: %s' % (
                u['name'], ' '.join(u['checks']),
                ', '.join('%s %s' % (k, v) for k, vs in u['toolchains'].items() for v in vs) or 'none'))
            if u['error']:
                print('    fails: %s' % u['error'])
            for s in u['skipped']:
                print('    not on %s (needs %s): %s' % (HOST, u['runner'], s))
        print('fixture-checks: %d units, %d checks' % (len(units), len({c for u in units for c in u['checks']})))
        return 0
    keyer = Keyer(tree)
    if a.base:
        changed = set(CR.changed_files(ROOT, a.base))
        if CR.WORKFLOW not in changed:  # a changed workflow can change any unit: keep them all
            # A unit with no record yet is kept; one is affected when a file it read changed.
            units = [u for u in units if not (records := keyer.records(u))
                     or any(changed & set(r) for _, r in records)]
    todo = [u for u in units if not keyer.unchanged(u)]
    if a.pending:
        if todo:
            return 1
        print('fixture-checks: %d units, all unchanged since their last pass' % len(units))
        return 0
    if a.prepare:
        for kind, version in sorted({(k, v) for u in todo for k, vs in u['toolchains'].items() for v in vs}):
            try:
                print('fixture-checks: %s Zig %s: %s' % (kind, version, resolve(kind, version)))
            except Unavailable as error:  # the units that need it fail in the run, naming it
                print('fixture-checks: %s' % error, file=sys.stderr)
        return 0
    failed = []
    if todo:
        scratch = Path(tempfile.mkdtemp(prefix='air2lean-fixture-checks.'))
        logs = a.logs or Path(tempfile.mkdtemp(prefix='air2lean-fixture-logs.'))
        logs.mkdir(parents=True, exist_ok=True)
        names = {u['name']: '%02d-%s' % (i, par.safe_name(u['name'])[:80]) for i, u in enumerate(todo)}
        commit, clone = CR.snapshot(ROOT), cloned_entries()
        try:
            jobs = [staged_job(u, scratch / names[u['name']], names[u['name']], commit, clone) for u in todo]
            print('fixture-checks: running %d of %d units' % (len(todo), len(units)), flush=True)
            with open(os.devnull, 'wb') as null:
                statuses = par.run(jobs, par.workers(a.jobs, a.mem_mib, len(jobs)), out=null, err=null,
                                   log_dir=logs)
            for u, status in zip(todo, statuses):
                trace = scratch / names[u['name']] / 'trace.json'
                if status == 0 and trace.is_file():
                    keyer.remember(u, json.loads(trace.read_text()))
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
        for u, status in zip(todo, statuses):
            if status == 0:
                continue
            log = logs / (names[u['name']] + '.log')
            tail = log.read_text(errors='replace').strip().splitlines()[-15:] if log.is_file() else []
            failed.append('%s (exit %d, log %s)%s' % (u['name'], status, log, ''.join('\n    ' + l for l in tail)))
        if not failed and not a.logs:
            shutil.rmtree(logs, ignore_errors=True)
    skipped = sum(len(u['skipped']) for u in units)
    print('fixture-checks: %d units (%d checks), %d run, %d unchanged since their last pass, %d failed'
          % (len(units), len({c for u in units for c in u['checks']}), len(todo), len(units) - len(todo), len(failed)))
    if skipped:
        print('fixture-checks: %d native runs need their CI host, not %s (--list names them; '
              'scripts/local-ci.sh part PART runs them)' % (skipped, HOST))
    for f in failed:
        print('fixture-checks: FAILED ' + f, file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
