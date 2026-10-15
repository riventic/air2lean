#!/usr/bin/env python3
"""Every proof-fixture check that CI runs, run locally (scripts/full-build.sh, docs/ci.md#full-build).

    python3 -B scripts/fixture-checks.py [--jobs N] [--mem-mib M] [--only TEXT]... [--logs DIR]
    python3 -B scripts/fixture-checks.py --list [--only TEXT]...
    python3 -B scripts/fixture-checks.py --prepare [--only TEXT]...

The checks are derived from the workflow, not listed: a *proof-fixture check* is a
`tests/**/check.sh` whose directory holds tracked `.lean` files, and its *unit* is the CI step
that runs it (the whole `run:` script, with its `env:`), for every job row the step's `if:` may
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
once), in the checkout, after the full build's Lean phases. A pass is remembered under a key
(`$AIR2LEAN_CAS_DIR/fixture-checks/`, else `.lake/fixture-checks/`), so an unchanged tree costs
seconds. The key covers: the rendered step and environment, the host, each toolchain's identity
(the patched compiler's cache key, the stock binary's digest), and the content of
  - the translator and tooling: Air2Lean/, scripts/, zig-patch/, tools/ and the top-level files
    other than *.md (lakefile, toolchain, manifest);
  - every tracked or new file under tests/ outside the fixture directories (shared models, logs);
  - the directories of the step's fixture checks;
  - every file or directory a scanned text names by its repository path (another fixture's
    directory, examples/X, docs/X.json, ...), scanned again in turn;
  - the library modules (ZigLean, Proofs, ...) a scanned text names (imports, `lake build`
    targets, module names), with their transitive imports.
A check that reaches a file by a path none of these spells out (a glob over another fixture's
directory) is not keyed by it; the nightly CI run executes every check on every tree.

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

SCHEMA = 1
WS, TMP = '@WORKSPACE@', '@RUNNER_TEMP@'  # placeholders: the key does not depend on scratch paths
CHECK = re.compile(r'(?<![\w/.-])(tests/[\w/.-]+/check\.sh)\b')
PATH_TOKEN = re.compile(r'(?<![\w/.-])\.?/?([A-Za-z0-9_][\w.-]*(?:/[\w.-]+)+)')
ARG = r'(?:[ \t]+(?:\\\n[ \t]*)?[^\s;&|()<>]+)'
NATIVE = re.compile(r'(?<![\w/.:-])(?:bash[ \t]+)?tests/[\w/.-]+\.sh%s*?[ \t]+--native[\w-]*%s*' % (ARG, ARG))
_ARCH = {'arm64': 'aarch64', 'amd64': 'x86_64'}
HOST = '%s-%s' % (_ARCH.get(platform.machine().lower(), platform.machine().lower()),
                  {'Darwin': 'macos'}.get(platform.system(), platform.system().lower()))
BASE_DIRS = ('Air2Lean/', 'scripts/', 'zig-patch/', 'tools/')
SCAN_SUFFIXES = {'.sh', '.py', '.lean', '.zig', '.toml', '.txt', '.yml', '.args'}
SCAN_MAX_BYTES = 1 << 20


# ---- the tree ---------------------------------------------------------------------------------

class Tree:
    """The checkout's files (tracked, and new ones not ignored) and their content digests."""

    def __init__(self):
        out = subprocess.run(['git', 'ls-files', '-z', '-co', '--exclude-standard'], cwd=ROOT,
                             check=True, capture_output=True, text=True).stdout
        self.files = sorted({f for f in out.split('\0') if f and (ROOT / f).is_file()})
        self.file_set = set(self.files)
        self.dirs = {str(Path(f).parent) for f in self.files}
        self.dirs |= {str(p) for d in list(self.dirs) for p in Path(d).parents if str(p) != '.'}
        self._digest = {}

    def digest(self, f):
        if f not in self._digest:
            self._digest[f] = hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
        return self._digest[f]

    def under(self, d):
        prefix = d.rstrip('/') + '/'
        return [f for f in self.files if f.startswith(prefix)]


def fixture_dirs(tree):
    """Directories of every tests/**/check.sh (the fixtures; a check's own files live there)."""
    return sorted({str(Path(f).parent) for f in tree.files
                   if f.startswith('tests/') and f.endswith('/check.sh')})


def is_proof_fixture(tree, script):
    return any(f.endswith('.lean') for f in tree.under(str(Path(script).parent)))


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
                checks = sorted({s for s in CHECK.findall(step['run']) if is_proof_fixture(tree, s)})
                if not checks:
                    continue
                name = '%s: %s' % (job_id, step.get('name', '?'))
                try:
                    run = render(step['run'], row or {})
                    env = {k: render(v, row or {}) for k, v in {**(job.get('env') or {}),
                                                                **(step.get('env') or {})}.items()}
                except Unsupported as error:
                    raise SystemExit('fixture-checks: %s: unsupported expression: %s' % (name, error))
                skipped = []
                if host != HOST:
                    run, skipped = strip_native(run)
                ident = json.dumps([job_id, step.get('name'), run, env], sort_keys=True)
                if ident in units:
                    units[ident]['rows'].append(CR.part_id(job_id, row))
                    continue
                units[ident] = {'name': name, 'job': job_id, 'rows': [CR.part_id(job_id, row)],
                                'zig': (row or {}).get('zig') or default, 'checks': checks,
                                'run': run, 'env': env, 'runner': host, 'skipped': skipped}
    out = list(units.values())
    shared = {u['name'] for u in out if sum(v['name'] == u['name'] for v in out) > 1}
    for unit in out:
        unit['toolchains'] = toolchains(unit)
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
        raise SystemExit('fixture-checks: %s: a patched compiler not at github.workspace/zig-air-VERSION'
                         % unit['name'])
    stock = set(re.findall(r'host-zig-(\d+\.\d+\.\d+)', text))
    if 'host-zig/' in text or any(v.strip() == 'zig' for v in unit['env'].values()):
        stock.add(unit['zig'])
    return {'patched': sorted(patched), 'stock': sorted(stock)}


# ---- the key ----------------------------------------------------------------------------------

class Keyer:
    def __init__(self, tree):
        self.tree = tree
        self.fixtures = fixture_dirs(tree)
        self.roots = DEPS.lib_roots()
        self.module_token = re.compile(r'\b((?:%s)(?:\.[A-Za-z_][\w\']*)*)' %
                                       '|'.join(sorted(map(re.escape, self.roots))))
        self.base = [f for f in tree.files
                     if f.startswith(BASE_DIRS) or ('/' not in f and not f.endswith('.md'))
                     or (f.startswith('tests/') and not any(f.startswith(d + '/') for d in self.fixtures))]
        self.identity = {}

    def modules(self, text):
        """The library modules TEXT names (the longest module prefix of each dotted name)."""
        out = set()
        for name in self.module_token.findall(text):
            parts = name.split('.')
            for n in range(len(parts), 0, -1):
                if DEPS.module_file('.'.join(parts[:n])).is_file():
                    out.add('.'.join(parts[:n]))
                    break
        return out

    def paths(self, text):
        out = set()
        for token in PATH_TOKEN.findall(text):
            token = token.rstrip('.')
            if token in self.tree.dirs:
                out.update(self.tree.under(token))
            elif token in self.tree.file_set:
                out.add(token)
        return out

    def files(self, unit):
        """Every file the unit's key covers (see the module docstring)."""
        chosen = set(self.base)
        for check in unit['checks']:
            chosen.update(self.tree.under(str(Path(check).parent)))
        texts, scanned, modules = [unit['run'] + '\n' + '\n'.join(unit['env'].values())], set(), set()
        todo = sorted(chosen - set(self.base))
        while texts or todo:
            for text in texts:
                modules |= self.modules(text)
                new = self.paths(text) - chosen
                chosen |= new
                todo += sorted(new)
            texts = []
            while todo:
                f = todo.pop()
                if f in scanned:
                    continue
                scanned.add(f)
                p = ROOT / f
                if p.suffix in SCAN_SUFFIXES and p.stat().st_size <= SCAN_MAX_BYTES:
                    texts.append(p.read_text(encoding='utf-8', errors='replace'))
        seen, stack = set(), sorted(modules)
        while stack:
            m = stack.pop()
            if m in seen or m.split('.')[0] not in self.roots or not DEPS.module_file(m).is_file():
                continue
            seen.add(m)
            stack += sorted(DEPS.imports(DEPS.module_file(m)))
        chosen |= {str(DEPS.module_file(m).relative_to(ROOT)) for m in seen}
        return sorted(chosen)

    def tool(self, kind, version):
        if (kind, version) not in self.identity:
            try:
                if kind == 'patched':
                    value = CAS.zig_air(ROOT, version, key_only=True)
                else:
                    value = CAS.sha256_file(CAS.host_zig(version))
            except CAS.CasError as error:
                value = 'unavailable: %s' % error.args[0]
            self.identity[(kind, version)] = value
        return self.identity[(kind, version)]

    def key(self, unit):
        h = hashlib.sha256(json.dumps({
            'schema': SCHEMA, 'run': unit['run'], 'env': unit['env'],
            'host': [platform.system(), platform.machine()],
            'tools': {k: {v: self.tool(k, v) for v in vs} for k, vs in unit['toolchains'].items()},
        }, sort_keys=True).encode())
        for f in self.files(unit):
            h.update(f.encode() + b'\0' + self.tree.digest(f).encode() + b'\n')
        return h.hexdigest()


# ---- running ----------------------------------------------------------------------------------

def store_dir():
    cas = os.environ.get('AIR2LEAN_CAS_DIR')
    return Path(cas).expanduser() / 'fixture-checks' if cas else ROOT / '.lake' / 'fixture-checks'


def resolve(kind, version):
    """bin/zig of a toolchain; a patched-compiler miss builds it (scripts/build-guard.py)."""
    try:
        return Path(CAS.zig_air(ROOT, version) if kind == 'patched' else CAS.host_zig(version))
    except CAS.CasError as error:
        raise SystemExit('fixture-checks: cannot provide the %s Zig %s: %s' % (kind, version, error.args[0]))


def stage(unit, scratch):
    """(argv, env) of the unit: the CI layout under SCRATCH, the step's environment."""
    workspace, temp = scratch / 'workspace', scratch / 'temp'
    workspace.mkdir(parents=True)
    temp.mkdir()
    for entry in ROOT.iterdir():
        (workspace / entry.name).symlink_to(entry)
    for version in unit['toolchains']['patched']:
        (workspace / ('zig-air-' + version)).symlink_to(resolve('patched', version).parent.parent)
    for version in unit['toolchains']['stock']:
        (temp / ('host-zig-' + version)).symlink_to(resolve('stock', version).parent)
    env = dict(os.environ, RUNNER_TEMP=str(temp), GITHUB_WORKSPACE=str(workspace))
    path = []
    if unit['zig'] in unit['toolchains']['stock']:
        (workspace / 'host-zig').symlink_to(resolve('stock', unit['zig']).parent)
        path.append(str(workspace / 'host-zig'))
    if platform.system() == 'Darwin' and CAS.DARWIN_NO_XCRUN & set(unit['toolchains']['stock']):
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--list', action='store_true', help='print the units, their checks and toolchains')
    parser.add_argument('--prepare', action='store_true', help='resolve the pending units\' toolchains only')
    parser.add_argument('--only', action='append', default=[], help='units whose name or checks contain TEXT')
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
            for s in u['skipped']:
                print('    not on %s (needs %s): %s' % (HOST, u['runner'], s))
        print('fixture-checks: %d units, %d checks' % (len(units), len({c for u in units for c in u['checks']})))
        return 0
    keyer, store = Keyer(tree), store_dir()
    keys = {u['name']: keyer.key(u) for u in units}
    todo = [u for u in units if not (store / keys[u['name']]).exists()]
    if a.prepare:
        for kind, version in sorted({(k, v) for u in todo for k, vs in u['toolchains'].items() for v in vs}):
            print('fixture-checks: %s Zig %s: %s' % (kind, version, resolve(kind, version)))
        return 0
    failed = []
    if todo:
        scratch = Path(tempfile.mkdtemp(prefix='air2lean-fixture-checks.'))
        logs = a.logs or Path(tempfile.mkdtemp(prefix='air2lean-fixture-logs.'))
        logs.mkdir(parents=True, exist_ok=True)
        names = {u['name']: '%02d-%s' % (i, par.safe_name(u['name'])[:80]) for i, u in enumerate(todo)}
        try:
            jobs = []
            for u in todo:
                command, env = stage(u, scratch / names[u['name']])
                jobs.append(par.Job(names[u['name']], command, cwd=str(ROOT), env=env))
            print('fixture-checks: running %d of %d units' % (len(todo), len(units)), flush=True)
            with open(os.devnull, 'wb') as null:
                statuses = par.run(jobs, par.workers(a.jobs, a.mem_mib, len(jobs)), out=null, err=null,
                                   log_dir=logs)
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
        store.mkdir(parents=True, exist_ok=True)
        for u, status in zip(todo, statuses):
            if status == 0:
                (store / keys[u['name']]).touch()
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
