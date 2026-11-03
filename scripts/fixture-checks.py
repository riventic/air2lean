#!/usr/bin/env python3
"""Every proof-fixture check that CI runs, run locally (scripts/full-build.sh, docs/ci.md#full-build).

    scripts/fixture-checks.sh [--logs DIR] [--only TEXT]...   (guarded; full-build.sh)
    python3 -B scripts/fixture-checks.py [--jobs N] [--mem-mib M] [--only TEXT]... [--logs DIR] [--rerun]
    python3 -B scripts/fixture-checks.py --pending [--only TEXT]...
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
once), in the checkout, after the full build's Lean phases.

A unit runs unless a pass of exactly its inputs is recorded. Its key covers everything it can
read, not the files it names (a key over those missed every input reached by a path built in
code: a stale pass of tests/roadmap/callbacks after an edit of tests/roadmap/asm-effects, #443):
the content of every file of the checkout, tracked or not, and of the whole-tree generated
files; every build output of the three Lake packages; the Lean toolchain's runtime digest; the
content of each Zig compiler it names; python3, bash and git on PATH; the host; the inherited
environment (all of it but RUN_VARIABLES, RUN_PREFIXES); and its CI step (`run_inputs`, `unit_key`). So any edit
anywhere runs every unit again, and an unchanged tree runs none (docs/ci.md#full-build). A pass
is recorded (~/.cache/air2lean/fixture-checks/passes, AIR2LEAN_FIXTURE_PASSES) only when those
inputs are the same at the end of the run as at its start. CI (GITHUB_ACTIONS or CI set: pull
requests, main, nightly, release) never reuses or records a pass. `--rerun` runs every unit;
`--pending` exits 0 when no unit would run (scripts/fixture-checks.sh then takes no admission).

The units of one run audit one build, so their `fixtures.py audit`s share one kernel-replay cache
(AIR2LEAN_FIXTURE_REPLAY_CACHE, a file in the run's scratch directory, removed with it): a
Lake-built module that one audit replayed is not replayed again in this run
(scripts/assumptions.py `kernel_replay`). Nothing outlives the run.

`--prepare` resolves the toolchains of the units that will run (a patched-compiler miss builds it
under its own scripts/build-guard.py); scripts/full-build.sh calls it before its guarded run.
Exit status: 0 when every unit passed, else 1 with each failure's log tail.
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
import time
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
GENERATED = _load('air2lean_generated', 'scripts/generated.py')
import assumptions as AS  # noqa: E402

WS, TMP = '@WORKSPACE@', '@RUNNER_TEMP@'  # placeholders for the unit's scratch paths
CHECK = re.compile(r'(?<![\w/.-])(tests/[\w/.-]+/check\.sh)\b')
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

    def under(self, d):
        prefix = d.rstrip('/') + '/'
        return [f for f in self.files if f.startswith(prefix)]


def is_proof_fixture(tree, script):
    return any(f.endswith('.lean') for f in tree.under(str(Path(script).parent)))


# ---- discovery --------------------------------------------------------------------------------

class Unsupported(Exception):
    pass


def render(text, row):
    try:
        text = re.sub(r'\$\{\{\s*github\.workspace\s*\}\}', WS, TM.expression_string(text))
        text = re.sub(r'\$\{\{\s*runner\.temp\s*\}\}', TMP, text)
        return TM.interpolate(text, {'matrix': row, 'runner.os': 'Linux'})
    except TM.Unknown as error:
        raise Unsupported(str(error)) from None


def may_run(step, context):
    """The step's `if:` for a passing run (success() true, failure() false); a condition this
    offline evaluator cannot decide runs the step."""
    try:
        return TM.condition(step.get('if'), context)
    except TM.Unknown as error:
        if not isinstance(step.get('if'), str):
            raise Unsupported('unsupported condition DATA: %s' % error) from error
        return True


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
            try:
                if not may_run(job, context):
                    continue
            except Unsupported as error:
                raise Unsupported('%s: job %s: %s' % (CR.WORKFLOW, job_id, error)) from error
            for step in job.get('steps') or []:
                if 'run' not in step:
                    continue
                name = '%s: %s' % (job_id, step.get('name', '?'))
                try:
                    if not may_run(step, context):
                        continue
                    run_text = TM.expression_string(step['run'])
                except (TM.Unknown, Unsupported) as error:
                    raise Unsupported('%s: %s: %s' % (CR.WORKFLOW, name, error)) from error
                checks = sorted({s for s in CHECK.findall(run_text) if is_proof_fixture(tree, s)})
                if not checks:
                    continue
                env = {**(job.get('env') or {}), **(step.get('env') or {})}
                try:
                    run, env, error = render(run_text, row or {}), \
                        {k: render(v, row or {}) for k, v in env.items()}, None
                except Unsupported as unsupported:  # this unit fails, naming it; the others run
                    run, env = run_text, {}
                    error = '%s: %s: unsupported expression: %s' % (CR.WORKFLOW, name, unsupported)
                skipped = []
                if host != HOST:
                    run, skipped = strip_native(run)
                identity = [job_id, step.get('name'), run, env]
                if error:
                    identity.append(error)
                ident = json.dumps(identity, sort_keys=True)
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


# ---- running ----------------------------------------------------------------------------------

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
    for entry in ROOT.iterdir():
        (workspace / entry.name).symlink_to(entry)
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


def report(units, statuses, stats, path, top=20):
    """Print the `top` longest units (wall time, peak RSS, time by process kind); write every
    unit's row to PATH (JSON) when given."""
    # A unit's status is also in its statistics: a stopped run reports its finished units' too.
    rows = [{'name': u['name'], 'status': status, **(s or {})} for u, status, s in zip(units, statuses, stats)]
    if path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(rows, indent=1) + '\n')
    print('fixture-checks: longest units (wall s, peak RSS MiB, s by process kind):')
    for row in sorted(rows, key=lambda r: -r.get('elapsed_s', 0))[:top]:
        print('  %7.1f %6d  %-40s %s' % (row.get('elapsed_s', 0), row.get('peak_rss_kib', 0) // 1024,
                                         ' '.join('%s %d' % kv for kv in row.get('busy_s', {}).items()),
                                         row['name']))


SHARED = ROOT / '.lake/build/lib/lean'


def shared_outputs():
    """Identity (inode, size, mtime) of every root-package module the units import, its .olean.
    The full build compiles them before this phase; Lake has no build lock, so a unit that
    rebuilds one in place races every unit importing it (a missing .olean mid-write, compiled
    inputs changed during a kernel replay). Lake's trace and hash files are not compared: an
    up-to-date check may rewrite them."""
    found = {}
    for path in SHARED.rglob('*.olean'):
        try:
            info = path.lstat()
        except FileNotFoundError:
            continue
        found[str(path.relative_to(SHARED))] = (info.st_ino, info.st_size, info.st_mtime_ns)
    return found


def changed_outputs(before, after):
    return sorted(name for name in before.keys() | after.keys() if before.get(name) != after.get(name))


# ---- passes of unchanged inputs ---------------------------------------------------------------

SCHEMA = 'air2lean-fixture-pass-v1'
PASSES = Path(os.environ.get('AIR2LEAN_FIXTURE_PASSES') or Path.home() / '.cache/air2lean/fixture-checks/passes')
# CI (every workflow run: pull requests, main, nightly, release) never reuses or records a pass:
# its runs are the independent confirmation of the local ones.
IN_CI = bool(os.environ.get('GITHUB_ACTIONS') or os.environ.get('CI'))
# The Lake packages whose build outputs the units read (and the full build builds first).
PACKAGES = ('.', 'tests/roadmap', 'tests/diff')
# The environment a unit inherits is an input, every variable of it except these: the run's own
# scratch paths, admission, worker counts and pass store, which differ per run and select no
# result (the guard always sets ELAN_NO_OVERRIDE_NOTICE for the units); and the shell's and the
# terminal's session state (RUN_PREFIXES), which no check reads. A variable not named here is an
# input: a new one runs every unit again.
RUN_VARIABLES = ('AIR2LEAN_FIXTURE_REPLAY_CACHE', 'AIR2LEAN_TOOLCHAIN_RUNTIME_RUN', 'AIR2LEAN_GUARD_ADMISSION',
                 'AIR2LEAN_GUARD_MODE', 'AIR2LEAN_GUARD_PRIORITY', 'AIR2LEAN_JOBS', 'AIR2LEAN_MEM_MIB',
                 'AIR2LEAN_LOCK_WAIT', 'AIR2LEAN_BUILD_LOCK', 'AIR2LEAN_BUILD_MEM_MIB',
                 'AIR2LEAN_FIXTURE_PASSES', 'AIR2LEAN_FULL_BUILD_INNER', 'GITHUB_WORKSPACE',
                 'LEAN_NUM_THREADS', 'ELAN_NO_OVERRIDE_NOTICE', 'PWD', 'OLDPWD', 'SHLVL', '_')
RUN_PREFIXES = ('CLAUDE', 'AI_AGENT', 'WARP_', 'TERM', 'COLORTERM', 'SSH_', 'XPC_', '__CF', 'HIST')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def directory_records(path):
    """Every file below PATH (followed through aliases) with its content digest, and each alias's
    target (scripts/assumptions.py input_tree_records)."""
    if not path.exists():
        return None
    return [[str(p.relative_to(path)), link, content]
            for p, link, content in AS.input_tree_records(path, binaries=True)]


def run_inputs(tree):
    """Everything a unit can read that the run does not choose per unit: the content of every
    file of the checkout (tracked and untracked, `Tree`) and of the whole-tree generated files,
    every build output of the Lake packages the units read, the Lean toolchain, the interpreter,
    the host and the inherited environment (ENV_*). A unit's own key adds its CI step and its
    Zig compilers (`unit_key`)."""
    files = sorted(set(tree.files) | {f for f in GENERATED.paths(ROOT) if (ROOT / f).is_file()})
    return {
        'schema': SCHEMA,
        'checkout': [[f, AS.file_sha256(ROOT / f)] for f in files],
        'builds': {p: directory_records(ROOT / p / '.lake/build') for p in PACKAGES},
        'lean': AS.toolchain_runtime_sha256(Path(AS.lake_env('LEAN_SYSROOT')).resolve()),
        'tools': {name: path and [path, AS.file_sha256(Path(path)), subprocess.run(
                      [path, '--version'], capture_output=True, text=True).stdout.strip()]
                  for name in ('python3', 'bash', 'git') for path in [shutil.which(name)]},
        'host': [platform.platform(), platform.machine(), HOST],
        'environment': {k: v for k, v in os.environ.items()
                        if k not in RUN_VARIABLES and not k.startswith(RUN_PREFIXES)},
    }


def unit_key(unit, run_digest, compilers):
    """The key of UNIT's pass: the run's inputs (`run_inputs`, as RUN_DIGEST), the CI step it is
    (its rendered script, environment and the native runs it leaves out on this host) and the
    content of each Zig compiler it names (COMPILERS: (kind, version) -> digest)."""
    return digest([SCHEMA, run_digest, unit['name'], unit['run'], unit['env'], unit['skipped'], unit['error'],
                   [[kind, version, compilers[kind, version]]
                    for kind, versions in sorted(unit['toolchains'].items()) for version in versions]])


def compiler_digests(units):
    """(kind, version) -> digest of the content of that Zig compiler's installation; None when this
    host cannot provide it (its unit fails, and a failing unit records no pass)."""
    found = {}
    for kind, version in sorted({(k, v) for u in units for k, vs in u['toolchains'].items() for v in vs}):
        try:
            zig = resolve(kind, version)
        except Unavailable:
            found[kind, version] = None
            continue
        found[kind, version] = digest(directory_records(zig.parent.parent if kind == 'patched' else zig.parent))
    return found


def recorded(key):
    try:
        return json.loads((PASSES / (key + '.json')).read_text()).get('key') == key
    except (OSError, ValueError, AttributeError):
        return False


def record(key, unit, elapsed):
    PASSES.mkdir(parents=True, exist_ok=True)
    AS.write_report(PASSES / (key + '.json'), {'key': key, 'unit': unit['name'], 'elapsed_s': elapsed,
                                                'head': AS.git_revision(ROOT)['head'],
                                                'recorded': time.strftime('%Y-%m-%dT%H:%M:%S%z')})


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--list', action='store_true', help='print the units, their checks and toolchains')
    parser.add_argument('--prepare', action='store_true', help='resolve the units\' toolchains only')
    parser.add_argument('--only', action='append', default=[], help='units whose name or checks contain TEXT')
    parser.add_argument('--jobs', type=int)
    # A unit's peak: three at once reached 10.4 GiB under the full build's 11000 MiB guard.
    parser.add_argument('--mem-mib', type=int, default=5000, help='peak memory of one unit (default 5000)')
    parser.add_argument('--logs', type=Path, help='keep every unit\'s log here')
    parser.add_argument('--report', type=Path, help='write each unit\'s status, wall time, peak RSS and '
                        'wall time by process kind (scripts/par.py) to this JSON file')
    parser.add_argument('--rerun', action='store_true', help='run every unit, also one with a recorded pass')
    parser.add_argument('--pending', action='store_true',
                        help='exit 0 when every unit has a recorded pass of its inputs (nothing to run), else 1')
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
    if a.prepare:
        for kind, version in sorted({(k, v) for u in units for k, vs in u['toolchains'].items() for v in vs}):
            try:
                print('fixture-checks: %s Zig %s: %s' % (kind, version, resolve(kind, version)))
            except Unavailable as error:  # the units that need it fail in the run, naming it
                print('fixture-checks: %s' % error, file=sys.stderr)
        return 0
    failed, keys, inputs = [], {}, None
    if units and not IN_CI:
        inputs = digest(run_inputs(tree))
        compilers = compiler_digests(units)
        keys = {u['name']: unit_key(u, inputs, compilers) for u in units}
    reused = [u for u in units if inputs and not a.rerun and recorded(keys[u['name']])]
    for u in reused:
        print('fixture-checks: %s: a pass of the same inputs is recorded (%s)' % (u['name'], keys[u['name']][:16]))
    units = [u for u in units if u not in reused]
    if a.pending:
        print('fixture-checks: %d units to run, %d with a recorded pass' % (len(units), len(reused)))
        return 1 if units else 0
    if units:
        scratch = Path(tempfile.mkdtemp(prefix='air2lean-fixture-checks.'))
        logs = a.logs or Path(tempfile.mkdtemp(prefix='air2lean-fixture-logs.'))
        logs.mkdir(parents=True, exist_ok=True)
        names = {u['name']: '%02d-%s' % (i, par.safe_name(u['name'])[:80]) for i, u in enumerate(units)}
        try:
            jobs = []
            for u in units:
                command, env = stage(u, scratch / names[u['name']])
                if env is not None:  # one build: the units' audits share their kernel replays
                    env['AIR2LEAN_FIXTURE_REPLAY_CACHE'] = str(scratch / 'kernel-replay.json')
                jobs.append(par.Job(names[u['name']], command, cwd=str(ROOT), env=env))
            workers = par.workers(a.jobs, a.mem_mib, len(jobs))
            print('fixture-checks: running %d units, %d at once' % (len(units), workers), flush=True)
            stats, statuses = [], None
            before = shared_outputs()
            try:
                with open(os.devnull, 'wb') as null:
                    statuses = par.run(jobs, workers, out=null, err=null, log_dir=logs, stats=stats)
            finally:  # also the finished units of a stopped run (a guard's timeout)
                report(units, statuses or [None] * len(units), stats, a.report)
            if changed := changed_outputs(before, shared_outputs()):
                failed.append('the root package\'s build outputs changed while the units ran (a unit '
                              'built root modules, racing the units that read them): '
                              + ', '.join(changed[:20]) + (' ...' if len(changed) > 20 else ''))
            # A pass is recorded only for the inputs the whole run saw: unchanged from its start
            # to its end (a unit that changed an input, or an edit during the run, records none).
            elif inputs is None:  # CI: nothing is recorded
                pass
            elif digest(run_inputs(Tree())) == inputs:
                for u, status, s in zip(units, statuses, stats):  # stats: one per job, in order
                    if status == 0:
                        record(keys[u['name']], u, (s or {}).get('elapsed_s'))
            else:
                print('fixture-checks: the inputs changed during the run: no pass is recorded')
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
        for u, status in zip(units, statuses):
            if status != 0:
                log = logs / (names[u['name']] + '.log')
                tail = log.read_text(errors='replace').strip().splitlines()[-15:] if log.is_file() else []
                failed.append('%s (exit %d, log %s)%s' % (u['name'], status, log,
                                                          ''.join('\n    ' + l for l in tail)))
        if not failed and not a.logs:
            shutil.rmtree(logs, ignore_errors=True)
    skipped = sum(len(u['skipped']) for u in units)
    print('fixture-checks: %d units (%d checks) run, %d failed, %d with a recorded pass of the same inputs'
          % (len(units), len({c for u in units for c in u['checks']}), len(failed), len(reused)))
    if skipped:
        print('fixture-checks: %d native runs need their CI host, not %s (--list names them; '
              'scripts/local-ci.sh part PART runs them)' % (skipped, HOST))
    for f in failed:
        print('fixture-checks: FAILED ' + f, file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
