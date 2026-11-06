#!/usr/bin/env python3
"""Every proof-fixture check that CI runs, run locally (scripts/full-build.sh, docs/ci.md#full-build).

    scripts/fixture-checks.sh [--logs DIR] [--only TEXT]...   (guarded; full-build.sh)
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

Units run in parallel (scripts/par.py: --jobs, else AIR2LEAN_JOBS), in the checkout, after the
full build's Lean phases: the longest first, each admitted while the memory requests of the
running units fit in the guard's budget (`schedule`; from the last runs' wall times and peaks,
`hints_path`; --mem-mib for a unit not measured yet).
Those measurements decide only order and admission. Every unit runs on every invocation:
no result is reused across runs until a sound input tracer exists (maintainer decision on #443,
2026-10-19; docs/ci.md#full-build). A key over the files a unit's text names missed every input
reached by a path built in code (a stale pass of tests/roadmap/callbacks after an edit of
tests/roadmap/asm-effects).

The units of one run audit one build, so their `fixtures.py audit`s share one kernel-replay cache
(AIR2LEAN_FIXTURE_REPLAY_CACHE, a file in the run's scratch directory, removed with it): a
Lake-built module that one audit replayed is not replayed again in this run
(scripts/assumptions.py `kernel_replay`). They also share one digest of the Lean toolchain's
runtime, hashed when the run starts and again when it ends (a change fails the run;
assumptions.py `runtime_run`). Before the units start, every library of the proof-fixture
package (tests/roadmap/lakefile.toml, `scripts/fixtures.py build`) and the compiled assurance
extractor (assumptions.py `prepared_tool`) are built (`prepare_shared`): no unit builds a module
of the root or the fixture package, and a run in which one changed fails. Nothing outlives the run.

`--prepare` resolves the toolchains of the units that will run (a patched-compiler miss builds it
under its own scripts/build-guard.py); scripts/full-build.sh calls it before its guarded run.
Exit status: 0 when every unit passed, else 1 with each failure's log tail.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import par  # noqa: E402
import assumptions  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CR = _load('air2lean_ci_reuse', 'scripts/ci-reuse.py')
TM = CR.TM
CAS = _load('air2lean_cas', 'scripts/cas.py')
GUARD = _load('air2lean_build_guard', 'scripts/build-guard.py')
PEAKS = _load('air2lean_lean_peaks', 'scripts/lean-peaks.py')

WS, TMP = '@WORKSPACE@', '@RUNNER_TEMP@'  # placeholders for the unit's scratch paths
CHECK = re.compile(r'(?<![\w/.-])(tests/[\w/.-]+/check\.sh)\b')
ARG = r'(?:[ \t]+(?:\\\n[ \t]*)?[^\s;&|()<>]+)'
NATIVE = re.compile(r'(?<![\w/.:-])(?:bash[ \t]+)?tests/[\w/.-]+\.sh%s*?[ \t]+--native[\w-]*%s*' % (ARG, ARG))
# A native row's runner (AIR2LEAN_<ARCH>_RUN, a command prefix; empty: the host): `_stage` fails a
# unit whose runner is not installed, since a check script may send the runner's errors to a file.
RUNNER = re.compile(r'AIR2LEAN_\w+_RUN')
# Scheduling (`schedule`): a request is the largest of a unit's last HINT_RUNS sampled peaks times
# MEM_MARGIN (sampling every 2 s misses short spikes), at least MEM_FLOOR_MIB. In an elastic
# admission (scripts/fixture-checks.sh, scripts/full-build.sh) each unit is a sub-admission of
# build-guard charged its request (`admitted`); elsewhere the requests of the running units stay
# within MEM_SHARE of the guard's limit (AIR2LEAN_MEM_MIB), which the guard enforces on their sum.
HINT_RUNS, MEM_MARGIN, MEM_FLOOR_MIB, MEM_SHARE = 5, 1.5, 1024, 0.85
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
    if unit['runner'] == HOST:  # its native runs execute here, each through its row's runner
        for name in sorted(n for n in unit['env'] if RUNNER.fullmatch(n) and env[n].strip()):
            if not shutil.which(env[name].split()[0], path=env['PATH']):
                raise Unavailable('missing prerequisite: %s=%s is not installed '
                                  '(scripts/doctor.sh native-runners)' % (name, env[name]))
    # Every attempt starts from the staged temp, as a CI job starts from a fresh runner.temp:
    # build-guard runs a unit stopped at its charge again with the same command
    # (`retries_at_declared`), and the stopped attempt's outputs there are no input of the rerun
    # (spawn-failure's evidence directory must be empty). The staged entries are the host-zig links.
    reset = 'find %s -mindepth 1 -maxdepth 1 ! -name "host-zig-*" -exec rm -rf -- {} +\n' % shlex.quote(str(temp))
    return ['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', reset + place(unit['run'])], env


def elastic_grant():
    """The enclosing guard's admission when it is elastic (build-guard.py --elastic: the units'
    guard, scripts/fixture-checks.sh), else None."""
    grant = GUARD.read_grant()
    return grant if grant and grant.get('elastic') and isinstance(grant.get('lock'), str) else None


def admitted(command, request_mib, grant):
    """A unit's command as a sub-admission of the elastic guard: it holds its own slots, charged
    its request, while it runs, and runs again at build-guard's PROCESS_MIB if it outgrows them.
    It keeps the units' guard's jobs and Lean threads (which the sub-admission sets again), samples
    as often as the hints were measured (`write_hints`)."""
    return [sys.executable, '-B', str(ROOT / 'scripts/build-guard.py'),
            *GUARD.part_options(request_mib, grant['lock'], 2), '--cwd', str(ROOT),
            '--jobs', os.environ.get('AIR2LEAN_JOBS') or '1',
            '--lean-threads', os.environ.get('LEAN_NUM_THREADS') or '1', '--', *command]


def lean_processes_env(grant):
    """The environment of the proof-fixture package's build in an elastic admission: each of its
    Lean processes is a sub-admission charged its module's measured peak (build-guard.py
    --lean-processes; the package holds the largest modules, 9 GB and more). Only that build:
    the assurance tools refuse a LEAN_SYSROOT overlay."""
    sysroot = subprocess.run(['lean', '--print-prefix'], cwd=ROOT, check=True, capture_output=True,
                             text=True).stdout.strip()
    return os.environ | GUARD.lean_processes_env(sysroot, Path(grant['lock']))


def hints_path():
    """The last runs' per-unit measurements, one file per machine (every worktree runs the same
    units, and a gate's worktree is fresh): $AIR2LEAN_FIXTURE_SCHEDULE, else beside the build
    lock in ~/.cache/air2lean. It holds no result, so it is not in the artifact cache."""
    path = os.environ.get('AIR2LEAN_FIXTURE_SCHEDULE')
    return Path(path) if path else Path.home() / '.cache' / 'air2lean' / 'fixture-checks' / 'schedule.json'


def lean_threads():
    """The Lean processes each unit's Lake runs at once (LEAN_NUM_THREADS, set by the guard)."""
    text = os.environ.get('LEAN_NUM_THREADS', '')
    return int(text) if text.isdigit() and int(text) > 0 else 1


def _hint(entry):
    """A well-formed measurement, else None (the file is a cache: a bad entry is unmeasured)."""
    number = lambda x: isinstance(x, (int, float)) and not isinstance(x, bool) and x >= 0
    if (isinstance(entry, dict) and number(entry.get('elapsed_s'))
            and isinstance(entry.get('peak_rss_kib'), list) and all(map(number, entry['peak_rss_kib']))
            and isinstance(entry.get('lean_threads'), int) and entry['lean_threads'] > 0):
        return entry
    return None


def read_hints():
    try:
        data = json.loads(hints_path().read_text())
    except (OSError, ValueError):
        return {}
    return {k: v for k, v in data.items() if _hint(v)} if isinstance(data, dict) else {}


def write_hints(units, stats):
    """Record each measured unit's wall time and its peaks of the last HINT_RUNS runs with this
    run's Lean thread count (peaks measured with another count are dropped). A file that cannot
    be written only loses the measurements: a warning, never a failed run."""
    hints, threads = read_hints(), lean_threads()
    for u, s in zip(units, stats):
        if s:
            old = hints.get(u['name'])
            peaks = old['peak_rss_kib'] if old and old['lean_threads'] == threads else []
            hints[u['name']] = {'elapsed_s': s['elapsed_s'], 'lean_threads': threads,
                                'peak_rss_kib': ([s['peak_rss_kib']] + peaks)[:HINT_RUNS]}
    path, written = hints_path(), None
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile('w', dir=path.parent, delete=False) as handle:
            written = handle.name
            json.dump(hints, handle, indent=1, sort_keys=True)
        os.replace(written, path)
    except OSError as error:
        print('fixture-checks: the schedule was not recorded: %s' % error, file=sys.stderr)
        if written:
            Path(written).unlink(missing_ok=True)


def schedule(units, mem_mib, elastic=False):
    """(start order, memory requests in MiB): the longest units first by their last wall time, an
    unmeasured one before all; a request is the largest recent peak with a margin (MEM_MARGIN,
    at least MEM_FLOOR_MIB), scaled up by the ratio of Lean threads when this run has more than
    the measured one. An unmeasured unit requests `mem_mib`; in an elastic admission, where its
    request is its limit and one that outgrows it runs again at PROCESS_MIB (`admitted`), it
    requests the typical request of every unit this machine measured, selected or not
    (lean-peaks.py `typical`, the quantile a Lean module never measured is charged by), at most
    PROCESS_MIB. Only order and admission depend on these measurements, never a unit's result."""
    hints, threads = read_hints(), lean_threads()

    def request(hint):
        if not hint or not hint['peak_rss_kib']:
            return None
        return max(MEM_FLOOR_MIB, int(max(hint['peak_rss_kib']) / 1024 * MEM_MARGIN
                                      * max(1, threads / hint['lean_threads'])))

    known = [hints.get(u['name']) for u in units]
    order = sorted(range(len(units)), key=lambda i: -(known[i]['elapsed_s'] if known[i] else float('inf')))
    unmeasured = mem_mib
    if elastic:
        typical = PEAKS.typical(filter(None, map(request, hints.values())))
        unmeasured = min(GUARD.PROCESS_MIB, typical or GUARD.PROCESS_MIB)
    return order, [request(h) or unmeasured for h in known]


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


# The compiled modules the units import: the root package's and the proof-fixture package's
# (tests/roadmap/lakefile.toml), whose every library `FIXTURE_BUILD` builds before the units.
SHARED = (ROOT / '.lake/build/lib/lean', ROOT / 'tests/roadmap/.lake/build/lib/lean')
FIXTURE_BUILD = [sys.executable, '-B', str(ROOT / 'scripts/fixtures.py'), 'build']


def log_tail(log: Path, lines=15):
    """The last lines of a failure's log, indented, for the failure message (the log may not
    outlive the run)."""
    tail = log.read_text(errors='replace').strip().splitlines()[-lines:] if log.is_file() else []
    return ''.join('\n    ' + line for line in tail)


def prepare_shared(log: Path):
    """Build what the units share before any of them starts, so no unit builds it under the
    others: every library of the proof-fixture package (a unit's own `fixtures.py build` is then
    an up-to-date check), and the compiled assurance extractor (assumptions.py `prepared_tool`).
    Returns the failure, or None."""
    try:
        grant = elastic_grant()
        env = lean_processes_env(grant) if grant else None
        with open(log, 'wb') as out:
            status = subprocess.run(FIXTURE_BUILD, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return 'the proof-fixture package: %s' % error
    if status:
        return 'the proof-fixture package: fixtures.py build exited %d (log %s)%s' % (status, log, log_tail(log))
    try:
        with assumptions.prepared_tool():
            pass
    except (OSError, ValueError, RuntimeError) as error:
        return 'the assurance extractor: %s' % error
    return None


def shared_outputs():
    """Identity (inode, size, mtime) of every compiled file of the shared packages (`SHARED`):
    each module's .olean and its companions, the files an audit binds (assumptions.py
    `COMPILED_SUFFIXES`, `lean_path_binding`). They are built before the units (`prepare_shared`);
    Lake has no build lock, so a unit that rebuilds or deletes one in place races every unit that
    reads the package (a missing .olean mid-walk, "compiler-owned Unit imported inputs changed").
    Lake's trace and hash files are not compared: an up-to-date check may rewrite them."""
    found = {}
    for shared in SHARED:
        for path in (p for suffix in assumptions.COMPILED_SUFFIXES for p in shared.rglob('*' + suffix)):
            try:
                info = path.lstat()
            except FileNotFoundError:
                continue
            found[os.path.relpath(path, ROOT)] = (info.st_ino, info.st_size, info.st_mtime_ns)
    return found


def changed_outputs(before, after):
    return sorted(name for name in before.keys() | after.keys() if before.get(name) != after.get(name))


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
    failed = []
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
            grant = elastic_grant()
            order, requests = schedule(units, a.mem_mib, elastic=bool(grant))
            for job, request in zip(jobs, requests):
                if grant:  # each unit admitted by build-guard, beside every other workload
                    job.argv = admitted(job.argv, request, grant)
                else:
                    job.mem_mib = request
            workers = par.workers(a.jobs, None, len(jobs))
            budget = None if grant else int(par.memory_budget_mib() * MEM_SHARE)
            print('fixture-checks: running %d units, up to %d at once, %s'
                  % (len(units), workers, 'each its own sub-admission' if grant else 'within %d MiB' % budget),
                  flush=True)
            stats, statuses, before = [], None, None
            try:
                # The units' audits share one toolchain-runtime digest, hashed again when they end
                # (assumptions.runtime_run): a toolchain changed during the run fails it.
                with assumptions.runtime_run(), open(os.devnull, 'wb') as null:
                    # They also share the proof-fixture package and the compiled extractor, built
                    # here, before the units, so no unit builds them under the units that read them.
                    if error := prepare_shared(logs / 'shared-build.log'):
                        failed.append(error)
                    else:
                        before = shared_outputs()
                        for job in jobs:
                            if job.env is not None:
                                job.env[assumptions.RUNTIME_RUN] = os.environ[assumptions.RUNTIME_RUN]
                        try:
                            statuses = par.run(jobs, workers, out=null, err=null, log_dir=logs, stats=stats,
                                               order=order, mem_budget_mib=budget)
                        except (OSError, ValueError) as error:  # a bad order, a job that cannot spawn
                            failed.append('the run: %s' % error)
            except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
                failed.append('the toolchain runtime: %s' % error)
            finally:  # also the finished units of a stopped run (a guard's timeout)
                report(units, statuses or [None] * len(units), stats, a.report)
                write_hints(units, stats)
            if before is not None and (changed := changed_outputs(before, shared_outputs())):
                failed.append('the shared build outputs changed while the units ran (a unit built '
                              'modules of the root or the proof-fixture package, racing the units '
                              'that read them): '
                              + ', '.join(changed[:20]) + (' ...' if len(changed) > 20 else ''))
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
        for u, status in zip(units, statuses or []):  # none: the run did not start
            if status != 0:
                log = logs / (names[u['name']] + '.log')
                failed.append('%s (exit %d, log %s)%s' % (u['name'], status, log, log_tail(log)))
        if not failed and not a.logs:
            shutil.rmtree(logs, ignore_errors=True)
    skipped = sum(len(u['skipped']) for u in units)
    print('fixture-checks: %d units (%d checks) run, %d failed'
          % (len(units), len({c for u in units for c in u['checks']}), len(failed)))
    if skipped:
        print('fixture-checks: %d native runs need their CI host, not %s (--list names them; '
              'scripts/local-ci.sh part PART runs them)' % (skipped, HOST))
    for f in failed:
        print('fixture-checks: FAILED ' + f, file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
