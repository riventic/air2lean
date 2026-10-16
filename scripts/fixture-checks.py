#!/usr/bin/env python3
"""Every proof-fixture check and Python test that CI runs, run locally (scripts/full-build.sh,
docs/ci.md#full-build).

    scripts/fixture-checks.sh [--logs DIR] [--base REF] [--only TEXT]...   (guarded; full-build.sh)
    python3 -B scripts/fixture-checks.py [--jobs N] [--mem-mib M] [--base REF] [--only TEXT]... [--logs DIR]
    python3 -B scripts/fixture-checks.py --list [--only TEXT]...
    python3 -B scripts/fixture-checks.py --prepare [--only TEXT]...

The checks are derived from the workflow, not listed: a *proof-fixture check* is a
`tests/**/check.sh` whose directory holds tracked `.lean` files, and its *unit* is the CI step
that runs it (the whole `run:` script, with its `env:`), for every job row the step's `if:` may
run for (scripts/ci-reuse.py's `may_run`). The step is rendered for that row (`matrix.*`,
`github.workspace`, `runner.temp`); rows whose rendered step is the same run it once. So a new
check is covered by adding it to CI, and a step's own prerequisites, sibling gates and mode
switches (`check.sh --native`, `--export DIR`, an `if` on the version) run as CI runs them.
A *Python test* is a command line of another step (without its redirections and pipes) that runs
a tracked `tests/**/*.py` with `python3`, or `python3 -m unittest discover -s` a `tests/`
directory; its unit is that command alone with the step's `env:`. An offline one (only literal
arguments) runs; one that takes an argument from the runner (`$RUNNER_TEMP/...` an earlier step
wrote, `$PWD/.lake/build/bin/air2lean`, the workspace) or needs a toolchain this layout cannot
provide is *left out*: `--list` and every run name it with the reason.

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
once), after the full build's Lean phases, each traced (scripts/ci-reuse.py `trace`,
docs/ci.md#traced-records): in a fresh repository of the checkout's content with copy-on-write
clones of the Lake builds and the generated files, under a sandbox that hides everything outside
but keyed roots and content-addressed caches, so that its record covers what it read. Its
pre-key is what it runs (`identity`: the rendered step and environment, this script's staging
code between the `key-relevant` markers, the toolchains it links) with ci-reuse's environment,
outside identities and machinery. A unit is unchanged when one of its records matches the
checkout: a docs file, a generated inventory or another fixture's sources rerun it only when it
read them.

`--prepare` resolves the toolchains of the units that will run (a patched-compiler miss builds it
under its own scripts/build-guard.py); scripts/full-build.sh calls it before its guarded run.
Exit status: 0 when every unit passed or was unchanged, else 1 with each failure's log tail.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
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


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CR = _load('air2lean_ci_reuse', 'scripts/ci-reuse.py')
TM = CR.TM
CAS = _load('air2lean_cas', 'scripts/cas.py')

SCHEMA = 3
WS, TMP = '@WORKSPACE@', '@RUNNER_TEMP@'  # placeholders: the key does not depend on scratch paths
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
        self.file_set = set(self.files)
        self.dirs = {str(Path(f).parent) for f in self.files}
        self.dirs |= {str(p) for d in list(self.dirs) for p in Path(d).parents if str(p) != '.'}

    def under(self, d):
        prefix = d.rstrip('/') + '/'
        return [f for f in self.files if f.startswith(prefix)]


def is_proof_fixture(tree, script):
    return any(f.endswith('.lean') for f in tree.under(str(Path(script).parent)))


def proof_fixtures(tree, run):
    return sorted({s for s in CHECK.findall(run) if is_proof_fixture(tree, s)})


def python_tests(tree, run):
    """[(command, test, reason)] of the Python tests RUN runs (see the module docstring): each command
    line, without its redirections and pipes, that runs a tracked tests/ Python file with python3
    or `python3 -m unittest discover -s` a tests/ directory. REASON is None for an offline test
    (literal arguments), else why it is left out (an argument from the runner)."""
    out = []
    for line in re.sub(r'\\\n', ' ', run).splitlines():
        lexer = shlex.shlex(line, posix=True, punctuation_chars=True)
        lexer.whitespace_split = True
        try:
            tokens = list(lexer)
        except ValueError:
            continue
        words = []
        for token in tokens:
            if set(token) <= set('|&;<>()'):
                if words and words[-1].isdigit():  # `2>&1`
                    words.pop()
                break
            words.append(token)
        # The step's working directory is the workspace (github.workspace) in CI and in the layout.
        command = [re.sub(r'\$(?:PWD|\{PWD\}|GITHUB_WORKSPACE|\{GITHUB_WORKSPACE\})(?![\w])', WS, w) for w in words]
        words = list(command)
        while words and re.fullmatch(r'[A-Za-z_]\w*=.*', words[0]):
            words.pop(0)
        if words[:1] not in (['python3'], ['python']):
            continue
        args = words[1:]
        while args and args[0].startswith('-') and args[0] != '-m':
            args.pop(0)
        if args[:3] == ['-m', 'unittest', 'discover'] and '-s' in args[3:-1]:
            test = args[args.index('-s') + 1].rstrip('/')
            if test not in tree.dirs:
                continue
        elif args and args[0] in tree.file_set and args[0].endswith('.py'):
            test = args[0]
        else:
            continue
        if not test.startswith('tests/'):
            continue
        runner = [w for w in command if '$' in w or '`' in w or TMP in w]
        out.append((shlex.join(command), test, 'takes %s from the runner' % runner[0] if runner else None))
    return out


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
    """[unit]: one per distinct rendered CI step that runs a proof-fixture check, and one per
    distinct Python test command of another step (`left_out`: why it does not run here)."""
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
                checks = proof_fixtures(tree, step['run'])
                if not checks and not python_tests(tree, step['run']):
                    continue
                name = '%s: %s' % (job_id, step.get('name', '?'))
                env = {**(job.get('env') or {}), **(step.get('env') or {})}
                try:
                    run, env, error = render(step['run'], row or {}), \
                        {k: render(v, row or {}) for k, v in env.items()}, None
                except Unsupported as unsupported:  # this unit fails, naming it; the others run
                    run, error = step['run'], 'unsupported expression: %s' % unsupported
                if checks:  # the whole step, as CI runs it
                    skipped = []
                    if host != HOST:
                        run, skipped = strip_native(run)
                    found = [(name, run, checks, skipped, None)]
                else:  # each Python test command on its own; an unrenderable step's are left out
                    found = [('%s: %s' % (name, command), command, [test], [], error or reason)
                             for command, test, reason in python_tests(tree, run)]
                for unit_name, unit_run, unit_checks, skipped, left_out in found:
                    ident = json.dumps([job_id, step.get('name'), unit_run, env], sort_keys=True)
                    if ident in units:
                        units[ident]['rows'].append(CR.part_id(job_id, row))
                        continue
                    units[ident] = {'name': unit_name, 'job': job_id, 'rows': [CR.part_id(job_id, row)],
                                    'zig': (row or {}).get('zig') or default, 'checks': unit_checks,
                                    'run': unit_run, 'env': env, 'runner': host, 'skipped': skipped,
                                    'error': error if checks else None, 'left_out': left_out}
    out = list(units.values())
    shared = {u['name'] for u in out if sum(v['name'] == u['name'] for v in out) > 1}
    for unit in out:
        try:
            unit['toolchains'] = toolchains(unit)
        except Unsupported as unsupported:
            unit['toolchains'] = {'patched': [], 'stock': []}
            if proof_fixtures(tree, unit['run']):
                unit['error'] = unit['error'] or str(unsupported)
            else:  # a Python test that needs a toolchain this host cannot provide in CI's layout
                unit['left_out'] = unit['left_out'] or str(unsupported)
        if unit['name'] in shared:
            unit['name'] += ' [%s]' % ', '.join(unit['rows'])
    seen = {}
    for unit in sorted(out, key=lambda u: u['name']):  # a name is the unit's identity: unique
        seen[unit['name']] = seen.get(unit['name'], 0) + 1
        if seen[unit['name']] > 1:
            unit['name'] += ' #%d' % seen[unit['name']]
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
# From here to the `key-relevant: end` marker: how a unit is staged in CI's layout and what of
# that its pre-key names; the text is part of every pre-key (RUNNER), so a change here reruns
# every unit. How it runs and what its record covers is scripts/ci-reuse.py's (its own marker).


class Unavailable(Exception):
    pass


def resolve(kind, version):
    """bin/zig of a toolchain; a patched-compiler miss builds it (scripts/build-guard.py)."""
    try:
        return Path(CAS.zig_air(ROOT, version) if kind == 'patched' else CAS.host_zig(version))
    except CAS.CasError as error:
        raise Unavailable('cannot provide the %s Zig %s: %s' % (kind, version, error.args[0])) from None


def identity(unit):
    """What the unit runs, for its pre-key (scripts/ci-reuse.py adds the environment it keeps, the
    identities outside the checkout and its machinery): the rendered step and environment, this
    staging code, and the toolchains it links: a stock Zig by its path (its directory is a keyed
    root), a patched compiler also by the zig-patch/ inputs it is built from (its CAS entry)."""
    return {'schema': SCHEMA, 'runner': RUNNER, 'run': unit['run'], 'env': unit['env'],
            'tools': {k: {v: _tool(k, v) for v in vs} for k, vs in unit['toolchains'].items()},
            'path-zig': _tool('stock', unit['zig'])}


@functools.cache
def _tool(kind, version):
    try:
        zig = str(CAS.host_zig(version))
        return (zig, CAS.zig_patch_inputs(ROOT, version)) if kind == 'patched' else zig
    except CAS.CasError as error:
        return 'unavailable: %s' % error.args[0]


def stage(unit, scratch, base):
    """(argv, env, extra) of the unit: the CI layout under SCRATCH over the environment BASE, the
    step's environment, the toolchain directories it may read outside the caches (EXTRA); a unit
    whose toolchain this host cannot provide becomes a command that fails with the reason."""
    try:
        if unit['error']:
            raise Unavailable(unit['error'])
        return _stage(unit, scratch, base)
    except Unavailable as error:
        return ['sh', '-c', 'echo "fixture-checks: $1" >&2; exit 1', 'sh', str(error)], None, []


def _stage(unit, scratch, base):
    workspace, temp = scratch / 'workspace', scratch / 'temp'
    workspace.mkdir(parents=True)
    temp.mkdir()
    for entry in ROOT.iterdir():  # the entries of the unit's tree (traced), made at its start
        if entry.name not in CR.NOISE:
            (workspace / entry.name).symlink_to(scratch / 'tree' / entry.name)
    extra = []
    for version in unit['toolchains']['patched']:
        extra.append(resolve('patched', version).parent.parent)
        (workspace / ('zig-air-' + version)).symlink_to(extra[-1])
    for version in unit['toolchains']['stock']:
        (temp / ('host-zig-' + version)).symlink_to(resolve('stock', version).parent)
    env = dict(base, RUNNER_TEMP=str(temp), GITHUB_WORKSPACE=str(workspace))
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
    return ['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', place(unit['run'])], env, extra


def staged_job(unit, scratch, name, commit, outside):
    """par.Job of the unit: its staged command traced (scripts/ci-reuse.py trace) in its own tree
    SCRATCH/tree, the trace going to SCRATCH/trace.json; a unit that cannot be staged fails,
    naming why."""
    command, env, extra = stage(unit, scratch, outside.environment()[0])
    if env is None:
        return par.Job(name, command, cwd=str(ROOT))
    spec = scratch / 'spec.json'
    spec.write_text(json.dumps({
        'root': str(ROOT), 'argv': command, 'env': env, 'dest': str(scratch / 'tree'), 'private': str(scratch),
        'commit': commit, 'clone': CR.cloned_entries(ROOT), 'trace': str(scratch / 'trace.json'),
        'profile': outside.profile(scratch, extra) if outside.available() else None}))
    return par.Job(name, [sys.executable, '-B', str(ROOT / 'scripts/ci-reuse.py'), 'trace', str(spec)], cwd=str(ROOT))

# ---- key-relevant: end ------------------------------------------------------------------------


def _runner():
    text = Path(__file__).read_text()
    return hashlib.sha256(text[text.index('# ---- key-relevant: begin'):
                               text.index('# ---- key-relevant: end')].encode()).hexdigest()


RUNNER = _runner()


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
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
    found = [u for u in discover(tree)
             if not a.only or any(t in u['name'] or any(t in c for c in u['checks']) for t in a.only)]
    units, left_out = [u for u in found if not u['left_out']], [u for u in found if u['left_out']]
    if a.list:
        for u in found:
            print('%s\n    checks: %s\n    toolchains: %s' % (
                u['name'], ' '.join(u['checks']),
                ', '.join('%s %s' % (k, v) for k, vs in u['toolchains'].items() for v in vs) or 'none'))
            if u['left_out']:
                print('    left out: %s' % u['left_out'])
            elif u['error']:
                print('    fails: %s' % u['error'])
            for s in u['skipped']:
                print('    not on %s (needs %s): %s' % (HOST, u['runner'], s))
        print('fixture-checks: %d units, %d checks; %d Python tests left out' % (
            len(units), len({c for u in units for c in u['checks']}), len(left_out)))
        return 0
    outside, commit = CR.Outside(ROOT), CR.snapshot(ROOT)
    records = CR.Records(ROOT, commit)
    prekeys = {u['name']: records.prekey(outside, identity(u)) for u in units} if outside.available() else {}
    if a.base and prekeys:
        changed = set(CR.changed_files(ROOT, a.base))
        if CR.WORKFLOW not in changed:  # a changed workflow can change any unit: keep them all
            # A unit with no record yet is kept; one is affected when a file it read changed.
            units = [u for u in units if not (entries := records.entries(prekeys[u['name']]))
                     or any(changed & set(json.loads((e / 'record.json').read_text())) for e in entries)]
    todo = [u for u in units if not (prekeys and records.lookup(prekeys[u['name']]))]
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
    failed, notes = [], []
    if not prekeys:
        notes.append('no unit is reused or recorded: the traced runs\' sandbox does not apply here '
                     '(docs/ci.md#traced-records)')
    if todo:
        scratch = Path(tempfile.mkdtemp(prefix='air2lean-fixture-checks.'))
        logs = a.logs or Path(tempfile.mkdtemp(prefix='air2lean-fixture-logs.'))
        logs.mkdir(parents=True, exist_ok=True)
        names = {u['name']: '%02d-%s' % (i, par.safe_name(u['name'])[:80]) for i, u in enumerate(todo)}
        try:
            jobs = [staged_job(u, scratch / names[u['name']], names[u['name']], commit, outside) for u in todo]
            print('fixture-checks: running %d of %d units' % (len(todo), len(units)), flush=True)
            with open(os.devnull, 'wb') as null:
                statuses = par.run(jobs, par.workers(a.jobs, a.mem_mib, len(jobs)), out=null, err=null,
                                   log_dir=logs)
            passes = [(u, json.loads(trace.read_text())) for u, status in zip(todo, statuses)
                      if status == 0 and (trace := scratch / names[u['name']] / 'trace.json').is_file()]
            if prekeys and outside.identity(fresh=True) != outside.identity():
                notes.append('nothing recorded: a root outside the checkout changed during the run')
            elif prekeys:
                for u, trace in passes:
                    if trace['record'] is not None:
                        records.publish(prekeys[u['name']], trace['record'], {'unit': u['name']})
                    else:
                        notes.append('%s: not recorded (%s)' % (u['name'], trace['reason']))
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
    if left_out:
        print('fixture-checks: %d Python tests take runner inputs and are left out (--list names them)'
              % len(left_out))
    for note in notes:
        print('fixture-checks: ' + note)
    for f in failed:
        print('fixture-checks: FAILED ' + f, file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
