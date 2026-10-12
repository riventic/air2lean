#!/usr/bin/env python3
"""Bring every generated file up to date, in dependency order (scripts/regen.sh).

  regen.sh [--pr] [--only STEP[,STEP]] [--no-commit] [--keep-going]   regenerate
  regen.sh --check [--pr]                                             check only (preflight, op table, pins)
  regen.sh --list [--json]                                            steps, scope and outputs

Each step drives the repository's own generator (coverage.py, premises.py, theorem-inventory.py,
support-matrix.py, gen-integrity.py, provenance-evidence.py, ...). A step whose own check passes is
skipped, so a second run changes nothing. Heavy builds run under scripts/build-guard.py and are
retried while the build lock is busy (exit 75). With AIR2LEAN_CAS_DIR set, Lake builds, patched
compilers and pristine compiler sources come from the shared cache (scripts/cas.py).

Scope: a `tree` step generates the whole-tree files of assurance/generated.json (coverage
inventories, premise index, provenance fixtures). They are never committed: CI produces them on
the tested tree and publishes them on the `generated` branch (docs/ci.md); here they are only
regenerated in place for local tools, and `--pr` skips them. Every other step is `pr`: its
committed output is checked in every CI run, so a PR regenerates it.

Provenance runs last: its proof receipts need a clean committed tree, so when a fixture is stale
the earlier (committed) outputs are committed first, then both fixtures are regenerated in place
by scripts/generated.py. `--no-commit` stops before that commit.
Exit 0: up to date; 1: a step failed; 2: usage; 3: provenance needs commits (--no-commit).
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
PY = sys.executable
LOCK_BUSY = 75
WORK = ROOT / '.lake/regen'


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


cas = load('cas', 'cas.py')


class Failed(Exception):
    def __init__(self, message, code=1):
        super().__init__(message)
        self.code = code  # 3: provenance needs commits (--no-commit)


def log(message):
    print('regen: ' + message, file=sys.stderr, flush=True)


def run(argv, env=None, check=True, quiet=False, **kw):
    if not quiet:
        log('$ ' + ' '.join(map(str, argv)))
    done = subprocess.run([str(a) for a in argv], cwd=ROOT, env=env, **kw)
    if check and done.returncode != 0:
        raise Failed('%s exited %d' % (' '.join(map(str, argv[:4])), done.returncode))
    return done


def ok(argv, env=None):
    """Whether a check command passes (its output is suppressed)."""
    return run(argv, env=env, check=False, quiet=True, stdout=subprocess.DEVNULL,
               stderr=subprocess.DEVNULL).returncode == 0


def lake_env():
    return dict(os.environ, **cas.lake_env())


def lock_retries():
    """Attempts of a heavy command while the build lock is busy (at least one)."""
    return max(1, int(os.environ.get('AIR2LEAN_LOCK_RETRIES', '6')))


def retry_while_busy(name, attempt, busy):
    """attempt(n) until it returns a result that busy() rejects no more (the build lock was busy
    longer than AIR2LEAN_LOCK_WAIT), at most AIR2LEAN_LOCK_RETRIES times, 120 s apart."""
    retries = lock_retries()
    for n in range(1, retries + 1):
        result = attempt(n)
        if n == retries or not busy(result):
            return result
        log('build lock busy during %s (attempt %d); retrying in 120 s' % (name, n))
        time.sleep(120)


def guarded(name, argv, env=None, timeout=18000):
    """argv under scripts/build-guard.py (lock AIR2LEAN_BUILD_LOCK), retried while the lock is busy;
    its RSS limit is AIR2LEAN_REGEN_RSS_MIB (default 24576 MiB; lower it on a shared machine).
    Returns (report path, log path)."""
    WORK.mkdir(parents=True, exist_ok=True)
    report, logfile = WORK / (name + '.guard.json'), WORK / (name + '.guard.log')
    wait = os.environ.get('AIR2LEAN_LOCK_WAIT', '21600')
    code = retry_while_busy(name, lambda n: run(
        [PY, 'scripts/build-guard.py', '--cwd', ROOT, '--lock-wait', wait, '--timeout', timeout,
         '--rss-mib', os.environ.get('AIR2LEAN_REGEN_RSS_MIB', '24576'), '--log-bytes', 16 << 20,
         '--report', report, '--log', logfile, '--', *argv],
        env=env, check=False).returncode, lambda code: code == LOCK_BUSY)
    if code != 0:
        raise Failed('%s failed (exit %d); log %s' % (name, code, logfile))
    return report, logfile


def write_if_changed(path, data):
    path = ROOT / path
    if path.exists() and path.read_bytes() == data:
        return False
    staged = path.with_name(path.name + '.partial')
    staged.write_bytes(data)
    os.replace(staged, path)
    log('wrote ' + str(path.relative_to(ROOT)))
    return True


def versions():
    return [v['version'] for v in json.loads((ROOT / 'compatibility.json').read_text())['zig']['versions']]


# ------------------------------------------------------------------ steps

def step_translator(check):
    """`lake build air2lean`: the translator that later steps run."""
    guarded('translator', ['lake', 'build', 'air2lean'], env=lake_env(), timeout=3600)


def step_gen(check):
    """Generated modules from committed AIR; `write` ends with the full check itself."""
    if ok([PY, '-B', 'scripts/gen-integrity.py', 'check']):
        return
    if check:
        raise Failed('generated modules are stale; regenerate with: scripts/gen-integrity.py write')
    run([PY, '-B', 'scripts/gen-integrity.py', 'write'])


def simple(check_argv, write_argv):
    def step(check):
        if ok(check_argv):
            return
        if check:
            raise Failed('stale; regenerate with: ' + ' '.join(write_argv))
        run(write_argv)
        run(check_argv)
    return step


def step_op_table(check):
    fresh = run([ROOT / '.lake/build/bin/air2lean', '--print-op-table'], quiet=True, stdout=subprocess.PIPE).stdout
    target = 'coverage/op-table/op-table.json'
    if check:
        if (ROOT / target).read_bytes() != fresh:
            raise Failed(target + ' is stale')
    else:
        write_if_changed(target, fresh)


def step_coverage(check):
    with tempfile.TemporaryDirectory(prefix='air2lean-regen.') as scratch:
        for version in versions():
            source = cas.pristine_source(ROOT, version, Path(scratch) / version)
            args = ['--version', version, '--source', source, '--os', 'linux', '--inventory',
                    'coverage/%s.json' % version]
            if not ok([PY, 'scripts/coverage.py', 'check', *args]):
                if check:
                    raise Failed('coverage/%s.json is stale; run scripts/regen.sh' % version)
                run([PY, 'scripts/coverage.py', 'generate', *args])
                run([PY, 'scripts/coverage.py', 'check', *args])
    run([PY, 'scripts/coverage.py', 'l14', 'coverage/0.14.1.json', 'coverage/0.15.2.json', 'coverage/0.16.0.json'])


def step_pins(check):
    """Input pins of the L04 try-pointers integration (check-artifacts.py): its retained
    translation and the exporter it was taken with. Outputs are pinned, not translator sources:
    check.sh and gen-integrity.py re-translate and compare the output itself."""
    digest = lambda rel: cas.sha256_file(ROOT / rel)
    pins = {'tests/roadmap/try-pointers/emitter-integration.json': {
                'current_generated_sha256': digest('tests/roadmap/try-pointers/TryPointers/Gen.lean')},
            'tests/roadmap/try-pointers/integration-qualification.json': {
                'current_exporter_sha256': digest('zig-patch/air-json/json.zig')}}
    for rel, fields in pins.items():
        data = json.loads((ROOT / rel).read_text())
        if all(data.get(k) == v for k, v in fields.items()):
            continue
        if check:
            raise Failed(rel + ' pins are stale')
        data.update(fields)
        write_if_changed(rel, (json.dumps(data, indent=2) + '\n').encode())


def step_claims(check):
    """tests/roadmap/claims/fixture-report.json from the statement extractor (Lean build)."""
    guarded('claims', ['bash', 'tests/roadmap/claims/check.sh'] + ([] if check else ['--write']),
            env=lake_env(), timeout=7200)


def step_audit_exposure(check):
    """tests/roadmap/architecture-audit/claims/exposure-report.json: the kernel statements of the
    audit fixtures (their fingerprints and redirections follow the library they import)."""
    snapshot = [PY, '-B', 'tests/roadmap/architecture-audit/claims/snapshot.py']
    # The libraries the fixtures import (as in CI): the audit replays them with `lake build --no-build`.
    guarded('audit-exposure-deps', ['lake', 'build', 'ZigLean', 'AssuranceTools', 'Proofs.Asm.Gen',
                                    'ZigLean.Witness'], env=lake_env(), timeout=7200)
    guarded('audit-exposure', ['bash', 'tests/roadmap/architecture-audit/claims/build.sh'],
            env=lake_env(), timeout=7200)
    if ok(snapshot + ['check']):
        return
    if check:
        raise Failed('exposure-report.json is stale; regenerate with: '
                     'tests/roadmap/architecture-audit/claims/snapshot.py write')
    run(snapshot + ['write'])
    run(snapshot + ['check'])


def run_is_current(inv_mod, run_record):
    """Whether a recorded theorem-inventory run still matches the tree (the hashes `record` took)."""
    if run_record.get('outcome') != 'success' or run_record.get('exit_code') != 0:
        return False
    if run_record.get('lean_toolchain_sha256') != inv_mod.sha256(ROOT / 'lean-toolchain'):
        return False
    for gen in run_record.get('gens', {}).values():
        if not (ROOT / gen['path']).is_file() or inv_mod.sha256(ROOT / gen['path']) != gen['sha256']:
            return False
    for mod, digest in run_record.get('sources', {}).items():
        path = ROOT / inv_mod.module_path(mod)
        if not path.is_file() or inv_mod.sha256(path) != digest:
            return False
    command = run_record['command']
    modules = command[command.index('build') + 1:] if 'build' in command and 'lake' in command[0] \
        else command[command.index('--') + 1:]
    try:
        built = inv_mod.library_modules(ROOT) if 'Proofs' in modules else inv_mod.closure(ROOT, modules)
    except inv_mod.Error:
        return False
    return sorted(m for m in built if not m.endswith('.Gen')) == run_record.get('modules')


def step_inventory(check):
    """Re-record every theorem-inventory run whose recorded hashes no longer match, then write."""
    inv_mod = load('theorem_inventory', 'theorem-inventory.py')
    inventory = inv_mod.load(ROOT)
    stale = [rid for rid, r in sorted(inventory.get('runs', {}).items()) if not run_is_current(inv_mod, r)]
    if check:
        if stale:
            raise Failed('stale theorem-inventory runs: ' + ', '.join(stale))
        run([PY, '-B', 'scripts/theorem-inventory.py', 'check'])
        return
    for rid in stale:
        record = inventory['runs'][rid]
        log('re-recording theorem-inventory run %s' % rid)
        report, logfile = guarded('inventory-' + rid, record['command'], env=lake_env())
        run([PY, '-B', 'scripts/theorem-inventory.py', 'record', '--run', rid, '--zig', record['zig'],
             '--target', record['target'], '--guard-report', report, '--guard-log', logfile])
    if not ok([PY, '-B', 'scripts/theorem-inventory.py', 'check']):
        run([PY, '-B', 'scripts/theorem-inventory.py', 'write'])
        run([PY, '-B', 'scripts/theorem-inventory.py', 'check'])




def provenance_current():
    return all(ok([PY, 'scripts/provenance-evidence.py', '--fixture', 'all', action, '--strict'])
               for action in ('check', 'replay'))


def commit(message, paths):
    run(['git', 'add', '-A', '--', *paths])
    if run(['git', 'diff', '--cached', '--quiet'], check=False, quiet=True).returncode != 0:
        run(['git', 'commit', '-q', '-m', message])


def step_provenance(check, allow_commit, written):
    """The provenance fixtures' manifest, pins and receipts: whole-tree generated files, never
    committed (assurance/generated.json). Regenerated in place by scripts/generated.py; its proof
    receipts need a clean tracked tree, so this step's earlier outputs are committed first."""
    if provenance_current():
        return
    if check:
        raise Failed('provenance fixtures are stale; run scripts/regen.sh --only provenance '
                     '(or scripts/generated.py fetch --group provenance --group provenance-gap)')
    dirty = changed_paths()
    if dirty:
        if not allow_commit:
            raise Failed('provenance receipts need a clean tree; rerun without --no-commit', code=3)
        foreign = sorted(dirty - written)
        if foreign:
            raise Failed('provenance receipts need a clean tree; commit or stash these first: '
                         + ', '.join(foreign[:10]))
        commit('Regenerate generated files (scripts/regen.sh)', sorted(written))
    env = dict(os.environ, AIR2LEAN_ZIG_AIR=str(cas.zig_air(ROOT, '0.16.0')), AIR2LEAN_ZIG=str(cas.host_zig('0.16.0')))
    for name in cas.lake_env():  # Proof receipts refuse Lake environment overlays.
        env.pop(name, None)
    # provenance-evidence.py waits for the build lock itself (--lock-wait).
    run([PY, '-B', 'scripts/generated.py', 'regen', '--group', 'provenance-gap', '--group', 'provenance'], env=env)
    if not provenance_current():
        raise Failed('provenance fixtures still stale after regeneration')


# name, scope, outputs, function; in dependency order (provenance is handled last, separately).
STEPS = [
    ('translator', 'pr', [], step_translator),
    ('gen', 'pr', ['Gen.lean modules (scripts/gen-integrity.py list)'], step_gen),
    ('ci-matrix', 'pr', ['.github/workflows/ci.yml (generated matrix regions)'],
     simple([PY, 'scripts/ci-matrix.py', 'check'], [PY, 'scripts/ci-matrix.py', 'write'])),
    ('trust-report', 'pr', ['docs/trust-report.md'],
     simple([PY, 'scripts/trust-report.py', 'check'], [PY, 'scripts/trust-report.py', 'write'])),
    ('op-table', 'pr', ['coverage/op-table/op-table.json'], step_op_table),
    ('coverage', 'tree', ['coverage/<version>.json'], step_coverage),
    ('pins', 'pr', ['tests/roadmap/try-pointers/emitter-integration.json',
                      'tests/roadmap/try-pointers/integration-qualification.json'], step_pins),
    ('premises', 'tree', ['docs/premise-index.md'],
     simple([PY, '-B', 'scripts/premises.py', 'check'], [PY, '-B', 'scripts/premises.py', 'write'])),
    ('support-matrix', 'pr', ['docs/support-matrix.md', 'README.md and PLAN.md (marked regions)'],
     simple([PY, 'scripts/support-matrix.py', 'check'], [PY, 'scripts/support-matrix.py', 'generate'])),
    ('claims', 'pr', ['tests/roadmap/claims/fixture-report.json'], step_claims),
    ('audit-exposure', 'pr', ['tests/roadmap/architecture-audit/claims/exposure-report.json'],
     step_audit_exposure),
    ('inventory', 'pr', ['assurance/theorem-inventory.json', 'docs/theorem-inventory.md'], step_inventory),
    ('provenance', 'tree', ['assurance/provenance-gap/{manifest,pins}.json, receipt/',
                            'assurance/provenance/{manifest,pins}.json, receipt/'], None),
]
# The `tree` steps are exactly the generators of assurance/generated.json (one source of truth):
# whole-tree files are never committed; CI produces them and publishes them on `generated`.
TREE_GROUPS = {'coverage': ['coverage'], 'premises': ['premise-index'],
               'provenance': ['provenance', 'provenance-gap']}
GENERATED = load('generated', 'generated.py')
assert sorted(g for groups in TREE_GROUPS.values() for g in groups) == sorted(
    g['name'] for g in GENERATED.load(ROOT)['groups']), 'regen.py TREE_GROUPS out of step with ' + GENERATED.REGISTRY
assert {name for name, scope, _, _ in STEPS if scope == 'tree'} == set(TREE_GROUPS)


def changed_paths():
    out = run(['git', 'status', '--porcelain', '--untracked-files=no'], quiet=True, stdout=subprocess.PIPE,
              text=True).stdout
    return {line[3:] for line in out.splitlines()}


def dirty_state():
    """Content hash of every modified tracked file (None: deleted)."""
    return {path: cas.sha256_file(ROOT / path) if (ROOT / path).is_file() else None for path in changed_paths()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--check', action='store_true', help='check only (runs scripts/preflight.sh)')
    parser.add_argument('--pr', action='store_true', help='skip whole-tree steps (produced at merge)')
    parser.add_argument('--only', default='', help='comma-separated step names')
    parser.add_argument('--no-commit', action='store_true', help='never commit; stop before stale provenance')
    parser.add_argument('--keep-going', action='store_true', help='run the remaining steps after a failure')
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--json', action='store_true')
    a = parser.parse_args(argv)
    names = [s[0] for s in STEPS]
    only = [n for n in a.only.split(',') if n]
    if any(n not in names for n in only):
        parser.error('unknown step; choose from ' + ', '.join(names))
    if a.list:
        rows = [{'step': n, 'scope': scope, 'outputs': outputs} for n, scope, outputs, _ in STEPS]
        print(json.dumps(rows, indent=2) if a.json else
              '\n'.join('%-15s %-5s %s' % (r['step'], r['scope'], ', '.join(r['outputs'])) for r in rows))
        return 0
    if a.check and not only:
        # preflight runs the checks of these steps (plus the record gates) except the op table and
        # the try-pointers pins, checked here; the claims fixture needs a Lean build (--only claims).
        code = run(['bash', 'scripts/preflight.sh'] + (['--pr'] if a.pr else []), check=False).returncode
        if not a.pr:
            for name, function in (('op-table', step_op_table), ('pins', step_pins)):
                try:
                    function(True)
                except (Failed, OSError) as error:
                    log('FAILED %s: %s' % (name, error))
                    code = code or 1
        return code
    selected = [s for s in STEPS if (not only or s[0] in only) and not (a.pr and s[1] == 'tree')]
    if any(s[0] in ('gen', 'op-table', 'inventory') for s in selected) and 'translator' not in [s[0] for s in selected]:
        selected.insert(0, STEPS[0])
    written = set()  # Files a step changed: only these are ever committed (never the user's edits).
    failures, timings, code = [], [], 1
    state = dirty_state()
    for name, scope, _, function in selected:
        start = time.monotonic()
        log('== %s (%s)' % (name, scope))
        try:
            if name == 'provenance':
                step_provenance(a.check, not a.no_commit, written)
            else:
                function(a.check)
        except (Failed, cas.CasError) as error:
            failures.append(name)
            log('FAILED %s: %s' % (name, error.args[0]))
            code = getattr(error, 'code', 1)
            if code != 1 or not a.keep_going:
                break
        finally:
            after = dirty_state()
            written |= {path for path, digest in after.items() if state.get(path, '') != digest}
            state = after
            timings.append((name, time.monotonic() - start))
    for name, seconds in timings:
        log('%-15s %7.1f s' % (name, seconds))
    if not a.check:
        cas.gc_if_due()
    if failures:
        log('failed: ' + ', '.join(failures))
        return code
    log('every generated file is up to date' if not a.pr else 'every PR-scoped generated file is up to date')
    return 0


if __name__ == '__main__':
    sys.exit(main())
