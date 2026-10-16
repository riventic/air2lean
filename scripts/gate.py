#!/usr/bin/env python3
"""The pre-merge gate: every local check a PR needs before it merges, affected-only and cached.

    scripts/gate.sh [--base REF] [--check] [--only UNIT[,UNIT]] [--jobs N] [--no-cache] [--logs DIR]
    scripts/gate.sh --list [--json] [--base REF]

One command for the sequence a PR ran before (docs/ci.md#pre-merge-gate): the full build with
the proof-fixture checks, `scripts/regen.sh --pr`, `scripts/preflight.sh` and
`scripts/proof-framework.py --base origin/main`. It composes those scripts; it checks nothing
itself. Its units:

- `materialize:GROUP` and `fetch:...`: the whole-tree generated files (assurance/generated.json)
  as scripts/preflight.sh makes them; a cheap group's files are stored with the unit's record
  and restored on a hit.
- `full-build`, after those: scripts/full-build.sh (Lake builds, the standalone Lean files, the
  proof-fixture checks and Python tests CI runs). Lake, lean-deps.py and fixture-checks.py
  remember their own results.
- `regen:STEP` for each PR-scoped step of scripts/regen.py: the step regenerates its committed
  output when it is stale (`--check`: the unit fails instead), then checks it.
- `preflight:LABEL` for each check of scripts/preflight.sh, parsed from it (a new check there is a
  new unit here), except those another unit runs already: the full build, the materialization
  and every check a regen step ends with (its `check_argv`). proof-framework.py compares with
  the base (--base).

Results are reused through scripts/ci-reuse.py's traced records (docs/ci.md#traced-records), the
one mechanism fixture-checks.py uses too: a unit's check runs traced, in a fresh repository of
the checkout's content (no history or refs; a sandbox hides everything outside but roots keyed
by identity and content-addressed caches), and a pass records what it read; the unit is reused
while a record of it matches the checkout. A regen unit whose check fails regenerates in the
checkout and checks the new state traced. The full build and the fetch run in the checkout.
Where the sandbox does not apply (another OS, or inside a sandbox already) every unit runs and
nothing is recorded.

Units run in parallel (--jobs); those that build or run Lean wait for each other through
scripts/build-guard.py (within the machine's memory budget). When a regen unit rewrote files, a
second pass runs every unit over the new state (the full build builds what was rewritten;
unaffected units hit), and fails if it rewrites files again. Exit 0: every unit passed (files a
regen unit rewrote are listed: commit them); 1: a unit failed, or the checkout changed during
the run; 2: usage.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
PY = sys.executable


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CR = load('air2lean_ci_reuse', 'ci-reuse.py')
REGEN = load('air2lean_regen', 'regen.py')
GENERATED = REGEN.GENERATED


def log(message):
    print('gate: ' + message, file=sys.stderr, flush=True)


def git(*args, check=True):
    """git's output in the checkout (CR.git: CR.ReuseError on failure when CHECK)."""
    return CR.git(ROOT, *args, check=check).decode('utf-8', 'surrogateescape')


def execute(argv, cwd, out):
    """Exit code of ARGV in CWD, its output written to the binary file OUT."""
    out.flush()
    return subprocess.run([str(a) for a in argv], cwd=cwd, stdout=out, stderr=subprocess.STDOUT,
                          env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')).returncode


# ---- units ------------------------------------------------------------------------------------

@dataclasses.dataclass
class Unit:
    name: str
    argv: list
    after: tuple = ()              # units that run first
    requires: tuple = ()           # of those, the ones that must have passed
    outputs: tuple = ()            # untracked files the unit produces (stored with its record)
    cache: bool = True             # traced and recorded (else run in the checkout, every time)
    check_argv: list | None = None  # the check alone (a regen step without regenerating)

    def __post_init__(self):
        self.check_argv = self.check_argv or self.argv

    def identity(self):
        """What the unit runs, for its pre-key (scripts/ci-reuse.py adds the rest)."""
        return {'argv': [str(a) for a in self.check_argv], 'outputs': list(self.outputs)}


def preflight_checks(text):
    """[(label, argv)] of scripts/preflight.sh's `check 'LABEL' CMD...` lines (also indented ones)."""
    return [(words[1], words[2:]) for words in (shlex.split(line) for line in text.splitlines()
                                                 if line.lstrip().startswith("check '"))]


def normalized(argv):
    """argv without the interpreter and its flags (`python3 -B x.py` == `PY x.py`)."""
    words = [str(w) for w in argv]
    while words and (words[0] in ('python3', 'bash', PY) or words[0].startswith('-')):
        words = words[1:]
    return words


def script_of(argv):
    return next((w for w in normalized(argv) if w.endswith(('.py', '.sh'))), None)


def regen_checks():
    """{step: normalized check argv} of each regen step that ends with a plain check command."""
    return {name: tuple(normalized(function.check_argv)) for name, _, _, function in REGEN.STEPS
            if hasattr(function, 'check_argv')}


def units(base, check):
    """Every unit of the gate, in dependency order.

    Ordering keeps every record exact: nothing writes a file of the checkout while another unit
    runs. The whole-tree generated files (ignored files, which every traced unit gets a copy of)
    come first, one group after another; then the full build, whose fixture checks and tests read
    them; then the regen steps one after another (each may rewrite committed files that a later
    step reads), in regen.py's order; then the preflight checks, which write nothing, all at once."""
    data = GENERATED.load(ROOT)
    out = []
    for g in data['groups']:
        if g['name'] in GENERATED.cheap(data):
            out.append(Unit('materialize:' + g['name'], [PY, '-B', 'scripts/generated.py', 'regen', '--group', g['name']],
                            after=tuple(u.name for u in out), outputs=tuple(g['paths'])))
    heavy = [g['name'] for g in data['groups'] if g['name'] not in GENERATED.cheap(data)]
    # As scripts/preflight.sh: CI regenerates these for the tree; offline they stay as they are.
    out.append(Unit('fetch:' + ','.join(heavy), ['bash', '-c', 'python3 -B scripts/generated.py fetch %s || '
                    'echo "note: not fetched; CI regenerates them"' % ' '.join('--group ' + h for h in heavy)],
                    after=tuple(u.name for u in out), cache=False))
    out.append(Unit('full-build', ['bash', 'scripts/full-build.sh'], after=tuple(u.name for u in out), cache=False))
    first = tuple(u.name for u in out)
    steps = {name for name, scope, _, _ in REGEN.STEPS if scope == 'pr'}
    covered = {check for name, check in regen_checks().items() if name in steps}
    previous = first
    for name, scope, _, _ in REGEN.STEPS:
        if scope != 'pr' or name == 'translator':
            continue
        argv = [PY, '-B', 'scripts/regen.py', '--pr', '--only', name, '--no-commit', '--no-translator', '--no-gc']
        out.append(Unit('regen:' + name, argv + (['--check'] if check else []), after=previous,
                        requires=('full-build',), check_argv=argv + ['--check']))
        previous = first + ('regen:' + name,)
    for label, argv in preflight_checks((ROOT / 'scripts/preflight.sh').read_text()):
        script = script_of(argv)
        # The materialize/fetch units and the full build run these already.
        if script in ('scripts/generated.py', 'scripts/full-build.sh') or tuple(normalized(argv)) in covered:
            continue
        if any('$' in word for word in argv):  # fail closed: the gate runs no shell
            raise SystemExit('gate: the preflight check %r reads a shell variable; give it literal '
                             'arguments or a unit here' % label)
        if script == 'scripts/proof-framework.py' and '--base' not in argv:
            argv = argv + ['--base', base]
        out.append(Unit('preflight:' + label, argv, after=previous))
    return out


def dirty_state():
    """Content digest of every file that differs from HEAD or is new (None: deleted)."""
    return {f: CR.sha256((ROOT / f).read_bytes()) if (ROOT / f).is_file() else None
            for f in CR.changed_files(ROOT, 'HEAD')}


def rewritten(before):
    """The files whose content changed since BEFORE (a dirty_state())."""
    after = dirty_state()
    return {f for f in before.keys() | after.keys() if before.get(f, 'HEAD') != after.get(f, 'HEAD')}


# ---- running ----------------------------------------------------------------------------------

class Run:
    def __init__(self, a, chosen, outside):
        self.a, self.units, self.outside = a, chosen, outside
        self.sound = outside.available()
        self.results, self.lock = {}, threading.Lock()
        self.changed = CR.changed_files(ROOT, a.base)
        self.written, self.pending = set(), []
        self.logs = Path(a.logs) if a.logs else Path(tempfile.mkdtemp(prefix='air2lean-gate.'))
        self.logs.mkdir(parents=True, exist_ok=True)
        self._records = None
        self.start_tree = self.records().commit

    def records(self):
        """Records over the current checkout state (a new snapshot after a unit rewrote files)."""
        with self.lock:
            if self._records is None:
                self._records = CR.Records(ROOT, CR.snapshot(ROOT))
            return self._records

    def invalidate(self):
        with self.lock:
            self._records = None

    def prekey(self, unit, records):
        return records.prekey(self.outside, unit.identity()) if self.sound and unit.cache else None

    def external_changes(self):
        """Files that changed during the run although no unit wrote them (an edit meanwhile)."""
        out = git('diff', '--name-only', '--no-renames', '-z', self.start_tree, CR.snapshot(ROOT))
        return sorted(f for f in out.split('\0') if f and f not in self.written)

    def traced(self, unit, records, logfile):
        """(exit code, trace) of the unit's check, traced in a fresh tree of RECORDS' snapshot."""
        private = Path(tempfile.mkdtemp(prefix='air2lean-gate-unit.'))
        try:
            spec = {'root': str(ROOT), 'argv': unit.identity()['argv'], 'env': self.outside.environment()[0],
                    'dest': str(private / 'tree'), 'private': str(private), 'commit': records.commit,
                    'clone': CR.cloned_entries(ROOT), 'outputs': list(unit.outputs), 'trace': str(private / 'trace.json'),
                    'logs': ['.lake/regen/*.guard.log'], 'profile': self.outside.profile(private) if self.sound else None}
            (private / 'spec.json').write_text(json.dumps(spec))
            with open(logfile, 'ab') as out:
                code = execute([PY, '-B', ROOT / 'scripts/ci-reuse.py', 'trace', private / 'spec.json'], ROOT, out)
            trace = private / 'trace.json'
            return code, json.loads(trace.read_text()) if trace.is_file() else None
        finally:
            shutil.rmtree(private, ignore_errors=True)

    def one(self, unit):
        start = time.monotonic()
        records = self.records()
        prekey = self.prekey(unit, records)
        if prekey and not self.a.no_cache and (entry := records.lookup(prekey)):
            for rel in unit.outputs:
                if (entry / 'files' / rel).is_file():
                    (ROOT / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(entry / 'files' / rel, ROOT / rel)
            if unit.outputs:
                self.invalidate()
            return 'cached', 0.0, []
        notes = []
        if prekey:
            changed = records.changed(prekey)
            notes.append('no record yet' if changed is None else 'changed since its record: ' +
                         (', '.join(changed[:6]) + (' ...' if len(changed) > 6 else '') if changed else 'nothing it read'))
        before, wrote, trace = dirty_state(), set(), None
        # A unit that runs in the checkout or copies outputs to it may change ignored files (Lake
        # builds, generated files) that no tracked change shows: later units get new records (the
        # digests a Records object computed are of the state it was made in).
        touched = not unit.cache or bool(unit.outputs)
        path = self.logs / (re.sub(r'[^\w.-]+', '_', unit.name) + '.log')
        path.write_bytes(b'')
        if not unit.cache:
            with open(path, 'ab') as out:
                code = execute(unit.argv, ROOT, out)
        else:
            code, trace = self.traced(unit, records, path)
            if code != 0 and unit.argv != unit.check_argv:
                # A regen step: regenerate in the checkout, then check the new state traced.
                with open(path, 'ab') as out:
                    code = execute(unit.argv, ROOT, out)
                touched, wrote = True, rewritten(before)
                if code == 0 and not wrote:
                    code = 1
                    notes.append('passes in the checkout but not traced in a fresh tree of its content '
                                 '(no git history, nothing outside but keyed roots: docs/ci.md#traced-records)')
                elif code == 0:
                    self.invalidate()
                    records = self.records()
                    prekey = self.prekey(unit, records)
                    code, trace = self.traced(unit, records, path)
        seconds = time.monotonic() - start
        wrote = wrote or rewritten(before)
        if wrote:
            with self.lock:
                self.written |= wrote
        if wrote or touched:
            self.invalidate()
        if code != 0:
            tail = path.read_text(errors='replace').strip().splitlines()[-15:]
            return 'FAILED', seconds, notes + ['log: %s' % path] + ['  ' + l for l in tail]
        if prekey and trace and trace['record'] is not None:
            body = {'unit': unit.name, 'seconds': round(seconds, 1), 'worktree': str(ROOT), 'time': time.time()}
            with self.lock:
                self.pending.append((records, prekey, trace['record'], body, trace['outputs']))
        elif prekey:
            notes.append('not recorded: %s' % (trace or {}).get('reason', 'no trace'))
        return ('wrote ' + ', '.join(sorted(wrote))) if wrote else 'ran', seconds, notes

    def publish(self):
        """Store the passes' records, unless a root outside the checkout changed meanwhile. (Each
        is exact for the snapshot its unit ran on, whatever changed in the checkout since.)"""
        if self.pending and self.outside.identity(fresh=True) != self.outside.identity():
            log('nothing recorded: a root outside the checkout changed during the run')
            return
        for records, prekey, record, body, outputs in self.pending:
            if records.publish(prekey, record, body, outputs) is None:
                log('%s: not recorded: an output changed in the checkout after the unit wrote it' % body['unit'])

    def go(self):
        pending = {u.name: u for u in self.units}
        names = set(pending)
        done, failed, running = set(), set(), {}
        with concurrent.futures.ThreadPoolExecutor(self.a.jobs) as pool:
            while pending or running:
                for name, unit in list(pending.items()):
                    if not all(n in done or n in failed for n in unit.after if n in names):
                        continue
                    del pending[name]
                    if broken := [n for n in unit.requires if n in failed]:
                        failed.add(name)
                        self.results[name] = ('skipped: %s failed' % ', '.join(broken), 0.0, [])
                    else:
                        running[pool.submit(self.one, unit)] = name
                if not running:
                    break
                finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in finished:
                    name = running.pop(future)
                    try:
                        result = future.result()
                    except Exception as error:  # a gate bug fails the unit, never passes it
                        result = ('FAILED', 0.0, ['gate error: %r' % error])
                    self.results[name] = result
                    (failed if result[0] == 'FAILED' else done).add(name)
                    log('%-58s %-8s %6.1f s' % (name, result[0].split(' ')[0], result[1]))
                    for note in result[2]:
                        log('    ' + note)
        return failed


def report(run, total, ok, written):
    rows = [(u.name, *run.results.get(u.name, ('not run', 0.0, []))) for u in run.units]
    counts = {}
    for _, status, _, _ in rows:
        counts[status.split(' ')[0]] = counts.get(status.split(' ')[0], 0) + 1
    print('\ngate: %s in %.0f s (%s)' % ('passed' if ok else 'FAILED', total,
                                          ', '.join('%d %s' % (n, s) for s, n in sorted(counts.items()))))
    for name, status, _, notes in rows:
        if status.startswith(('FAILED', 'skipped', 'not run')):
            print('  %s: %s' % (name, status))
            for note in notes:
                print('    ' + note)
    if written:
        print('gate: regenerated, commit them: ' + ' '.join(sorted(written)))


# ---- main -------------------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--base', help='compare with REF (default: merge base of HEAD and origin/main)')
    parser.add_argument('--check', action='store_true', help='never regenerate: a stale output fails')
    parser.add_argument('--only', default='', help='comma-separated unit names (and what they need)')
    parser.add_argument('--jobs', type=int, default=min(8, os.cpu_count() or 4))
    parser.add_argument('--no-cache', action='store_true', help='run every unit (results still recorded)')
    parser.add_argument('--logs', help='keep the unit logs here')
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--json', action='store_true')
    a = parser.parse_args(argv)
    a.base = a.base or git('merge-base', 'HEAD', 'origin/main', check=False).strip() or 'origin/main'
    every = units(a.base, a.check)
    chosen = every
    if a.only:
        wanted, by_name = set(a.only.split(',')), {u.name: u for u in every}
        if wanted - set(by_name):
            parser.error('unknown unit; choose from ' + ', '.join(by_name))
        todo = list(wanted)
        while todo:
            todo += [n for n in by_name[todo.pop()].after if n not in wanted]
            wanted |= set(todo)
        chosen = [u for u in every if u.name in wanted]
    outside = CR.Outside(ROOT)
    if not outside.available():
        log("the traced runs' sandbox does not apply here: every unit runs, nothing is recorded "
            '(docs/ci.md#traced-records)')
    if a.list:
        records = CR.Records(ROOT, CR.snapshot(ROOT))
        rows = []
        for u in chosen:
            prekey = records.prekey(outside, u.identity()) if outside.available() and u.cache else None
            cached = bool(prekey and records.lookup(prekey))
            changed = None if cached or not prekey else records.changed(prekey)
            rows.append({'unit': u.name, 'after': list(u.after), 'cached': cached,
                         'status': 'cached' if cached else 'runs' if not prekey else
                         'no record' if changed is None else 'changed', 'changed': (changed or [])[:20]})
        if a.json:
            print(json.dumps(rows, indent=1))
        else:
            for r in rows:
                print('%-58s %-9s %s' % (r['unit'], r['status'], ' '.join(r['changed'][:3])))
        return 0
    start, written = time.monotonic(), set()
    # A pass that regenerated files checked them only from its later units on (the full build ran
    # before): a second pass checks the new state, and every unit it did not affect hits.
    for attempt in (1, 2):
        run = Run(a, chosen, outside)
        log('pass %d: base %s; %d files changed; %d units, %d at once; logs %s' % (
            attempt, a.base[:12], len(run.changed), len(chosen), a.jobs, run.logs))
        failed = run.go()
        run.publish()
        if edited := run.external_changes():
            log('the checkout changed during the run (%s): run the gate again' % ', '.join(edited[:5]))
            failed = failed | {'checkout changed'}
        written |= run.written
        if failed or not run.written:
            break
    else:
        log('the second pass regenerated files again: %s' % ' '.join(sorted(run.written)))
        failed = {'regeneration does not settle'}
    ok = not failed and len(run.results) == len(chosen)
    report(run, time.monotonic() - start, ok, written)
    # Eviction of the shared cache (at most hourly), off the critical path: detached.
    subprocess.Popen([PY, '-B', 'scripts/cas.py', 'gc', '--if-due'], cwd=ROOT, stdout=subprocess.DEVNULL,
                     stderr=subprocess.DEVNULL, start_new_session=True)
    return 0 if ok else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except CR.ReuseError as error:
        sys.exit('gate: %s' % error)
