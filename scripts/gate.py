#!/usr/bin/env python3
"""The pre-merge gate: every local check a PR needs before it merges, in dependency order and in
parallel.

    scripts/gate.sh [--base REF] [--check] [--only UNIT[,UNIT]] [--jobs N] [--logs DIR]
    scripts/gate.sh --list [--json] [--base REF]

One command for the sequence a PR ran before (docs/ci.md#pre-merge-gate): the full build with
the proof-fixture checks, `scripts/regen.sh --pr`, `scripts/preflight.sh` and
`scripts/proof-framework.py --base origin/main`. It composes those scripts; it checks nothing
itself. Its units:

- `materialize:GROUP` and `fetch:...`: the whole-tree generated files (assurance/generated.json)
  as scripts/preflight.sh makes them.
- `full-build`, after those: scripts/full-build.sh --no-fixtures (Lake builds, the standalone
  Lean files). Lake and lean-deps.py remember their own results.
- `regen:STEP` for each PR-scoped step of scripts/regen.py: the step regenerates its committed
  output when it is stale (`--check`: the unit fails instead), then checks it.
- `fixtures`, after the regen steps: scripts/fixture-checks.sh, the full build's last phase (the
  proof-fixture checks and Python tests CI runs).
- `preflight:LABEL` for each check of scripts/preflight.sh, parsed from it (a new check there is a
  new unit here), except those another unit runs already: the full build, the materialization
  and every check a regen step ends with (its `check_argv`). proof-framework.py compares with
  the base (--base).

Every unit runs in the checkout, every time: the gate takes no result from an earlier run
(docs/ci.md#parked-precise-input-tracking). Units run in parallel (--jobs); those that build or
run Lean wait for each other through scripts/build-guard.py (within the machine's memory
budget). When a regen unit rewrote files, a second pass runs every unit over the new state (the
full build ran before the rewrite), also after a failure, and fails if it rewrites files again.
Exit 0: every unit passed (files a regen unit rewrote are listed: commit them); 1: a unit
failed, or the checkout changed during the run; 2: usage.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures
import dataclasses
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
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


COMMAND_START = {';', '&&', '||', '|', 'then', 'else', 'do', '!', 'if', 'while', 'until'}


def preflight_checks(text):
    """[(label, argv)] of scripts/preflight.sh's `check LABEL CMD...` lines (also indented ones). A
    check this cannot read as one line of words, or a script or interpreter that a line runs
    outside `check`, fails closed: the gate would miss it."""
    out = []
    for line in text.splitlines():
        try:
            words = shlex.split(line, comments=True)
        except ValueError:
            words = []
        if not re.match(r'\s*check\s', line):
            if any((i == 0 or words[i - 1] in COMMAND_START) and
                   (w in ('python3', 'python', 'bash', 'sh') or w.endswith(('.py', '.sh'))) for i, w in enumerate(words)):
                raise SystemExit('gate: scripts/preflight.sh runs %r outside `check`; make it a check line '
                                 '`check LABEL CMD ARGS...`' % line.strip())
            continue
        if len(words) < 3 or line.rstrip().endswith('\\') or any(w in (';', '&&', '||', '|') for w in words):
            raise SystemExit('gate: cannot read the preflight check %r; write it as one line '
                             '`check LABEL CMD ARGS...`' % line.strip())
        out.append((words[1], words[2:]))
    return out


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

    Nothing writes a file of the checkout while another unit runs. The whole-tree generated files
    come first, one group after another; then the full build of the Lean modules; then the regen
    steps one after another (each may rewrite committed files that a later step reads), in
    regen.py's order; then the checks, which write nothing, all at once: the proof-fixture checks
    and Python tests (scripts/fixture-checks.sh, the full build's last phase, after the
    regeneration as in the sequence it replaces) and the preflight checks."""
    data = GENERATED.load(ROOT)
    out = []
    for g in data['groups']:
        if g['name'] in GENERATED.cheap(data):
            out.append(Unit('materialize:' + g['name'], [PY, '-B', 'scripts/generated.py', 'regen', '--group', g['name']],
                            after=tuple(u.name for u in out)))
    heavy = [g['name'] for g in data['groups'] if g['name'] not in GENERATED.cheap(data)]
    # As scripts/preflight.sh: CI regenerates these for the tree; offline they stay as they are.
    out.append(Unit('fetch:' + ','.join(heavy), ['bash', '-c', 'python3 -B scripts/generated.py fetch %s || '
                    'echo "note: not fetched; CI regenerates them"' % ' '.join('--group ' + h for h in heavy)],
                    after=tuple(u.name for u in out)))
    out.append(Unit('full-build', ['bash', 'scripts/full-build.sh', '--no-fixtures'], after=tuple(u.name for u in out)))
    first = tuple(u.name for u in out)
    steps = {name for name, scope, _, _ in REGEN.STEPS if scope == 'pr'}
    covered = {check for name, check in regen_checks().items() if name in steps}
    previous = first
    for name, scope, _, _ in REGEN.STEPS:
        if scope != 'pr' or name == 'translator':
            continue
        argv = [PY, '-B', 'scripts/regen.py', '--pr', '--only', name, '--no-commit', '--no-translator', '--no-gc']
        out.append(Unit('regen:' + name, argv + (['--check'] if check else []), after=previous,
                        requires=('full-build',)))
        previous = first + ('regen:' + name,)
    out.append(Unit('fixtures', ['bash', 'scripts/fixture-checks.sh'], after=previous, requires=('full-build',)))
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


def changed_files(revision):
    """The files that differ between REVISION and the checkout (committed, staged or not; both
    paths of a rename) and the new ones (not ignored), sorted."""
    out = git('diff', '--name-only', '--no-renames', '-z', revision) + '\0' \
        + git('ls-files', '-o', '--exclude-standard', '-z')
    return sorted({f for f in out.split('\0') if f})


def dirty_state():
    """Content digest of every file that differs from HEAD or is new (None: deleted)."""
    return {f: CR.sha256((ROOT / f).read_bytes()) if (ROOT / f).is_file() else None
            for f in changed_files('HEAD')}


def rewritten(before):
    """The files whose content changed since BEFORE (a dirty_state())."""
    after = dirty_state()
    return {f for f in before.keys() | after.keys() if before.get(f, 'HEAD') != after.get(f, 'HEAD')}


# ---- running ----------------------------------------------------------------------------------

class Run:
    def __init__(self, a, chosen):
        self.a, self.units = a, chosen
        self.results, self.lock = {}, threading.Lock()
        self.changed = changed_files(a.base)
        self.written = set()
        self.logs = Path(a.logs) if a.logs else Path(tempfile.mkdtemp(prefix='air2lean-gate.'))
        self.logs.mkdir(parents=True, exist_ok=True)
        self.start = git('rev-parse', 'HEAD').strip(), dirty_state()

    def external_changes(self):
        """Files that changed during the run although no unit wrote them (an edit meanwhile)."""
        head, before = self.start
        if git('rev-parse', 'HEAD').strip() != head:
            return ['HEAD (now %s)' % git('rev-parse', '--short', 'HEAD').strip()]
        return sorted(rewritten(before) - self.written)

    def one(self, unit):
        start, before = time.monotonic(), dirty_state()
        path = self.logs / (re.sub(r'[^\w.-]+', '_', unit.name) + '.log')
        with open(path, 'wb') as out:
            code = execute(unit.argv, ROOT, out)
        seconds = time.monotonic() - start
        wrote = rewritten(before)
        if wrote:
            with self.lock:
                self.written |= wrote
        if code != 0:
            tail = path.read_text(errors='replace').strip().splitlines()[-15:]
            return 'FAILED', seconds, ['log: %s' % path] + ['  ' + l for l in tail]
        return ('wrote ' + ', '.join(sorted(wrote))) if wrote else 'ran', seconds, []

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
    counts = collections.Counter(status.split(' ')[0] for _, status, _, _ in rows)
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
    if a.list:
        rows = [{'unit': u.name, 'after': list(u.after), 'argv': [str(w) for w in u.argv]} for u in chosen]
        if a.json:
            print(json.dumps(rows, indent=1))
        else:
            for r in rows:
                print('%-58s %s' % (r['unit'], shlex.join(normalized(r['argv']))))
        return 0
    start, written = time.monotonic(), set()
    # A pass that regenerated files checked them only from its later units on (the full build ran
    # before): a second pass checks the new state.
    for attempt in (1, 2):
        run = Run(a, chosen)
        log('pass %d: base %s; %d files changed; %d units, %d at once; logs %s' % (
            attempt, a.base[:12], len(run.changed), len(chosen), a.jobs, run.logs))
        failed = run.go()
        if edited := run.external_changes():
            log('the checkout changed during the run (%s): run the gate again' % ', '.join(edited[:5]))
            failed = failed | {'checkout changed'}
        written |= run.written
        # A failure on the state before a regeneration (the full build ran first) is checked again.
        if not run.written or 'checkout changed' in failed:
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
