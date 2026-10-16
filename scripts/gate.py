#!/usr/bin/env python3
"""The pre-merge gate: every local check a PR needs before it merges, affected-only and cached.

    scripts/gate.sh [--base REF] [--check] [--only UNIT[,UNIT]] [--jobs N] [--no-cache] [--logs DIR]
    scripts/gate.sh --list [--json] [--base REF]
    scripts/gate.sh verify UNIT...

One command for the sequence a PR ran before (docs/ci.md#pre-merge-gate): the full build with
the proof-fixture checks, `scripts/regen.sh --pr`, `scripts/preflight.sh` and
`scripts/proof-framework.py --base origin/main`. It composes those scripts; it checks nothing
itself. Its units:

- `materialize:GROUP` and `fetch:...`: the whole-tree generated files (assurance/generated.json)
  as scripts/preflight.sh makes them; a cheap group's files are stored with the unit's record
  and restored on a hit.
- `full-build`, after those: scripts/full-build.sh (Lake builds, the standalone Lean files, the
  proof-fixture checks and Python tests CI runs). Lake, lean-deps.py and fixture-checks.py
  remember their own results by input.
- `regen:STEP` for each PR-scoped step of scripts/regen.py: the step regenerates its committed
  output when it is stale (`--check`: the unit fails instead), then checks it.
- `preflight:LABEL` for each check of scripts/preflight.sh, parsed from it (a new check there is a
  new unit here), except those another unit runs already: the full build, the materialization
  and every check a regen step ends with (its `check_argv`). proof-framework.py compares with
  the base (--base).

Results are reused with CI's mechanism (scripts/ci-reuse.py, docs/ci.md#1-input-hash-result-reuse):
the checkout's current content is a commit (`snapshot`), a unit's key is the key of a part over
that commit (the unit's command, the gate's sources, the host, the declared content and all
tracked names), a passing unit is a local record (`record_local`, in scripts/cas.py's store), and a
unit with declared inputs (assurance/gate-inputs.json) passes only in a restricted worktree of
that commit (`RestrictedWorktree`: every other tracked file withheld), so a declaration that
misses an input fails the unit. Every other unit is keyed by the whole tree, the whole-tree
generated files, HEAD and the base. `verify UNIT` runs a declared unit's check restricted.

Affected: the changed files since the base (default: the merge base of HEAD and origin/main)
among a unit's inputs; `--list` shows them and the gate prints them for every declared unit it
runs. Units run in parallel (--jobs); those that build or run Lean in the checkout wait for each
other through scripts/build-guard.py (one build per checkout, within the machine's memory budget).
When a regen unit rewrote files, a second pass runs every unit over the new state (the full
build builds what was rewritten; unaffected units hit), and fails if it rewrites files again.
Exit 0: every unit passed (files a regen unit rewrote are listed: commit them); 1: a unit
failed, or the checkout changed during the run (nothing of it is recorded); 2: usage.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
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
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
PY = sys.executable
SCHEMA = 'air2lean-gate/1'
# The gate's own machinery: part of every key.
SELF = ('scripts/gate.py', 'scripts/gate.sh', 'scripts/ci-reuse.py')


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CR = load('air2lean_ci_reuse', 'ci-reuse.py')
REGEN = load('air2lean_regen', 'regen.py')
DEPS = load('air2lean_lean_deps', 'lean-deps.py')
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
    cache: bool = True
    check_argv: list | None = None  # the check alone (a regen step without regenerating)

    def __post_init__(self):
        self.check_argv = self.check_argv or self.argv


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

    Ordering keeps every key exact: nothing that writes a file of the checkout runs while another
    unit runs. The whole-tree generated files (ignored files) come first, side by side; then the
    full build, whose fixture checks and tests read them; then the regen steps one after another
    (each may rewrite committed files that a later step reads), in regen.py's order; then the
    preflight checks, which write nothing, all at once."""
    data = GENERATED.load(ROOT)
    out = []
    for g in data['groups']:
        if g['name'] in GENERATED.cheap(data):
            out.append(Unit('materialize:' + g['name'], [PY, '-B', 'scripts/generated.py', 'regen', '--group', g['name']],
                            outputs=tuple(g['paths'])))
    heavy = [g['name'] for g in data['groups'] if g['name'] not in GENERATED.cheap(data)]
    # As scripts/preflight.sh: CI regenerates these for the tree; offline they stay as they are.
    out.append(Unit('fetch:' + ','.join(heavy), ['bash', '-c', 'python3 -B scripts/generated.py fetch %s || '
                    'echo "note: not fetched; CI regenerates them"' % ' '.join('--group ' + h for h in heavy)],
                    cache=False))
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


# ---- keys -------------------------------------------------------------------------------------

class Keys:
    """Inputs and keys of the units over one state of the checkout (a snapshot commit)."""

    def __init__(self, base):
        self.commit = CR.snapshot(ROOT)
        self.tree = CR.tracked_tree(ROOT, self.commit)
        self.declared = CR.local_declarations(ROOT)
        self.head = git('rev-parse', 'HEAD').strip()
        self.base_commit = git('rev-parse', base, check=False).strip() or base
        self.sources = DEPS.Sources()
        self._inputs = {}

    def modules(self, entry):
        """Package modules of a `lean` entry: a module, a .lean file or a directory of them."""
        if entry.endswith('.lean') or (ROOT / entry).is_dir():
            files = [f for f in self.tree if f.endswith('.lean') and (f == entry or f.startswith(entry.rstrip('/') + '/'))]
            return set().union(*({f[:-5].replace('/', '.')} | DEPS.imports(ROOT / f) for f in files))
        return {entry}

    def inputs(self, unit):
        """CR.Inputs of the unit: its declaration with the sources of its Lean closure as exact
        paths (DEPS.Sources), or every file."""
        if unit.name not in self._inputs:
            entry = self.declared.get(unit.name)
            if entry is None:
                self._inputs[unit.name] = CR.Inputs(['**'])
            else:
                modules = self.sources.closure(set().union(*(self.modules(e) for e in entry.get('lean', ()))))
                self._inputs[unit.name] = CR.Inputs(entry['inputs'], entry.get('exclude', ()),
                                                    sorted(m.replace('.', '/') + '.lean' for m in modules))
        return self._inputs[unit.name]

    def declared_unit(self, unit):
        return unit.name in self.declared

    def files(self, unit):
        return self.affected(unit, self.tree)

    def key(self, unit):
        inputs = self.inputs(unit)
        preimage = {'schema': SCHEMA, 'unit': unit.name, 'argv': normalized(unit.argv),
                    'runner': [platform.system(), platform.machine()],
                    'gate': [list(self.tree.get(f, ())) for f in SELF],
                    **CR.content_preimage(ROOT, inputs, self.commit, tree=self.tree)}
        if not self.declared_unit(unit):
            # A unit with the whole tree may also read git history and the whole-tree generated
            # files (except the units that make those, side by side).
            preimage['git'] = [self.head, self.base_commit]
            if not unit.outputs:
                preimage['generated'] = CR.generated_digests(ROOT)
        return CR.key_of(preimage)

    def affected(self, unit, changed):
        """The changed files among the unit's inputs (a whole-tree unit: every change)."""
        inputs = self.inputs(unit)
        return sorted(f for f in changed if inputs.content(f))


def dirty_state():
    """Content digest of every file that differs from HEAD or is new (None: deleted)."""
    return {f: CR.sha256((ROOT / f).read_bytes()) if (ROOT / f).is_file() else None
            for f in CR.changed_files(ROOT, 'HEAD')}


def rewritten(before):
    """The files whose content changed since BEFORE (a dirty_state())."""
    after = dirty_state()
    return {f for f in before.keys() | after.keys() if before.get(f, 'HEAD') != after.get(f, 'HEAD')}


# ---- running ----------------------------------------------------------------------------------

def restricted_run(argv, inputs, label, commit, logfile, root=ROOT):
    """Exit code of ARGV in a worktree of COMMIT restricted to INPUTS (CR.RestrictedWorktree), with
    ROOT's Lake build cloned in (copy-on-write), so it builds nothing the full build did not. A
    withheld file that the run changed fails it."""
    check_tree = load('air2lean_check_tree', 'check-tree.py')
    worktree = CR.RestrictedWorktree(root, inputs, label, commit)
    with open(logfile, 'ab') as out:
        with worktree as dest:
            if (root / '.lake' / 'build').is_dir():
                check_tree.clone_tree(root / '.lake' / 'build', dest / '.lake' / 'build')
            out.write(b'gate: restricted run of %s in %s\n' % (label.encode(), str(dest).encode()))
            code = execute(argv, dest, out)
            if code:  # the guarded steps' own logs go away with the worktree: keep their tails
                for guard_log in sorted((dest / '.lake' / 'regen').glob('*.guard.log')):
                    out.write(b'--- %s (tail)\n' % guard_log.name.encode())
                    out.write(b'\n'.join(guard_log.read_bytes().splitlines()[-40:]) + b'\n')
        for problem in worktree.problems:
            out.write(('gate: %s\n' % problem).encode())
    return code or (1 if worktree.problems else 0)


class Run:
    def __init__(self, a, chosen):
        self.a, self.units = a, chosen
        self.results, self.lock = {}, threading.Lock()
        self.changed = CR.changed_files(ROOT, a.base)
        self.written, self.published = set(), []
        self.logs = Path(a.logs) if a.logs else Path(tempfile.mkdtemp(prefix='air2lean-gate.'))
        self.logs.mkdir(parents=True, exist_ok=True)
        self.keys_state = Keys(a.base)
        self.start_tree = self.keys_state.commit

    def keys(self):
        """Keys over the current checkout state (recomputed after a unit rewrote files)."""
        with self.lock:
            if self.keys_state is None:
                self.keys_state = Keys(self.a.base)
            return self.keys_state

    def invalidate(self):
        with self.lock:
            self.keys_state = None

    def external_changes(self):
        """Files that changed during the run although no unit wrote them (an edit meanwhile)."""
        out = git('diff', '--name-only', '--no-renames', '-z', self.start_tree, CR.snapshot(ROOT))
        return sorted(f for f in out.split('\0') if f and f not in self.written)

    def withdraw(self):
        """Remove the records this run published: they may be keyed by content it never checked."""
        for key in self.published:
            CR.withdraw_local(key)

    def one(self, unit):
        start = time.monotonic()
        keys = self.keys()
        key = keys.key(unit) if unit.cache else None
        if key and not self.a.no_cache and (entry := CR.lookup_local(key)):
            for rel in unit.outputs:
                if (entry / 'files' / rel).is_file():
                    (ROOT / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(entry / 'files' / rel, ROOT / rel)
            return 'cached', 0.0, []
        before, notes, wrote = dirty_state(), [], None
        path = self.logs / (re.sub(r'[^\w.-]+', '_', unit.name) + '.log')
        path.write_bytes(b'')
        if not keys.declared_unit(unit):
            with open(path, 'ab') as out:
                code = execute(unit.argv, ROOT, out)
        else:
            # A declared unit passes only restricted to its declaration; regeneration runs in the
            # checkout, then the check again, restricted (a restricted run writes no checkout file).
            code = restricted_run(unit.check_argv, keys.inputs(unit), unit.name, keys.commit, path)
            if code != 0 and unit.argv != unit.check_argv:
                with open(path, 'ab') as out:
                    code = execute(unit.argv, ROOT, out)
                wrote = rewritten(before)
                if code == 0 and not wrote:
                    code, notes = 1, ['passes in the checkout but not restricted to its declared inputs: '
                                      'widen %s in %s' % (unit.name, CR.LOCAL_DECLARATIONS)]
                elif code == 0:
                    self.invalidate()
                    fresh = self.keys()
                    code = restricted_run(unit.check_argv, fresh.inputs(unit), unit.name, fresh.commit, path)
        seconds = time.monotonic() - start
        wrote = rewritten(before) if wrote is None else wrote
        if wrote:
            with self.lock:
                self.written |= wrote
            self.invalidate()
        if code != 0:
            tail = path.read_text(errors='replace').strip().splitlines()[-15:]
            return 'FAILED', seconds, notes + ['log: %s' % path] + ['  ' + l for l in tail]
        if unit.cache:
            # No other unit writes while this one runs (units()), so the run checked the state
            # of KEY, or, when it regenerated files, the state after that (its last step checks it).
            final = self.keys().key(unit) if wrote else key
            body = {'unit': unit.name, 'seconds': round(seconds, 1), 'worktree': str(ROOT), 'time': time.time()}
            CR.record_local(final, body, [(rel, ROOT / rel) for rel in unit.outputs if (ROOT / rel).is_file()])
            with self.lock:
                self.published.append(final)
        if keys.declared_unit(unit) and (affected := keys.affected(unit, self.changed)):
            notes.append('changed inputs: ' + ', '.join(affected[:6]) + (' ...' if len(affected) > 6 else ''))
        return ('wrote ' + ', '.join(sorted(wrote))) if wrote else 'ran', seconds, notes

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


def verify(names, base):
    """Run each declared unit's check restricted to its declaration (`scripts/gate.sh verify UNIT`)."""
    by_name = {u.name: u for u in units(base, check=True)}
    keys, failures = Keys(base), 0
    for name in names:
        unit = by_name.get(name)
        if unit is None or not keys.declared_unit(unit):
            raise SystemExit('gate verify: %s is no unit with declared inputs (%s)' % (name, ', '.join(keys.declared)))
        logfile = Path(tempfile.mkdtemp(prefix='air2lean-gate-verify.')) / 'unit.log'
        code = restricted_run(unit.check_argv, keys.inputs(unit), name, keys.commit, logfile)
        log('verify %s: %s (log %s)' % (name, 'passed' if code == 0 else 'FAILED (exit %d)' % code, logfile))
        failures += code != 0
    return 1 if failures else 0


# ---- main -------------------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', nargs='*', help='`verify UNIT...`')
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
    if a.command[:1] == ['verify']:
        return verify(a.command[1:], a.base)
    if a.command:
        parser.error('unknown command ' + ' '.join(a.command))
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
        keys, changed = Keys(a.base), CR.changed_files(ROOT, a.base)
        rows = [{'unit': u.name, 'after': list(u.after), 'declared': keys.declared_unit(u),
                 'inputs': len(keys.files(u)), 'affected': keys.affected(u, changed)[:20],
                 'cached': bool(u.cache and CR.lookup_local(keys.key(u)))} for u in chosen]
        if a.json:
            print(json.dumps(rows, indent=1))
        else:
            for r in rows:
                print('%-58s %-9s %5d inputs  %s' % (r['unit'], 'cached' if r['cached'] else
                                                    ('affected' if r['affected'] else 'unchanged'),
                                                    r['inputs'], ' '.join(r['affected'][:3])))
        return 0
    start, written = time.monotonic(), set()
    # A pass that regenerated files checked them only from its later units on (the full build ran
    # before): a second pass checks the new state, and every unit it did not affect hits.
    for attempt in (1, 2):
        run = Run(a, chosen)
        log('pass %d: base %s; %d files changed; %d units, %d at once; logs %s' % (
            attempt, a.base[:12], len(run.changed), len(chosen), a.jobs, run.logs))
        failed = run.go()
        if edited := run.external_changes():
            run.withdraw()
            log('the checkout changed during the run (%s): nothing of it is recorded; run the gate again'
                % ', '.join(edited[:5]))
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
