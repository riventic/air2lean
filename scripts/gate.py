#!/usr/bin/env python3
"""The pre-merge gate: every local check a PR needs before it merges, affected-only and cached.

    scripts/gate.sh [--base REF] [--check] [--only UNIT[,UNIT]] [--jobs N] [--no-cache] [--logs DIR]
    scripts/gate.sh --list [--json] [--base REF]
    scripts/gate.sh verify UNIT...

One command for the sequence a PR ran before (docs/ci.md#pre-merge-gate): the full build with
the proof-fixture checks, `scripts/regen.sh --pr`, `scripts/preflight.sh` and
`scripts/proof-framework.py --base origin/main`. Its units:

- `full-build`: scripts/full-build.sh (Lake builds, the standalone Lean files, the proof-fixture
  checks CI runs). Lake, lean-deps.py and fixture-checks.py remember their own results by input.
- `regen:STEP` for each PR-scoped step of scripts/regen.py: the step regenerates its committed
  output when it is stale (`--check`: the unit fails instead), then checks it.
- `materialize`: the whole-tree generated files (assurance/generated.json): the cheap groups
  regenerated, stored with the unit's result and restored on a hit; the provenance fixtures
  fetched from the `generated` branch as scripts/preflight.sh does.
- `preflight:LABEL` for each check of scripts/preflight.sh, parsed from it (a new check there is a
  new unit here), except those another unit runs already: the full build, the generated-module
  check (regen:gen) and every check a regen step runs (the same command). proof-framework.py
  compares with the base (--base).

Cache. A passing unit is remembered under a key, `$AIR2LEAN_CAS_DIR/gate/<key>` (else
.lake/gate/): SHA-256 of the unit's command, the gate's own sources, the host, the names of
every file of the checkout (tracked and new, not ignored: a gate that lists a directory sees
them) and the content of the unit's inputs. A unit with an input declaration (DECLARED) keys
- the files its path patterns select;
- the sources of the package modules a named Lean module or file imports, transitively;
- the files and package modules that the scanned scripts name, followed transitively (the
  scanner of scripts/fixture-checks.py);
- the unit's runner (scripts/regen.py and what it loads).
Every other unit keys the content of the whole checkout and of the whole-tree generated files,
and HEAD and the base revision when a script it runs reads git history. So a unit is skipped
only when a run with the same inputs passed, in any worktree; a changed input is another key.
`verify UNIT` runs a declared unit in a fresh worktree of HEAD in which every tracked file outside
its declaration is unreadable (as CI's restricted checkout, docs/ci.md#restricted-checkout), so a
declaration that is too narrow fails there.

Affected: the units with an input that changed since the base (default: the merge base of HEAD
and origin/main); `--list` names them and the gate reports the changed inputs of each unit it
runs. Units run in parallel (--jobs); those that build or run Lean in the checkout wait for each
other through scripts/build-guard.py (one build per checkout, within the machine's memory budget).
Exit 0: every unit passed (files a regen unit rewrote are listed: commit them); 1: a unit
failed; 2: usage.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import fnmatch
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
PY = sys.executable
SCHEMA = 1
LAKE_FILES = ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json')
# The gate's own machinery: part of every key.
SELF = ('scripts/gate.py', 'scripts/gate.sh', 'scripts/fixture-checks.py')
GIT_USE = re.compile(r"""['"]git['"]|\bgit\s+(?:-C\s+\S+\s+)?(?:log|rev-parse|show|diff|merge-base|cat-file|"""
                     r"""rev-list|notes|for-each-ref|describe|blame|status|fetch)\b""")


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FC = load('air2lean_fixture_checks', 'fixture-checks.py')
REGEN = load('air2lean_regen', 'regen.py')
GENERATED = REGEN.GENERATED


def log(message):
    print('gate: ' + message, file=sys.stderr, flush=True)


def git(*args, root=ROOT, check=True):
    done = subprocess.run(['git', *args], cwd=root, capture_output=True, text=True)
    if check and done.returncode:
        raise SystemExit('gate: git %s: %s' % (' '.join(args), done.stderr.strip()))
    return done.stdout.strip() if done.returncode == 0 else None


# ---- units ------------------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class Inputs:
    """A unit's declared inputs: path patterns (`dir/**`, `dir/*.py`, exact) and Lean modules,
    .lean files or directories of them whose package imports count, transitively. A declared
    unit only passes in a restricted worktree that holds nothing else (restricted_run), so a
    declaration that misses an input fails the unit; it never lets a stale result stand."""
    paths: tuple = ()
    lean: tuple = ()


# What runs a regen step: regen.py and what it loads (the guard, the cache, the registry).
REGEN_RUNNER = ('scripts/regen.py', 'scripts/regen.sh', 'scripts/cas.py', 'scripts/generated.py',
                'scripts/build-guard.py', 'assurance/generated.json', 'compatibility.json',
                'zig-patch/versions.toml')
# The assurance extractor (scripts/assumptions.py) and what it reads.
EXTRACTOR = ('scripts/assumptions.sh', 'scripts/assumptions.py', 'scripts/premise_markers.py',
             'scripts/gen-integrity.py', 'scripts/float-semantics.py', 'scripts/lean-deps.py',
             'scripts/claims.py', 'scripts/outcomes.py', 'scripts/premises.py', 'assurance/**', 'tools/**', *LAKE_FILES)

# Units that cost tens of seconds and that a whole-checkout key would rerun on every change.
DECLARED = {
    'regen:claims': Inputs(
        paths=(*REGEN_RUNNER, *EXTRACTOR, 'tests/roadmap/claims/**', 'ZigLean/Witnesses/**'),
        lean=('tests/roadmap/claims/Fixture.lean', 'ZigLean.Bit', 'ZigLean/Witnesses', 'tools.Assurance')),
    'regen:audit-exposure': Inputs(
        paths=(*REGEN_RUNNER, *EXTRACTOR, 'tests/roadmap/architecture-audit/claims/**'),
        lean=('tests/roadmap/architecture-audit/claims/AuditClaims', 'ZigLean', 'tools.Assurance',
              'Proofs.Asm.Gen', 'ZigLean.Witness')),
}


@dataclasses.dataclass
class Unit:
    name: str
    argv: list
    after: tuple = ()              # units that run first
    requires: tuple = ()           # of those, the ones that must have passed
    inputs: Inputs | None = None   # None: the whole checkout
    outputs: tuple = ()            # untracked files the unit produces (stored with its result)
    cache: bool = True
    scripts: tuple = ()            # the scripts it runs (git-history detection of whole-tree keys)
    check_argv: list | None = None  # the check alone (a regen step without regenerating)

    def __post_init__(self):
        self.check_argv = self.check_argv or self.argv


def preflight_checks(text):
    """[(label, argv)] of scripts/preflight.sh's `check 'LABEL' CMD...` lines."""
    out = []
    for line in text.splitlines():
        if line.startswith("check '"):
            words = shlex.split(line)
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
    """{step: [normalized check argv]} of every regen step whose check is a plain command."""
    out = {}
    for name, scope, _, function in REGEN.STEPS:
        cells = dict(zip(function.__code__.co_freevars, function.__closure__ or ())) if function else {}
        if 'check_argv' in cells:
            out[name] = [normalized(cells['check_argv'].cell_contents)]
    out['inventory'] = [['scripts/theorem-inventory.py', 'check']]
    return out


GENERATORS = {'coverage': ('scripts/coverage.py',), 'premise-index': ('scripts/premises.py',)}


def units(base, check):
    """Every unit of the gate, in dependency order.

    Ordering keeps every key exact: nothing that writes a file of the checkout runs while another
    unit runs. The full build and the whole-tree generated files (which write only ignored files)
    come first, side by side; then the regen steps one after another (each may rewrite committed
    files that a later step reads), in regen.py's order; then the preflight checks, which write
    nothing, all at once."""
    groups = GENERATED.load(ROOT)['groups']
    out = [Unit('full-build', ['bash', 'scripts/full-build.sh'], cache=False, scripts=('scripts/full-build.sh',))]
    for g in groups:
        if not g.get('heavy'):
            out.append(Unit('materialize:' + g['name'], [PY, '-B', 'scripts/generated.py', 'regen', '--group', g['name']],
                            outputs=tuple(g['paths']), scripts=GENERATORS.get(g['generator'], ('scripts/generated.py',))))
    heavy = [g['name'] for g in groups if g.get('heavy')]
    # As scripts/preflight.sh: CI regenerates these for the tree; offline they stay as they are.
    out.append(Unit('fetch:' + ','.join(heavy), ['bash', '-c', 'python3 -B scripts/generated.py fetch %s || '
                    'echo "note: not fetched; CI regenerates them"' % ' '.join('--group ' + h for h in heavy)],
                    cache=False))
    first = tuple(u.name for u in out)
    run = {name for name, scope, _, _ in REGEN.STEPS if scope == 'pr'}
    covered = {tuple(c) for name, checks in regen_checks().items() if name in run for c in checks}
    previous = first
    for name, scope, _, _ in REGEN.STEPS:
        if scope != 'pr' or name == 'translator':
            continue
        argv = [PY, '-B', 'scripts/regen.py', '--pr', '--only', name, '--no-commit', '--no-translator', '--no-gc']
        out.append(Unit('regen:' + name, argv + (['--check'] if check else []), after=previous,
                        requires=('full-build',), inputs=DECLARED.get('regen:' + name),
                        scripts=('scripts/regen.py',), check_argv=argv + ['--check']))
        previous = first + ('regen:' + name,)
    for label, argv in preflight_checks((ROOT / 'scripts/preflight.sh').read_text()):
        script = script_of(argv)
        if script in ('scripts/generated.py', 'scripts/full-build.sh', 'scripts/gen-integrity.py') \
                or tuple(normalized(argv)) in covered:
            continue
        if script == 'scripts/proof-framework.py' and '--base' not in argv:
            argv = argv + ['--base', base]
        out.append(Unit('preflight:' + label, argv, after=previous, scripts=(script,) if script else ()))
    return out


# ---- keys -------------------------------------------------------------------------------------

class Keys:
    """Input files and keys of units over one state of the checkout."""

    def __init__(self, base):
        self.tree = FC.Tree()
        self.keyer = FC.Keyer(self.tree)
        self.base = base
        self.names = hashlib.sha256('\0'.join(self.tree.files).encode()).hexdigest()
        self.toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        self._git = {}

    def module(self, entry):
        """Package modules of ENTRY (a module, a .lean file or a directory of them)."""
        path = ROOT / entry
        if path.is_dir():
            files = [f for f in self.tree.under(entry) if f.endswith('.lean')]
        elif entry.endswith('.lean'):
            files = [entry]
        else:
            return {entry} if entry in self.keyer.lib else set()
        own = {f[:-5].replace('/', '.') for f in files}
        return {m for f in files for m in FC.DEPS.imports(ROOT / f) | own if m in self.keyer.lib}

    def declared(self, inputs):
        chosen = {f for f in self.tree.files if any(match(f, p) for p in inputs.paths)}
        modules = set()
        for entry in inputs.lean:
            modules |= self.module(entry)
        for m in sorted(modules):
            chosen |= {self.keyer.lib[i] for i in self.keyer.imports(m)}
        return sorted(chosen)

    def files(self, unit):
        if unit.inputs is not None:
            return self.declared(unit.inputs)
        return self.tree.files

    def reads_git(self, unit):
        """Whether a script the unit runs, or one it names, may read git history."""
        if not unit.scripts:  # a command without a script of its own (unittest discover): assume so
            return True
        if unit.name not in self._git:
            todo, seen, found = [s for s in unit.scripts if s in self.tree.file_set], set(), False
            while todo and not found:
                f = todo.pop()
                if f in seen:
                    continue
                seen.add(f)
                text = (ROOT / f).read_text(errors='replace')
                found = bool(GIT_USE.search(text))
                todo += sorted(g for g in self.keyer.scan(f)[0] if g.startswith('scripts/') and g not in seen)
            self._git[unit.name] = found
        return self._git[unit.name]

    def key(self, unit):
        whole = unit.inputs is None
        extra = {}
        if whole:
            extra['generated'] = {p: digest(ROOT / p) for g in GENERATED.load(ROOT)['groups'] for p in g['paths']
                                  if (ROOT / p).is_file() and p not in unit.outputs}
            if self.reads_git(unit):
                extra['git'] = [git('rev-parse', 'HEAD'), git('rev-parse', self.base)]
        h = hashlib.sha256(json.dumps({
            'schema': SCHEMA, 'unit': unit.name, 'argv': [str(a).replace(PY, 'python3') for a in unit.argv],
            'host': [platform.system(), platform.machine()], 'toolchain': self.toolchain,
            'names': self.names, 'extra': extra,
            'self': [self.tree.digest(f) for f in SELF if f in self.tree.file_set]}, sort_keys=True).encode())
        for f in self.files(unit):
            h.update(f.encode() + b'\0' + self.tree.digest(f).encode() + b'\n')
        return h.hexdigest()

    def affected(self, unit, changed):
        """The changed files among the unit's inputs (a whole-checkout unit: every change)."""
        files = set(self.files(unit))
        return sorted(f for f in changed if f in files or (unit.inputs is None))


def match(path, pattern):
    if pattern.endswith('/**'):
        return path.startswith(pattern[:-2])
    return path == pattern or fnmatch.fnmatchcase(path, pattern)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def changed_since(base):
    """Files changed since BASE: committed, staged, unstaged and new (not ignored)."""
    out = git('diff', '--name-only', '-z', base) or ''
    new = git('ls-files', '-o', '--exclude-standard', '-z') or ''
    return sorted({f for f in (out + '\0' + new).split('\0') if f})


# ---- store ------------------------------------------------------------------------------------

def store_dir():
    cas = os.environ.get('AIR2LEAN_CAS_DIR')
    return Path(cas).expanduser() / 'gate' if cas else ROOT / '.lake' / 'gate'


def recorded(key):
    entry = store_dir() / key
    return entry if (entry / 'pass.json').is_file() else None


def record(key, unit, seconds):
    """Publish a pass (with the unit's outputs) under KEY: built aside, then one rename."""
    store = store_dir()
    store.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix='.tmp-', dir=store))
    for rel in unit.outputs:
        if (ROOT / rel).is_file():
            (staging / 'outputs' / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, staging / 'outputs' / rel)
    (staging / 'pass.json').write_text(json.dumps({'unit': unit.name, 'seconds': round(seconds, 1),
                                                   'worktree': str(ROOT), 'time': time.time()}) + '\n')
    try:
        os.rename(staging, store / key)
    except OSError:  # another worktree published the same key meanwhile
        shutil.rmtree(staging, ignore_errors=True)


def restore(entry, unit):
    for rel in unit.outputs:
        source = entry / 'outputs' / rel
        if source.is_file():
            (ROOT / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, ROOT / rel)
    os.utime(entry / 'pass.json')  # last use, for eviction


# ---- running ----------------------------------------------------------------------------------

def dirty_state():
    out = git('status', '--porcelain', '--untracked-files=no') or ''
    return {line[3:]: digest(ROOT / line[3:]) if (ROOT / line[3:]).is_file() else None for line in out.splitlines()}


class Run:
    def __init__(self, a, chosen):
        self.a, self.units = a, chosen
        self.results, self.lock = {}, threading.Lock()
        self.changed = changed_since(a.base)
        self.written = set()
        self.logs = Path(a.logs) if a.logs else Path(tempfile.mkdtemp(prefix='air2lean-gate.'))
        self.logs.mkdir(parents=True, exist_ok=True)
        self.keys_state = None

    def keys(self):
        """Keys over the current checkout state (recomputed after a unit rewrote files)."""
        with self.lock:
            if self.keys_state is None:
                self.keys_state = Keys(self.a.base)
            return self.keys_state

    def invalidate(self):
        with self.lock:
            self.keys_state = None

    def one(self, unit):
        start = time.monotonic()
        keys = self.keys() if unit.cache else None
        key = keys.key(unit) if keys else None
        if key and not self.a.no_cache and (entry := recorded(key)):
            restore(entry, unit)
            return 'cached', 0.0, []
        affected = keys.affected(unit, self.changed) if keys else []
        before = dirty_state()
        path = self.logs / (re.sub(r'[^\w.-]+', '_', unit.name) + '.log')
        path.write_bytes(b'')
        notes = []
        if unit.inputs is None:
            code = self.plain(unit.argv, path)
        else:
            # A declared unit passes only restricted to its declaration; regeneration runs in the
            # checkout, then the check again, restricted.
            code = restricted_run(unit, unit.check_argv, keys.files(unit), path)
            if code != 0 and unit.argv != unit.check_argv:
                code = self.plain(unit.argv, path)
                if code == 0 and dirty_state() == before:
                    code, notes = 1, ['passes in the checkout but not restricted to its declared inputs: '
                                      'widen DECLARED[%r] in scripts/gate.py' % unit.name]
                elif code == 0:
                    self.invalidate()
                    code = restricted_run(unit, unit.check_argv, self.keys().files(unit), path)
        seconds = time.monotonic() - start
        after = dirty_state()
        wrote = {p for p, d in after.items() if before.get(p, '') != d}
        if wrote:
            with self.lock:
                self.written |= wrote
            self.invalidate()
        if code != 0:
            tail = path.read_text(errors='replace').strip().splitlines()[-15:]
            return 'FAILED', seconds, notes + ['log: %s' % path] + ['  ' + l for l in tail]
        if unit.cache:
            record(self.keys().key(unit), unit, seconds)
        notes = ['changed inputs: ' + ', '.join(affected[:6]) + (' ...' if len(affected) > 6 else '')] \
            if affected and unit.inputs is not None else []
        return ('wrote ' + ', '.join(sorted(wrote))) if wrote else 'ran', seconds, notes

    @staticmethod
    def plain(argv, path):
        with open(path, 'ab') as out:
            return subprocess.run([str(a) for a in argv], cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                  env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')).returncode

    def go(self):
        pending = {u.name: u for u in self.units}
        names = set(pending)
        done, failed = set(), set()
        running = {}
        with concurrent.futures.ThreadPoolExecutor(self.a.jobs) as pool:
            while pending or running:
                for name, unit in list(pending.items()):
                    if not all(n in done or n in failed for n in unit.after if n in names):
                        continue
                    if broken := [n for n in unit.requires if n in failed]:
                        del pending[name]
                        failed.add(name)
                        self.results[name] = ('skipped: %s failed' % ', '.join(broken), 0.0, [])
                    else:
                        del pending[name]
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


def report(run, total):
    rows = [(u.name, *run.results.get(u.name, ('not run', 0.0, []))) for u in run.units]
    counts = {}
    for _, status, _, _ in rows:
        counts[status.split(' ')[0]] = counts.get(status.split(' ')[0], 0) + 1
    print('\ngate: %s in %.0f s (%s)' % ('passed' if not any(s.startswith(('FAILED', 'skipped')) for _, s, _, _ in rows)
                                          else 'FAILED', total, ', '.join('%d %s' % (n, s) for s, n in sorted(counts.items()))))
    for name, status, seconds, notes in rows:
        if status.startswith(('FAILED', 'skipped')):
            print('  %s: %s' % (name, status))
            for note in notes:
                print('    ' + note)
    if run.written:
        print('gate: regenerated, commit them: ' + ' '.join(sorted(run.written)))


# ---- restricted runs --------------------------------------------------------------------------

def restricted_run(unit, argv, keep, logfile):
    """Exit code of ARGV run in a fresh worktree that holds the checkout's current content of
    KEEP (its declared inputs) and nothing else readable: every other tracked file is withheld
    (mode 000, skip-worktree; reading it fails), untracked files are absent. The checkout's Lake
    build is cloned in (copy-on-write), so the run builds nothing the full build did not."""
    check_tree = load('air2lean_check_tree', 'check-tree.py')
    scratch = Path(tempfile.mkdtemp(prefix='air2lean-gate-restricted.'))
    dest = scratch / 'tree'
    git('worktree', 'add', '-q', '--detach', str(dest), 'HEAD')
    try:
        tracked = [f for f in git('ls-files', '-z', root=dest).split('\0') if f]
        for f in keep:  # the checkout's state of the inputs: edited, new or deleted
            source, target = ROOT / f, dest / f
            if source.is_file():
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.is_file() or target.read_bytes() != source.read_bytes():
                    shutil.copy2(source, target)
        for f in set(tracked) - set(keep):
            if (dest / f).is_file() and not (dest / f).is_symlink() and not (ROOT / f).exists():
                (dest / f).unlink()  # deleted in the checkout
        withheld = [f for f in tracked if f not in keep and (dest / f).is_file() and not (dest / f).is_symlink()]
        for i in range(0, len(withheld), 500):
            git('update-index', '--skip-worktree', '--', *withheld[i:i + 500], root=dest)
        for f in withheld:
            (dest / f).chmod(0)
        if (ROOT / '.lake' / 'build').is_dir():
            check_tree.clone_tree(ROOT / '.lake' / 'build', dest / '.lake' / 'build')
        with open(logfile, 'ab') as out:
            out.write(b'gate: restricted run in %s: %d inputs, %d tracked files withheld\n'
                      % (str(dest).encode(), len(keep), len(withheld)))
            out.flush()
            code = subprocess.run([str(a) for a in argv], cwd=dest, stdout=out, stderr=subprocess.STDOUT,
                                  env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')).returncode
            if code:  # the guarded steps' own logs go away with the worktree: keep their tails
                for guard_log in sorted((dest / '.lake' / 'regen').glob('*.guard.log')):
                    out.write(b'--- %s (tail)\n' % guard_log.name.encode())
                    out.write(b'\n'.join(guard_log.read_bytes().splitlines()[-40:]) + b'\n')
            return code
    finally:
        for f in git('ls-files', '-z', root=dest, check=False).split('\0'):
            if f and (dest / f).is_file() and not (dest / f).is_symlink():
                (dest / f).chmod(stat.S_IRUSR | stat.S_IWUSR)
        git('worktree', 'remove', '--force', str(dest), check=False)
        shutil.rmtree(scratch, ignore_errors=True)


def verify(names, base):
    """Run each declared unit restricted to its declaration (`scripts/gate.sh verify UNIT`)."""
    by_name = {u.name: u for u in units(base, check=True)}
    failures = 0
    for name in names:
        unit = by_name.get(name)
        if unit is None or unit.inputs is None:
            raise SystemExit('gate verify: %s is no unit with declared inputs (%s)' % (name, ', '.join(DECLARED)))
        logfile = Path(tempfile.mkdtemp(prefix='air2lean-gate-verify.')) / 'unit.log'
        code = restricted_run(unit, unit.argv, Keys(base).files(unit), logfile)
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
    a.base = a.base or git('merge-base', 'HEAD', 'origin/main', check=False) or 'origin/main'
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
        keys, changed = Keys(a.base), changed_since(a.base)
        rows = [{'unit': u.name, 'after': list(u.after), 'declared': u.inputs is not None,
                 'inputs': len(keys.files(u)), 'affected': keys.affected(u, changed)[:20],
                 'cached': bool(u.cache and recorded(keys.key(u)))} for u in chosen]
        if a.json:
            print(json.dumps(rows, indent=1))
        else:
            for r in rows:
                print('%-58s %-9s %5d inputs  %s' % (r['unit'], 'cached' if r['cached'] else
                                                    ('affected' if r['affected'] else 'unchanged'),
                                                    r['inputs'], ' '.join(r['affected'][:3])))
        return 0
    start = time.monotonic()
    run = Run(a, chosen)
    log('base %s; %d files changed; %d units, %d at once; logs %s' % (
        a.base[:12], len(run.changed), len(chosen), a.jobs, run.logs))
    failed = run.go()
    report(run, time.monotonic() - start)
    # Eviction of the shared cache (at most hourly), off the critical path: detached.
    subprocess.Popen([PY, '-B', '-c', 'import runpy; runpy.run_path("scripts/cas.py", run_name="cas").get("gc_if_due")()'],
                     cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    return 1 if failed or len(run.results) < len(chosen) else 0


if __name__ == '__main__':
    sys.exit(main())
