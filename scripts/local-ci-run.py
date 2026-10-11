#!/usr/bin/env python3
"""Local CI runner behind `scripts/local-ci.sh --part ... --version ... --changed`.

Runs the steps of the rows of .github/workflows/ci.yml, read from that file (nothing is copied
from it), where GitHub would run them:

  aarch64-macos rows (macos)                          on this Mac, in a private workspace
  aarch64-linux rows (aarch64-linux, build-modes-..., bitops-native-arm)
                                                      in a native linux/arm64 container
  x86_64-linux rows (lake, test)                      in a linux/amd64 container (Rosetta)

GitHub-only actions are emulated: checkout (a snapshot of the tracked files), cache (persistent
volumes), upload-artifact (copied to the results directory). Install steps run exactly as written
once per recipe text, into persistent tool directories; the recipe's text is the cache key, so a
changed recipe re-runs by itself. Anything else the runner cannot interpret fails the row.
Condition syntax is evaluated by scripts/local-ci-steps.py's `expression`.
See docs/local-ci.md.
"""
import argparse
import ast
import datetime
import fnmatch
import glob
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

REPO = Path(__file__).resolve().parents[1]
HOME = Path(os.environ.get('AIR2LEAN_LOCAL_CI_HOME', Path.home() / '.cache/air2lean/local-ci'))
WORKFLOW = '.github/workflows/ci.yml'
DEFAULT_VERSION = '0.16.0'
# job -> where it runs. The `all-checks` aggregator has no steps of its own to run.
PLACEMENT = {'lake': 'amd64', 'test': 'amd64', 'macos': 'host', 'preflight': 'host', 'aarch64-linux': 'arm64',
             'build-modes-aarch64-linux': 'arm64', 'bitops-native-arm': 'arm64'}
# No row of their own. `zig-air` and `generated` produce what the rows download in CI: here the
# rows build the patched compiler into a persistent cache and `scripts/generated.py materialize`
# (run on the host before the rows) provides the generated files. `provenance` regenerates the
# provenance fixtures twice from a Lake build and a patched compiler (minutes of CPU on every run,
# and materialize fetches the published ones); use `scripts/generated.py regen --group provenance`
# for it. `all-checks` aggregates job results.
IGNORED_JOBS = {'all-checks', 'zig-air', 'generated', 'provenance'}
# Steps with no local meaning, recognised by what they run (not by name): the reuse machinery and
# trace coverage (local runs never reuse, trace or record), the system packages (in the image), and
# the in-run artifact hand-over between jobs (the substitutes are in Job.run_step).
CI_ONLY_CODE = ('scripts/ci-reuse.py', 'sudo apt-get', 'lake-root.tar.zst', 'zig-air.tar', 'scripts/generated.py install')
# Steps that cannot give CI's answer in the emulated container, by step name. They are skipped
# visibly (summary and steps.json), never silently.
EMULATION_SKIPS = {
    'Performance budget regression gate (portable)':
        'wall-clock budgets: Rosetta adds ~1 s start-up to every Lean process (baselines are 0.03-0.1 s)',
}
# Docker caps, per container; one container runs at a time (the Docker VM has ~15 GiB).
MEMORY = os.environ.get('AIR2LEAN_LOCAL_MEMORY', '9g')
CPUS = os.environ.get('AIR2LEAN_LOCAL_CPUS', '6')
LEAN_THREADS = os.environ.get('AIR2LEAN_LOCAL_LEAN_THREADS', '2')
LOCK_DIR = Path(os.environ.get('AIR2LEAN_LOCAL_LOCK_DIR', Path.home() / '.cache/air2lean'))


def ensure_yaml():
    """PyYAML for the host Python: a private venv when the system one lacks it."""
    try:
        import yaml  # noqa: F401
        return
    except ImportError:
        pass
    venv = HOME / 'venv'
    if Path(sys.prefix).resolve() == venv.resolve():
        raise SystemExit('error: PyYAML is not installable in %s' % venv)
    if not (venv / 'bin/python').exists():
        print('local-ci: creating %s for PyYAML (once)' % venv, file=sys.stderr)
        subprocess.run([sys.executable, '-m', 'venv', str(venv)], check=True)
        subprocess.run([str(venv / 'bin/python'), '-m', 'pip', 'install', '-q', 'PyYAML'], check=True)
    os.execv(str(venv / 'bin/python'), [str(venv / 'bin/python'), *sys.argv])


def load_condition_helpers(root):
    """`expression` and `render` of scripts/local-ci-steps.py, the CI condition evaluator."""
    source = (root / 'scripts/local-ci-steps.py').read_text()
    tree = ast.parse(source)
    wanted = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in ('expression', 'render')]
    if {n.name for n in wanted} != {'expression', 'render'}:
        raise SystemExit('error: scripts/local-ci-steps.py no longer defines expression() and render()')
    namespace = {'re': re}
    exec(compile(ast.Module(body=wanted, type_ignores=[]), 'local-ci-steps.py', 'exec'), namespace)
    return namespace['expression'], namespace['render']


def load_workflow(root):
    import yaml
    return yaml.safe_load((root / WORKFLOW).read_text())


# --- Rows --------------------------------------------------------------------------------

def enumerate_rows(workflow):
    rows = []
    for name, job in workflow['jobs'].items():
        if name in IGNORED_JOBS:
            continue
        if name not in PLACEMENT:
            raise SystemExit('error: ci.yml has a job (%s) that local-ci.sh does not place; add it to '
                             'PLACEMENT in scripts/local-ci-run.py' % name)
        matrix = job.get('strategy', {}).get('matrix', {}).get('include') or [{}]
        for index, entry in enumerate(matrix):
            zig, part = entry.get('zig'), entry.get('part', name if name != 'test' else None)
            row_id = name
            if zig:
                row_id += ':' + zig
            if entry.get('part'):
                row_id += ':' + entry['part']
            if entry.get('shard'):
                row_id += ':%s' % entry['shard']
            rows.append({'id': row_id, 'job': name, 'where': PLACEMENT[name], 'zig': zig, 'part': part,
                         'shard': entry.get('shard'), 'matrix': dict(entry),
                         'timeout': job.get('timeout-minutes', 90)})
    ids = [r['id'] for r in rows]
    if len(ids) != len(set(ids)):
        raise SystemExit('error: duplicate CI row ids')
    return rows


def select_rows(rows, parts, versions):
    """Rows named by --part (a part like golden/ReleaseFast/mutation[:N], or a job like macos)
    and --version. A row without a Zig version matches --version only when --part names it."""
    chosen = []
    for row in rows:
        by_part = not parts or any(
            p == row['part'] or p == row['job'] or p == '%s:%s' % (row['part'], row['shard'])
            or p == row['id'] for p in parts)
        by_version = not versions or row['zig'] in versions or (parts and row['zig'] is None)
        if by_part and by_version:
            chosen.append(row)
    unknown = [p for p in parts if not any(
        p in (r['part'], r['job'], r['id'], '%s:%s' % (r['part'], r['shard'])) for r in rows)]
    if unknown:
        raise SystemExit('error: unknown --part %s (known: %s)' % (
            ', '.join(unknown), ', '.join(sorted({r['part'] or r['job'] for r in rows} | {r['job'] for r in rows}))))
    return chosen


def row_context(row, root):
    values = {'github.workspace': str(root), 'runner.os': {'host': 'macOS'}.get(row['where'], 'Linux'),
              'runner.arch': 'X64' if row['where'] == 'amd64' else 'ARM64', 'strategy.job-index': '0',
              'matrix.zig': row['zig'] or '',  # expression() reads matrix.zig for any condition
              'env.AIR2LEAN_REUSED': '', 'env.AIR2LEAN_RECORD': '', 'env.AIR2LEAN_TRACE_DIR': '',
              'env.AIR2LEAN_REUSE_KEY': ''}
    values.update({'matrix.%s' % k: v for k, v in row['matrix'].items()})
    return values


def evaluate(expression, text, values):
    """expression() (scripts/local-ci-steps.py) without `!=`, which it deliberately rejects for
    the release record; here each `a != b` is decided first and replaced by a truth value."""
    def operand(token):
        return token[1:-1] if token.startswith("'") else str(values.get(token, ''))
    text = re.sub(r"([\w.-]+|'[^']*')\s*!=\s*([\w.-]+|'[^']*')",
                  lambda m: "'1'" if operand(m[1]) != operand(m[2]) else "''", text)
    return expression(text, values)


def active_steps(workflow, row, expression):
    """Steps whose condition holds before any step ran (step outputs read as empty)."""
    values = row_context(row, Path('/work'))
    values['runner.temp'] = '/tmp/runner'
    steps = []
    for step in workflow['jobs'][row['job']]['steps']:
        condition = step.get('if')
        if condition is not None:
            text = str(condition).replace('!cancelled()', "'1'").replace('failure()', "''").replace('success()', "'1'")
            text = re.sub(r'steps\.[\w.-]+', "''", text)
            try:
                if not evaluate(expression, text, values):
                    continue
            except ValueError:
                pass  # unsure: count the step in
        steps.append(step)
    return steps


# --- --changed ---------------------------------------------------------------------------

# Paths whose change can affect any row.
EVERYTHING = ('.github/', 'zig-patch/', 'docker/', 'Dockerfile', 'scripts/local-ci', 'compatibility.json',
              'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'tests/diff/lean-toolchain',
              'tests/diff/lake-manifest.json', '.gitattributes', 'scripts/build-guard.py', 'scripts/workflow-common.sh')
# Translator, runtime library, proofs and the test corpus: every row that builds or translates.
PIPELINE = ('Air2Lean/', 'ZigLean/', 'Proofs/', 'tools/', 'examples/', 'tests/golden/', 'tests/diff/')
# A step that mentions one of these says nothing about a file below it.
BROAD_DIRECTORIES = {'scripts/', 'tests/', 'tests/roadmap/', 'docs/', 'assurance/', 'tools/', 'coverage/'}
NO_LEAN_JOBS = {'aarch64-linux', 'bitops-native-arm'}
FILE_SUFFIXES = ('.py', '.sh', '.lean', '.zig', '.json', '.md', '.toml', '.txt', '.tsv', '.yml')


def changed_paths(root):
    # AIR2LEAN_LOCAL_BASE: compare with another revision than origin/main.
    base = subprocess.run(['git', '-C', str(root), 'merge-base', os.environ.get('AIR2LEAN_LOCAL_BASE', 'origin/main'), 'HEAD'],
                          capture_output=True, text=True)
    if base.returncode:
        return None
    out = subprocess.run(['git', '-C', str(root), 'diff', '--name-only', '--no-renames', '-z', base.stdout.strip()],
                         check=True, capture_output=True, text=True).stdout
    return [p for p in out.split('\0') if p]


def mentions_graph(root, tracked):
    """For each scripts/ file: which scripts/tests/tools files mention its name. Used to follow a
    changed helper up to the CI steps that run it (tests are covered by their directory)."""
    candidates = {}
    for path in tracked:
        if path.startswith('scripts/') and path.endswith(FILE_SUFFIXES):
            candidates.setdefault(os.path.basename(path), set()).add(path)
    pattern = re.compile('|'.join(re.escape(n) for n in sorted(candidates, key=len, reverse=True)))
    users = {}
    for path in tracked:
        if not path.endswith(FILE_SUFFIXES) or not path.startswith(('scripts/', 'tests/', 'tools/')):
            continue
        try:
            text = (root / path).read_text(errors='replace')
        except OSError:
            continue
        for name in set(pattern.findall(text)):
            for target in candidates[name]:
                if target != path:
                    users.setdefault(target, set()).add(path)
    return users


def affected_rows(root, rows, workflow, expression, paths):
    """(rows, reasons). Conservative: a path nothing refers to runs the default version's test rows."""
    tracked = subprocess.run(['git', '-C', str(root), 'ls-files', '-z'], check=True,
                             capture_output=True, text=True).stdout.split('\0')
    users = mentions_graph(root, tracked)
    text = {}
    for row in rows:
        steps = active_steps(workflow, row, expression)
        text[row['id']] = '\n'.join(str(s.get('run', '')) + json.dumps(s.get('env', {})) for s in steps)
    chosen, reasons = set(), {}

    def add(ids, why):
        for i in ids:
            if i not in chosen:
                chosen.add(i)
                reasons.setdefault(i, why)

    everything = [r['id'] for r in rows]
    default_tests = [r['id'] for r in rows if r['job'] == 'test' and r['zig'] == DEFAULT_VERSION
                     and r['part'] != 'mutation']
    for path in paths:
        if path.startswith(EVERYTHING):
            add(everything, path)
            continue
        if path.startswith(PIPELINE) or (path.endswith('.lean') and '/' not in path):
            add([r['id'] for r in rows if r['job'] not in NO_LEAN_JOBS and r['job'] != 'lake'], path)
            continue
        if path.endswith('.md') or path.startswith('docs/'):
            add([r['id'] for r in rows if r['part'] == 'inputs' and r['zig'] == DEFAULT_VERSION], path)
            if path.startswith('docs/architecture-audit/'):
                add([r['id'] for r in rows if r['part'] == 'audit'], path)
        # Files that run the tests and the files that run those, transitively.
        closure, todo = {path}, [path]
        while todo:
            for user in users.get(todo.pop(), ()):
                if user not in closure:
                    closure.add(user)
                    todo.append(user)
        needles = set()
        for item in closure:
            needles.add(item)
            parts = item.split('/')
            for depth in range(1, len(parts)):
                directory = '/'.join(parts[:depth]) + '/'
                if directory not in BROAD_DIRECTORIES:
                    needles.add(directory)
        hits = [row['id'] for row in rows if any(n in text[row['id']] for n in needles)]
        if hits:
            add(hits, path)
        elif not path.endswith('.md') and not path.startswith('docs/'):
            add(default_tests, path + ' (not referenced by a CI step)')
    return [r for r in rows if r['id'] in chosen], reasons


# --- Workspace ---------------------------------------------------------------------------

def sync_workspace(src, workspace, files):
    """Make `workspace` a private git checkout of the tracked files of `src` (as they are on
    disk now, including staged additions and unstaged edits). Untracked files, .lake and tool
    directories of the workspace are kept, so builds stay incremental."""
    workspace.mkdir(parents=True, exist_ok=True)
    wanted = set(files)
    old = subprocess.run(['git', '-C', str(workspace), 'ls-files', '-z'], capture_output=True, text=True)
    for path in (old.stdout.split('\0') if old.returncode == 0 else []):
        if path and path not in wanted:
            try:
                (workspace / path).unlink()
            except OSError:
                pass
    for path in files:
        s, d = src / path, workspace / path
        d.parent.mkdir(parents=True, exist_ok=True)
        if s.is_symlink():
            if d.is_symlink() or d.exists():
                d.unlink()
            d.symlink_to(os.readlink(s))
            continue
        a = s.stat()
        if d.is_symlink() or not d.exists() or (d.stat().st_size, d.stat().st_mtime_ns) != (a.st_size, a.st_mtime_ns):
            if d.is_symlink():
                d.unlink()
            shutil.copy2(s, d)
    shutil.rmtree(workspace / '.git', ignore_errors=True)
    env = dict(os.environ, GIT_LITERAL_PATHSPECS='1', GIT_AUTHOR_NAME='local-ci', GIT_AUTHOR_EMAIL='local-ci@example.invalid',
               GIT_COMMITTER_NAME='local-ci', GIT_COMMITTER_EMAIL='local-ci@example.invalid',
               GIT_AUTHOR_DATE='2000-01-01T00:00:00Z', GIT_COMMITTER_DATE='2000-01-01T00:00:00Z')
    listing = workspace / '.git-files'
    listing.write_bytes(b''.join(p.encode() + b'\0' for p in files))
    try:
        for cmd in (['init', '-q'], ['add', '-f', '--pathspec-from-file=.git-files', '--pathspec-file-nul'],
                    ['commit', '-q', '--allow-empty', '-m', 'Local tracked-source snapshot']):
            subprocess.run(['git', '-C', str(workspace), *cmd], check=True, env=env)
    finally:
        listing.unlink()


# --- Step execution (inside the container or on the host) ---------------------------------

class Job:
    def __init__(self, row, workflow, workspace, tools, artifacts, expression, render):
        self.row, self.workflow, self.job = row, workflow, workflow['jobs'][row['job']]
        self.workspace, self.tools, self.artifacts = workspace, tools, artifacts
        self.expression, self.render_text = expression, render
        self.runner_temp = artifacts / ('runner-temp-' + row['job'])
        self.values = row_context(row, workspace)
        self.values['runner.temp'] = str(self.runner_temp)
        self.path_extra = []
        self.env_extra = {}
        self.src = None
        self.generated = []
        self.outputs = {}
        self.log = None
        self.failed = False
        self.steps_report = []
        self.child = None
        self.zig_air = None

    # -- environment
    def base_env(self):
        host = self.row['where'] == 'host'
        env = dict(os.environ)
        path = env.get('PATH', '/usr/bin:/bin')
        if host:
            # No Zig/Lean of the user's own on the path: the steps install what CI installs.
            path = ':'.join(self.without_user_toolchains(d) for d in path.split(':'))
        elan = self.elan_home()
        env.update({'CI': 'true', 'GITHUB_ACTIONS': 'true', 'GITHUB_WORKSPACE': str(self.workspace),
                    'RUNNER_TEMP': str(self.runner_temp), 'RUNNER_OS': self.values['runner.os'],
                    'RUNNER_ARCH': self.values['runner.arch'], 'GITHUB_PATH': str(self.artifacts / 'github_path'),
                    'GITHUB_OUTPUT': str(self.artifacts / 'github_output'),
                    'GITHUB_ENV': str(self.artifacts / 'github_env'),
                    'AIR2LEAN_CACHE': str(self.tools / 'downloads'), 'ZIG_GLOBAL_CACHE_DIR': str(self.tools / 'zig-global'),
                    'LEAN_NUM_THREADS': LEAN_THREADS, 'ELAN_NO_OVERRIDE_NOTICE': '1', 'HOME': env.get('HOME', '/root'),
                    'PATH': ':'.join([*self.path_extra, *([str(elan / 'bin')] if elan else []), path])})
        if elan:
            env['ELAN_HOME'] = str(elan)
        if os.environ.get('AIR2LEAN_LOCAL_ROSETTA') == '1':
            # Rosetta rejects the empty RELRO segment of release builds ("bss_size overflow").
            env.setdefault('AIR2LEAN_DIFF_LINK_FLAGS', '-z norelro')
        env.update(self.env_extra)
        job_env = {k: self.render_text(v, self.step_values()) for k, v in self.job.get('env', {}).items()}
        env.update(job_env)
        return env

    BANNED = ('zig', 'lake', 'lean', 'leanc', 'elan', 'air2lean')

    def without_user_toolchains(self, directory):
        """A PATH directory minus the user's own Zig/Lean tools: a symlink farm when it has any."""
        if not any(os.access(os.path.join(directory, t), os.X_OK) for t in self.BANNED):
            return directory
        farm = self.tools / 'path' / re.sub(r'\W', '_', directory)
        shutil.rmtree(farm, ignore_errors=True)
        farm.mkdir(parents=True)
        for name in os.listdir(directory):
            if name not in self.BANNED:
                (farm / name).symlink_to(os.path.join(directory, name))
        return str(farm)

    def elan_home(self):
        for step in self.job['steps']:
            if 'elan-init' in str(step.get('run', '')):
                return self.tools / ('elan-' + digest(step['run'])[:16])
        return None

    # -- logging
    def say(self, text):
        print(text, flush=True)

    def run_code(self, code, env, cwd):
        self.log.flush()
        self.child = subprocess.Popen(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code],
                                      cwd=cwd, env=env, stdout=self.log, stderr=subprocess.STDOUT,
                                      stdin=subprocess.DEVNULL, start_new_session=True)
        status = self.child.wait()
        self.child = None
        return status

    def read_env_file(self, f):
        if f.exists():
            for line in f.read_text().splitlines():
                key, _, value = line.partition('=')
                if key:
                    self.env_extra[key] = value
            f.unlink()

    def read_github_output(self, step):
        f = self.artifacts / 'github_output'
        if f.exists():
            for line in f.read_text().splitlines():
                key, _, value = line.partition('=')
                if key:
                    self.outputs.setdefault(step.get('id', ''), {})[key] = value
            f.unlink()

    def read_github_path(self):
        f = self.artifacts / 'github_path'
        if f.exists():
            for line in reversed(f.read_text().split('\n')):
                if line and line not in self.path_extra and not line.endswith('/.elan/bin'):
                    self.path_extra.insert(0, line)
            f.unlink()

    # -- steps
    def active(self, step):
        condition = step.get('if')
        if condition is None:
            return True
        text = str(condition).replace('!cancelled()', "'1'").replace('always()', "'1'")
        text = text.replace('failure()', "'1'" if self.failed else "''").replace('success()', "''" if self.failed else "'1'")
        return bool(evaluate(self.expression, text, self.step_values()))

    def render(self, text):
        return self.render_text(text, self.step_values())

    def step_values(self):
        values = dict(self.values)
        for sid, out in self.outputs.items():
            for key, value in out.items():
                values['steps.%s.%s' % (sid, key if key == 'outcome' else 'outputs.' + key)] = value
        return values

    def hash_files(self, patterns):
        files = set()
        for pattern in patterns:
            files.update(p for p in glob.glob(pattern, root_dir=self.workspace, recursive=True)
                         if (self.workspace / p).is_file())
        return digest(''.join(hashlib.sha256((self.workspace / p).read_bytes()).hexdigest() for p in sorted(files)))

    def render_key(self, text):
        def sub(match):
            inner = match[1].strip()
            if inner.startswith('hashFiles('):
                inner = re.sub(r"format\('([^']*)',\s*([\w.]+)\)",
                               lambda m: "'%s'" % m[1].replace('{0}', str(self.step_values()[m[2]])), inner)
                return self.hash_files(re.findall(r"'([^']*)'", inner))[:16]
            return str(evaluate(self.expression, inner, self.step_values()))
        return re.sub(r'\$\{\{(.*?)\}\}', sub, str(text))

    def do_cache(self, step):
        w = step['with']
        path = self.render(w['path']).split('\n')[0].strip()
        key = self.render_key(w['key'])
        out = self.outputs.setdefault(step.get('id', ''), {})
        out['cache-primary-key'] = key
        out['cache-hit'] = 'false'
        runner_prefix = str(self.runner_temp) + '/'
        if re.fullmatch(r'(tests/diff/)?\.lake(/\*)?', path):
            # .lake directories persist in the volume/workspace, so every build is incremental. A
            # marker plays the exact-key cache entry: the `lake` job writes it after its build.
            if path.startswith('.lake') and self.lake_marker().exists() and self.lake_marker().read_text() == key:
                out['cache-hit'] = 'true'
            return
        if path.startswith(runner_prefix) and path.endswith('zig-diff-cache'):
            # The harness builds of scripts/diff.sh; content addressed, so staleness only costs time.
            target = self.tools / 'zig-diff-cache' / ('%s-%s-%s' % (self.row['job'], self.row['zig'], self.row['part']))
            target.mkdir(parents=True, exist_ok=True)
            link = Path(path)
            link.parent.mkdir(parents=True, exist_ok=True)
            if not link.exists():
                link.symlink_to(target)
            return
        if re.fullmatch(r'zig-air-[\w.]+/?', path):
            entry = self.tools / 'cache' / digest(key)[:24]
            self.zig_air = (path.rstrip('/'), entry)
            if (entry / '.complete').exists():
                dest = self.workspace / path.rstrip('/')
                shutil.rmtree(dest, ignore_errors=True)
                shutil.copytree(entry / path.rstrip('/'), dest, symlinks=True)
                out['cache-hit'] = 'true'
            return
        raise RuntimeError('unsupported cache path in ci.yml: %s (teach scripts/local-ci-run.py)' % path)

    def lake_marker(self):
        return self.workspace / '.lake/local-ci-lake-key'

    def lake_key(self):
        """The key under which CI's `lake` job caches this tree's build of the root package."""
        lookup = next(s for s in self.workflow['jobs']['lake']['steps'] if str(s.get('uses', '')).startswith('actions/cache/restore'))
        return self.render_key(lookup['with']['key'])

    def save_lake_marker(self):
        self.lake_marker().parent.mkdir(exist_ok=True)
        self.lake_marker().write_text(self.lake_key())

    def install_generated(self):
        """`generated.py install` of CI: the whole-tree generated files (materialized on the host
        by `generated.py materialize`) land in the workspace as untracked files."""
        for path in self.generated:
            target = self.workspace / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(self.src / path, target)
        self.log.write(('installed %d generated file(s)\n' % len(self.generated)).encode())

    def install_zig_air(self):
        """The patched compiler of the zig-air job: from the persistent cache under the key of
        scripts/ci-cache.py, or built with that job's own recipe and saved."""
        version = self.row['zig']
        dest = self.workspace / ('zig-air-' + version)
        env = self.base_env()
        key = subprocess.run(['python3', 'scripts/ci-cache.py', 'zig-air-key', version], cwd=self.workspace, env=env,
                             capture_output=True, text=True, check=True).stdout.strip()
        entry = self.tools / 'cache' / digest(key)[:24]
        if (entry / '.complete').exists():
            shutil.rmtree(dest, ignore_errors=True)
            shutil.copytree(entry / dest.name, dest, symlinks=True)
            return
        build = next(s for s in self.workflow['jobs']['zig-air']['steps'] if 'zig-patch/build.sh' in str(s.get('run', '')))
        if self.run_code(self.render(build['run']), env, self.workspace) != 0:
            raise RuntimeError('building the patched zig failed')
        self.zig_air = (dest.name, entry)
        self.save_zig_air()

    def save_zig_air(self):
        name, entry = self.zig_air
        stage = entry.with_name(entry.name + '.partial')
        shutil.rmtree(stage, ignore_errors=True)
        shutil.copytree(self.workspace / name, stage / name, symlinks=True)
        (stage / '.complete').write_text(name + '\n')
        shutil.rmtree(entry, ignore_errors=True)
        stage.rename(entry)

    def do_upload(self, step):
        w = step['with']
        name = self.render(w['name'])
        dest = self.artifacts / 'uploads' / name
        for line in self.render(w['path']).split('\n'):
            line = line.strip()
            for match in glob.glob(line):
                dest.mkdir(parents=True, exist_ok=True)
                target = dest / os.path.basename(match.rstrip('/'))
                if os.path.isdir(match):
                    shutil.copytree(match, target, symlinks=True, dirs_exist_ok=True)
                else:
                    shutil.copy2(match, target)

    def memoizable(self, code):
        return 'elan-init' in code or ('host-zig' in code and 'tar -xJ' in code)

    def do_memo(self, step, code, env):
        """Run an install recipe once per recipe text; later rows reuse its effects.

        The recipe runs in a scratch directory that mirrors the workspace's top level with
        symlinks (it reads zig-patch/ and the like), so what it creates there is exactly its
        product: host-zig/, elan-init, tarballs."""
        code = self.render(code)
        home = self.tools / 'setup' / digest(code)[:24]
        work, out = home / 'work', home / 'out'
        if not (home / '.ok').exists():
            shutil.rmtree(home, ignore_errors=True)
            (home / 'tmp').mkdir(parents=True)
            work.mkdir()
            for entry in self.workspace.iterdir():
                if entry.name not in ('.git', '.lake') and not entry.name.startswith(('host-zig', 'zig-air-', 'elan')):
                    (work / entry.name).symlink_to(entry)
            run_env = dict(env, RUNNER_TEMP=str(home / 'tmp'), GITHUB_PATH=str(home / 'github_path'),
                           GITHUB_ENV=str(home / 'github_env'))
            (home / 'github_path').touch()
            (home / 'github_env').touch()
            if self.run_code(code, run_env, work) != 0:
                return 1
            out.mkdir()
            for entry in list(work.iterdir()):
                if not entry.is_symlink() and not entry.name.endswith(('.tar.gz', '.tar.xz')) and entry.name != 'elan-init':
                    shutil.move(str(entry), out / entry.name)
            for junk in (home / 'tmp').glob('*.tar.*'):
                junk.unlink()
            (home / 'github_path').write_text((home / 'github_path').read_text().replace(str(work), str(out)))
            shutil.rmtree(work)
            (home / '.ok').write_text('ok\n')
        # Materialise: cwd-relative results become physical directories of the workspace (the
        # receipt gate wants real compiler directories), RUNNER_TEMP-relative ones are linked.
        mapping = {}
        for entry in sorted(out.iterdir()):
            target = self.workspace / entry.name
            marker = target / '.local-ci-recipe'
            if not (marker.exists() and marker.read_text() == home.name):
                shutil.rmtree(target, ignore_errors=True)
                shutil.copytree(entry, target, symlinks=True)
                marker.write_text(home.name)
            mapping[str(entry)] = str(target)
        self.runner_temp.mkdir(parents=True, exist_ok=True)
        for entry in sorted((home / 'tmp').iterdir()):
            link = self.runner_temp / entry.name
            if not link.exists():
                link.symlink_to(entry)
            mapping[str(entry)] = str(link)
        for line in (home / 'github_env').read_text().splitlines():  # e.g. AIR2LEAN_HOST_PIN
            key, _, value = line.partition('=')
            if key:
                self.env_extra[key] = value
        for line in (home / 'github_path').read_text().split('\n'):
            if line and not line.endswith('/.elan/bin'):  # the recipe's HOME; ELAN_HOME/bin is ours
                for old, new in sorted(mapping.items(), key=lambda kv: -len(kv[0])):
                    if line == old or line.startswith(old + '/'):
                        line = new + line[len(old):]
                        break
                self.path_extra.insert(0, line)
        return 0

    def run_step(self, step):
        name = step.get('name', step.get('uses', 'step'))
        uses = str(step.get('uses', '')).split('@')[0]
        started = time.monotonic()
        status, outcome = 0, 'success'
        code = str(step.get('run', ''))
        substitute = next((c for c in CI_ONLY_CODE if c in code), None)
        if substitute in ('scripts/ci-reuse.py', 'sudo apt-get'):
            return  # nothing to do locally, not even to report
        try:
            if not self.active(step):
                return
        except ValueError as error:
            raise StepFailed(name, 1) from error
        if self.row['where'] == 'amd64' and name in EMULATION_SKIPS:
            self.say('== CI %s: %s == SKIPPED (%s)' % (self.row['id'], name, EMULATION_SKIPS[name]))
            self.steps_report.append({'name': name, 'status': 'skipped', 'reason': EMULATION_SKIPS[name], 'seconds': 0})
            return
        self.say('== CI %s: %s ==' % (self.row['id'], name))
        self.log.write(('\n== CI %s: %s ==\n' % (self.row['id'], name)).encode())
        try:
            if uses == 'actions/checkout':
                pass
            elif uses in ('actions/cache', 'actions/cache/restore'):
                self.do_cache(step)
            elif uses == 'actions/download-artifact':
                pass  # the step that unpacks it is replaced below
            elif uses == 'actions/upload-artifact':
                self.do_upload(step)
            elif uses:
                raise RuntimeError('unsupported action in ci.yml: %s' % uses)
            elif substitute == 'scripts/generated.py install':
                self.install_generated()
            elif substitute == 'zig-air.tar':
                self.install_zig_air()
            elif substitute == 'lake-root.tar.zst':
                pass  # .lake persists; the `lake` job runs first when this tree's build is missing
            else:
                code = step['run']
                env = self.base_env()
                env.update({k: self.render(v) for k, v in step.get('env', {}).items()})
                self.runner_temp.mkdir(parents=True, exist_ok=True)
                if self.memoizable(code):
                    status = self.do_memo(step, code, env)
                else:
                    status = self.run_code(self.render(code), env, self.workspace)
                    if status == SIGSEGV_STATUS and re.search(r'\b(lake|lean)\b', code):
                        # Lean under Rosetta has been seen to segfault on a module that builds fine
                        # the next time. Lake builds are incremental, so run the step once more; a
                        # deterministic crash fails again.
                        self.log.write(b'\nlocal-ci: step exited 139 (SIGSEGV); running it once more\n')
                        self.say('   step exited 139; running it once more')
                        status = self.run_code(self.render(code), env, self.workspace)
                    self.read_github_path()
                    self.read_env_file(self.artifacts / 'github_env')
                    self.read_github_output(step)
                    if status == 0 and self.zig_air and 'build.sh' in code \
                            and (self.workspace / self.zig_air[0]).is_dir():
                        self.save_zig_air()
        except Exception as error:  # a runner bug or an unsupported construct fails the row, loudly
            self.log.write(('error: %r\n' % error).encode())
            status = 1
        if status:
            outcome = 'failure'
            self.failed = True
        if step.get('id'):
            self.outputs.setdefault(step['id'], {})['outcome'] = outcome
        self.steps_report.append({'name': name, 'status': status, 'seconds': round(time.monotonic() - started, 1)})
        if status and step.get('continue-on-error'):
            self.say('   (continue-on-error step failed; the row will be reported failed)')
        elif status:
            raise StepFailed(name, status)


SIGSEGV_STATUS = 139


class StepFailed(Exception):
    pass


def digest(text):
    return hashlib.sha256(text.encode() if isinstance(text, str) else text).hexdigest()


def exec_row(args):
    """Entry point inside the container / on the host: run one row's steps in `workspace`."""
    root = Path(args.src)
    workflow = load_workflow(root)
    expression, render = load_condition_helpers(root)
    rows = {r['id']: r for r in enumerate_rows(workflow)}
    row = rows[args.row]
    workspace, tools, artifacts = Path(args.workspace), Path(args.tools), Path(args.artifacts)
    artifacts.mkdir(parents=True, exist_ok=True)
    tools.mkdir(parents=True, exist_ok=True)
    files = [p for p in Path(args.files).read_bytes().decode().split('\0') if p]
    for stale in workspace.glob('.zig-air-*.air2lean-build.lock'):
        shutil.rmtree(stale, ignore_errors=True)  # a killed build; the lane lock excludes another one
    sync_workspace(root, workspace, files)
    generated = Path(args.generated).read_bytes().decode().split('\0') if args.generated else []
    job = Job(row, workflow, workspace, tools, artifacts, expression, render)
    job.src, job.generated = root, [p for p in generated if p]
    shutil.rmtree(job.runner_temp, ignore_errors=True)
    job.runner_temp.mkdir(parents=True)
    job.log = open(artifacts / 'row.log', 'wb')
    status, failed_step = 0, None

    def stop(signum, _frame):
        for each in jobs:
            if each.child is not None and each.child.poll() is None:
                os.killpg(each.child.pid, signum)
                try:
                    each.child.wait(timeout=20)
                except subprocess.TimeoutExpired:
                    os.killpg(each.child.pid, signal.SIGKILL)
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    os.chdir(workspace)
    jobs = [job]

    def build_lake_first():
        # `needs: lake`: CI's test rows restore the root package's build from the `lake` job,
        # and some steps rely on modules only that job builds. Run it first when this tree's
        # build is not in the persistent .lake yet.
        lake = Job(rows['lake'], workflow, workspace, tools, artifacts, expression, render)
        lake.log = job.log
        jobs.append(lake)
        if lake.lake_marker().exists() and lake.lake_marker().read_text() == lake.lake_key():
            return
        shutil.rmtree(lake.runner_temp, ignore_errors=True)
        lake.runner_temp.mkdir(parents=True)
        job.say('== CI %s: needs the lake job; running it first ==' % row['id'])
        for step in lake.job['steps']:
            lake.run_step(step)
        lake.save_lake_marker()
        job.failed = job.failed or lake.failed
        job.steps_report += lake.steps_report
    try:
        if 'lake' in ([job.job.get('needs')] if isinstance(job.job.get('needs'), str) else job.job.get('needs', [])):
            build_lake_first()
        for step in job.job['steps']:
            job.run_step(step)
        if row['job'] == 'lake' and not job.failed:
            job.save_lake_marker()
    except StepFailed as failure:
        status, failed_step = failure.args[1], failure.args[0]
    finally:
        job.log.close()
        (artifacts / 'steps.json').write_text(json.dumps(
            {'row': row['id'], 'steps': job.steps_report, 'failed_step': failed_step}, indent=1))
    if status == 0 and job.failed:
        status, failed_step = 1, 'a continue-on-error step'
    if failed_step:
        print('FAILED: %s (exit %s)' % (failed_step, status), flush=True)
    return status


# --- Orchestration (host) -------------------------------------------------------------------

def ensure_image(arch, root):
    dockerfile = root / 'docker/local-ci.Dockerfile'
    python_arch = 'arm64' if arch == 'amd64' and platform_is_arm_host() else arch
    tag = 'air2lean-local-ci:%s-py%s-%s' % (arch, python_arch, digest(dockerfile.read_bytes())[:8])
    if subprocess.run(['docker', 'image', 'inspect', tag], capture_output=True).returncode:
        print('local-ci: building %s (once per Dockerfile change)' % tag, file=sys.stderr)
        subprocess.run(['docker', 'build', '-q', '--platform', 'linux/' + arch, '--build-arg', 'PYTHON_ARCH=' + python_arch,
                        '-f', str(dockerfile), '-t', tag, str(dockerfile.parent)], check=True, stdout=subprocess.DEVNULL)
    return tag


def volumes(arch, root):
    """Named volumes. The amd64 names are the ones scripts/local-ci.sh's legacy modes use, so both
    share one set of toolchains and Lake builds."""
    tool = os.environ.get('AIR2LEAN_LOCAL_TOOL_VOLUME',
                          'air2lean-local-linux-toolchains' if arch == 'amd64' else 'air2lean-local-linux-%s-toolchains' % arch)
    ns = digest(tool)[:16]

    def key(*names):
        return digest(b''.join((root / n).read_bytes() for n in names))[:16]
    return {'/cache': tool,
            '/work/.lake': 'air2lean-linux-%s-%s-lake-%s' % (arch, ns, key('lean-toolchain', 'lake-manifest.json')),
            '/work/tests/diff/.lake': 'air2lean-linux-%s-%s-diff-%s' % (
                arch, ns, key('tests/diff/lean-toolchain', 'tests/diff/lake-manifest.json'))}


def generated_paths(root):
    out = subprocess.run([sys.executable, str(root / 'scripts/generated.py'), 'paths'], cwd=root, check=True,
                         capture_output=True, text=True).stdout
    return out.split()


def materialize_generated(root):
    """The `generated` job of CI, here: the whole-tree files (coverage inventories, premise index,
    provenance fixtures) in this worktree, which the rows then install like CI's artifact."""
    print('local-ci: scripts/generated.py materialize', file=sys.stderr)
    status = subprocess.call([sys.executable, '-B', str(root / 'scripts/generated.py'), 'materialize'], cwd=root,
                             stdout=subprocess.DEVNULL)
    if status:
        raise SystemExit('error: scripts/generated.py materialize failed (exit %d)' % status)


def launch_row(args):
    """Run one row where it belongs and leave its results in args.results. Exit status = the row's."""
    root = REPO
    workflow = load_workflow(root)
    row = {r['id']: r for r in enumerate_rows(workflow)}[args.row]
    results = Path(args.results)
    results.mkdir(parents=True, exist_ok=True)
    progress = open(results / 'progress.log', 'a', buffering=1)  # step headers; read by the heartbeat
    files = subprocess.run(['git', '-C', str(root), 'ls-files', '-z'], check=True, capture_output=True).stdout
    names = [p for p in files.decode().split('\0') if p and not p.startswith(('.lake/', '.claude/'))]
    names = [p for p in names if os.path.lexists(root / p) and not (root / p).is_dir()]
    snapshot = Path(tempfile.mkdtemp(prefix='air2lean-local-ci.'))
    try:
        (snapshot / 'files').write_bytes(b''.join(p.encode() + b'\0' for p in names))
        present = [p for p in generated_paths(root) if (root / p).is_file()]
        (snapshot / 'generated').write_bytes(b''.join(p.encode() + b'\0' for p in present))
        if row['where'] == 'host':
            tools = HOME / 'tools-macos'
            command = [sys.executable, str(root / 'scripts/local-ci-run.py'), 'exec-row', '--row', row['id'],
                       '--src', str(root), '--files', str(snapshot / 'files'), '--generated', str(snapshot / 'generated'), '--workspace', str(HOME / 'macos-work'),
                       '--tools', str(tools), '--artifacts', str(results)]
            return subprocess.call(command, stdout=progress, stderr=subprocess.STDOUT)
        arch = row['where']
        image = ensure_image(arch, root)
        mounts = []
        for target, volume in volumes(arch, root).items():
            mounts += ['--mount', 'type=volume,src=%s,dst=%s' % (volume, target)]
        # Hook for a shared content-addressed cache (or anything else a row should see): names in
        # AIR2LEAN_LOCAL_PASSTHROUGH are forwarded with their values, SRC:DST pairs in
        # AIR2LEAN_LOCAL_EXTRA_MOUNTS are bind-mounted. Host rows inherit the environment as is.
        hooks = []
        for name in os.environ.get('AIR2LEAN_LOCAL_PASSTHROUGH', '').split():
            if name in os.environ:
                hooks += ['--env', '%s=%s' % (name, os.environ[name])]
        for pair in os.environ.get('AIR2LEAN_LOCAL_EXTRA_MOUNTS', '').split():
            src, _, dst = pair.partition(':')
            hooks += ['--mount', 'type=bind,src=%s,dst=%s' % (src, dst)]
        stale = subprocess.run(['docker', 'ps', '-aq', '--filter', 'name=^air2lean-local-ci-', '--filter', 'status=exited'],
                               capture_output=True, text=True).stdout.split()
        if stale:  # left by an interrupted run
            subprocess.run(['docker', 'rm', '-f', *stale], capture_output=True)
        container = subprocess.run(
            ['docker', 'create', '--name', 'air2lean-local-ci-%s-%d' % (re.sub(r'\W', '_', row['id']), os.getpid()),
             '--platform', 'linux/' + arch, '--memory', MEMORY, '--memory-swap', MEMORY,
             '--cpus', CPUS, '--pids-limit', '1024', '--init', *hooks,
             '--env', 'AIR2LEAN_LOCAL_LEAN_THREADS=' + LEAN_THREADS,
             '--env', 'AIR2LEAN_LOCAL_ROSETTA=%d' % (arch == 'amd64' and platform_is_arm_host()),
             '--mount', 'type=bind,src=%s,dst=/src,readonly' % root,
             '--mount', 'type=bind,src=%s,dst=/snapshot,readonly' % snapshot, *mounts, image,
             'python3', '/src/scripts/local-ci-run.py', 'exec-row', '--row', row['id'], '--src', '/src',
             '--files', '/snapshot/files', '--generated', '/snapshot/generated', '--workspace', '/work', '--tools', '/cache', '--artifacts', '/artifacts'],
            check=True, capture_output=True, text=True).stdout.strip()
        try:
            subprocess.run(['docker', 'start', '-a', container], check=False, stdout=progress, stderr=subprocess.STDOUT)
            status = int(subprocess.run(['docker', 'inspect', '--format', '{{.State.ExitCode}}', container],
                                        check=True, capture_output=True, text=True).stdout)
        finally:
            subprocess.run(['docker', 'stop', '--time', '20', container], capture_output=True)
            subprocess.run(['docker', 'cp', container + ':/artifacts/.', str(results)], capture_output=True)
            subprocess.run(['docker', 'rm', '-f', container], capture_output=True)
        return status
    finally:
        shutil.rmtree(snapshot, ignore_errors=True)


def platform_is_arm_host():
    return subprocess.run(['docker', 'info', '--format', '{{.Architecture}}'], capture_output=True,
                          text=True).stdout.strip() in ('aarch64', 'arm64')


def guarded(row, results, scale, verbose):
    """Run one row under scripts/build-guard.py (the lane lock, wall-clock bound, evidence)."""
    lane = 'host' if row['where'] == 'host' else 'docker'
    LOCK_DIR.mkdir(parents=True, exist_ok=True)
    log = results / 'guard.log'
    progress = results / 'progress.log'
    command = [sys.executable, str(REPO / 'scripts/build-guard.py'), '--cwd', str(REPO),
               '--lock', str(LOCK_DIR / ('local-ci-%s.lock' % lane)), '--lock-wait', '28800',
               '--timeout', str(int(row['timeout'] * 60 * scale)),
               # The guard samples the host process tree; a container's memory is capped by Docker.
               '--rss-mib', '49152', '--report', str(results / 'guard.json'), '--log', str(log),
               '--profile', 'local-ci:' + row['id'], '--',
               sys.executable, str(REPO / 'scripts/local-ci-run.py'), 'launch', '--row', row['id'],
               '--results', str(results)]
    started = time.monotonic()
    proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    stop = threading.Event()

    def watch():  # progress: the last step started, every few minutes (every step with -v)
        seen, last_print = 0, time.monotonic()
        while not stop.wait(5):
            try:
                lines = progress.read_text(errors='replace').splitlines()
            except OSError:
                continue
            headers = [l for l in lines if l.startswith('== CI ')]
            if verbose and len(headers) > seen:
                print('\n'.join('    ' + h for h in headers[seen:]), flush=True)
            elif headers and time.monotonic() - last_print > 600:
                print('    ... %s (%d min)' % (headers[-1][6:], (time.monotonic() - started) / 60), flush=True)
                last_print = time.monotonic()
            seen = len(headers)
    thread = threading.Thread(target=watch, daemon=True)
    thread.start()
    try:
        out = proc.communicate()[0]
    except KeyboardInterrupt:
        proc.send_signal(signal.SIGTERM)
        out = proc.communicate()[0]
    stop.set()
    return proc.returncode, time.monotonic() - started, out


def tail(path, count=40):
    try:
        return '\n'.join(Path(path).read_text(errors='replace').splitlines()[-count:])
    except OSError:
        return '(no log)'


def format_seconds(seconds):
    return '%dm%02ds' % divmod(int(seconds), 60) if seconds >= 60 else '%.0fs' % seconds


def main(argv):
    parser = argparse.ArgumentParser(prog='local-ci.sh', description=__doc__.split('\n\n')[0])
    parser.add_argument('--part', action='append', default=[], metavar='P',
                        help='a CI part (golden, lean, inputs, native, audit, receipt, Debug, ReleaseFast, '
                             'ReleaseSmall, mutation[:N]) or a job (lake, macos, aarch64-linux, '
                             'build-modes-aarch64-linux, bitops-native-arm); repeatable')
    parser.add_argument('--version', action='append', default=[], metavar='V', help='Zig version; repeatable')
    parser.add_argument('--changed', action='store_true', help='rows affected by the diff against origin/main')
    parser.add_argument('--all', action='store_true', help='every row (the whole CI; hours)')
    parser.add_argument('--list', action='store_true', help='print the selected rows and stop')
    parser.add_argument('--timeout-scale', type=float, default=2.0, help='row wall-clock bound = ci.yml timeout x this')
    parser.add_argument('-v', '--verbose', action='store_true', help='print every step as it starts')
    args = parser.parse_args(argv)
    if not (args.part or args.version or args.changed or args.all):
        parser.error('select rows with --part, --version, --changed or --all')
    workflow = load_workflow(REPO)
    expression, _ = load_condition_helpers(REPO)
    rows = enumerate_rows(workflow)
    reasons = {}
    if args.changed:
        paths = changed_paths(REPO)
        if paths is None:
            print('local-ci: no origin/main to compare with; running every row', file=sys.stderr)
            chosen = rows
        else:
            chosen, reasons = affected_rows(REPO, rows, workflow, expression, paths)
            print('local-ci: %d changed path(s) -> %d row(s)' % (len(paths), len(chosen)), file=sys.stderr)
        if args.part or args.version:
            keep = {r['id'] for r in select_rows(rows, args.part, args.version)}
            chosen = [r for r in chosen if r['id'] in keep]
    elif args.all:
        chosen = rows
    else:
        chosen = select_rows(rows, args.part, args.version)
    order = {'host': 2, 'arm64': 1, 'amd64': 0}
    chosen = sorted(chosen, key=lambda r: (order[r['where']], rows.index(r)))
    if args.list or not chosen:
        for row in chosen:
            print('%-8s %-40s %s' % (row['where'], row['id'], reasons.get(row['id'], '')))
        if not chosen:
            print('local-ci: no row selected')
        return 0
    if any('scripts/generated.py install' in json.dumps(workflow['jobs'][r['job']]['steps']) for r in chosen):
        materialize_generated(REPO)
    stamp = datetime.datetime.now().strftime('%Y%m%d-%H%M%S')
    parent = Path(os.environ.get('AIR2LEAN_LOCAL_RESULTS', REPO / '.lake/local-ci-results'))
    run_dir = parent / ('run-' + stamp)
    summary = []
    for row in chosen:
        results = run_dir / row['id'].replace(':', '_')
        results.mkdir(parents=True, exist_ok=True)
        print('== %s (%s)' % (row['id'], row['where']), flush=True)
        status, seconds, out = guarded(row, results, args.timeout_scale, args.verbose)
        failed_step = None
        try:
            failed_step = json.loads((results / 'steps.json').read_text()).get('failed_step')
        except (OSError, ValueError):
            pass
        guard_note = ''
        try:
            outcome = json.loads((results / 'guard.json').read_text()).get('outcome')
            guard_note = '' if outcome in ('success', 'child_failed') else outcome
        except (OSError, ValueError):
            pass
        skipped = []
        try:
            skipped = [x['name'] for x in json.loads((results / 'steps.json').read_text())['steps'] if x['status'] == 'skipped']
        except (OSError, ValueError, KeyError):
            pass
        summary.append((row, status, seconds, failed_step or guard_note, skipped))
        print('   %s in %s' % ('passed' if status == 0 else 'FAILED (exit %d)' % status, format_seconds(seconds)), flush=True)
        if status:
            print(tail(results / 'row.log') if (results / 'row.log').exists() else tail(results / 'progress.log'), flush=True)
            print('   full log: %s' % (results / 'row.log'), flush=True)
    print('\nlocal-ci summary (results in %s)' % run_dir)
    for row, status, seconds, note, skipped in summary:
        print('  %-6s %-42s %-8s %s' % ('PASS' if status == 0 else 'FAIL', row['id'], format_seconds(seconds),
                                         ('at: ' + note) if note and status else ''))
        for name in skipped:
            print('           skipped: %s (%s)' % (name, EMULATION_SKIPS.get(name, 'see steps.json')))
    failed = [s for s in summary if s[1]]  # (row, status, seconds, note, skipped)
    print('%d row(s), %d failed, %s total' % (len(summary), len(failed), format_seconds(sum(s[2] for s in summary))))
    return 1 if failed else 0


if __name__ == '__main__':
    command = sys.argv[1] if len(sys.argv) > 1 else ''
    if command in ('exec-row', 'launch'):
        parser = argparse.ArgumentParser()
        parser.add_argument('command')
        parser.add_argument('--row', required=True)
        parser.add_argument('--src')
        parser.add_argument('--files')
        parser.add_argument('--generated')
        parser.add_argument('--workspace')
        parser.add_argument('--tools')
        parser.add_argument('--artifacts')
        parser.add_argument('--results')
        parsed = parser.parse_args()
        if command == 'exec-row':
            ensure_yaml()
            sys.exit(exec_row(parsed))
        ensure_yaml()
        sys.exit(launch_row(parsed))
    ensure_yaml()
    sys.exit(main(sys.argv[1:]))
