#!/usr/bin/env python3
"""CI result reuse: input keys, restricted checkouts and records (docs/ci.md).

  ci-reuse.py key --part ID [--manifest F]      the input key of a part at HEAD (--manifest: its preimage)
  ci-reuse.py decide --job JOB --row JSON       (CI step) reuse a recorded result, or restrict the
                                                checkout to the part's declared inputs and arm a record
  ci-reuse.py restrict (--part ID | --support JOB) [--seal | --discover]
                                                restrict the checkout to the declared inputs (CI support
                                                jobs; local runs of one part)
  ci-reuse.py unrestrict                        back to the tested commit (local runs)
  ci-reuse.py check-restricted                  (CI step) no withheld file was changed (or, as root, read)
  ci-reuse.py record --out F                    (CI step) the record a passing execution uploads
  ci-reuse.py check-workflow                    every part is declared; every step after the decision is guarded

A *part* is one CI job row: `test/<zig>/<part>[/<shard>]`, `macos/<zig>`, or a matrix-free job
name. .github/ci-inputs.json declares each part's inputs (content patterns, minus `exclude`
patterns) or `"reuse": false` (always runs). An executing part runs in a *restricted checkout*:
HEAD is a parentless commit with fixed metadata whose tree holds the declared files with their
content and every other tracked file as a withheld placeholder (same name, fixed content,
unreadable in the worktree). So whatever the part reads, lists or asks git is a function of the
declared content and the tracked names; reading a withheld file fails (EACCES), and
check-restricted fails the job when one was read anyway (root) or changed. The key hashes
exactly that: the declared content, all tracked names, the part's job definition (its own matrix
row) and the jobs it needs (with their declared inputs and the whole-tree generated files it
installs), every hashFiles() pattern of those jobs, the reuse machinery and the runner image. A
record is the artifact `ci-reuse-<key>` of a passing restricted execution. Offline except
`decide` (GitHub REST API, with GH_TOKEN); stdlib only.

Local runs (scripts/gate.sh, docs/ci.md#pre-merge-gate) use the same mechanism: the checkout's
content becomes a commit (`snapshot`), a unit's key covers its declared content over that commit
(`content_preimage`, declarations in assurance/gate-inputs.json), a declared unit runs in a
restricted worktree of it (`RestrictedWorktree`), and a pass is a local record
(`record_local`/`lookup_local`: an entry of kind `ci-reuse` in scripts/cas.py's store).
"""
import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
DECLARATIONS_SCHEMA = 'air2lean-ci-inputs/2'
DECLARATIONS = '.github/ci-inputs.json'
WORKFLOW = '.github/workflows/ci.yml'
WORKFLOW_NAME = 'CI'
# The reuse machinery and what it imports: always declared, never withheld.
MACHINERY = ('scripts/ci-reuse.py', 'scripts/release-record.py', 'scripts/generated.py', 'scripts/cas.py',
             'scripts/target-matrix.py', 'assurance/generated.json', DECLARATIONS)
# Jobs that are not parts: they build what the parts consume, or aggregate results. `lake` and
# `zig-air` run restricted to their declared inputs (`support` in the declarations), which every
# part that needs them adds to its own.
SUPPORT_JOBS = ('lake', 'zig-air', 'preflight', 'all-checks')
RESTRICTED_SUPPORT = ('lake', 'zig-air')
DECISION_STEP = 'Reuse a recorded result'
RESTRICT_STEP = 'Restrict the checkout to the declared inputs'
REFERENCE_STEP = 'Upload the reuse reference'
RECORD_STEPS = ('Record the result for reuse', 'Upload the reuse record')
GUARD = '!env.AIR2LEAN_REUSED'
# A `github.*` value other than the workspace path, a repository variable, a secret or a dispatch
# input can differ between runs while the job text does not.
RUN_SPECIFIC = re.compile(r'\$\{\{[^}]*\b(?:github\.(?!workspace\b)|vars\.|secrets\.|inputs\.)')
# Producer events whose records a pull_request run may reuse (never a fork: see lookup()).
RECORD_EVENTS = ('pull_request', 'push', 'merge_group', 'workflow_dispatch')
# Runs that test the commit main is (or becomes): the push run on main (every merge, admin merges
# included) and a merge_group run. They reuse only records of runs that tested a commit now on
# main, never a PR's.
MAIN_EVENTS = ('push', 'merge_group')
QUEUE_RECORD_EVENTS = ('push', 'merge_group', 'workflow_dispatch')
# The nightly run executes every part on the whole, unrestricted checkout: no reuse, no record.
FULL_EVENTS = ('schedule',)
DECLARATION_KEYS = {'reuse', 'inputs', 'exclude', 'note'}
# The withheld placeholder: a NUL first so that no parser accepts it, then what it is.
WITHHELD = b'\0air2lean: withheld by the restricted CI checkout; not a declared input of this part ' \
           b'(.github/ci-inputs.json, docs/ci.md#restricted-checkout)\n'
RESTRICTED_STATE = 'air2lean-restricted.json'  # in the git directory
IDENTITY = {'GIT_AUTHOR_NAME': 'air2lean restricted checkout', 'GIT_AUTHOR_EMAIL': 'ci@air2lean.invalid',
            'GIT_AUTHOR_DATE': '@0 +0000', 'GIT_COMMITTER_NAME': 'air2lean restricted checkout',
            'GIT_COMMITTER_EMAIL': 'ci@air2lean.invalid', 'GIT_COMMITTER_DATE': '@0 +0000'}

_spec = importlib.util.spec_from_file_location('air2lean_release_record', ROOT / 'scripts/release-record.py')
RR = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(RR)
SCHEMA = RR.REUSE_SCHEMA  # records and the reuse references release records read
_spec = importlib.util.spec_from_file_location('air2lean_generated', ROOT / 'scripts/generated.py')
GENERATED = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(GENERATED)
_spec = importlib.util.spec_from_file_location('air2lean_target_matrix', ROOT / 'scripts/target-matrix.py')
TM = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TM)


class ReuseError(Exception):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def sha256(text):
    return hashlib.sha256(text.encode() if isinstance(text, str) else text).hexdigest()


def git(root, *args, env=None, input=None, check=True):
    result = subprocess.run(['git', '-C', str(root), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=env, input=input)
    if result.returncode and check:
        raise ReuseError('git %s: %s' % (' '.join(args), result.stderr.decode(errors='replace').strip()))
    return result.stdout


def git_dir(root):
    return Path(root, git(root, 'rev-parse', '--git-dir').decode().strip())


# --- Patterns: `dir/**` (everything below), `*` (one path component), `**/` (any depth). ---

def glob_regex(pattern):
    out, i = '', 0
    while i < len(pattern):
        if pattern.startswith('**/', i):
            out, i = out + '(?:.*/)?', i + 3
        elif pattern.startswith('/**', i) and i + 3 == len(pattern):
            out, i = out + '(?:/.*)?', i + 3
        elif pattern.startswith('**', i):
            out, i = out + '.*', i + 2
        elif pattern[i] == '*':
            out, i = out + '[^/]*', i + 1
        elif pattern[i] == '?':
            out, i = out + '[^/]', i + 1
        else:
            out, i = out + re.escape(pattern[i]), i + 1
    return re.compile(out)


class Inputs:
    """A declared input set: tracked files matching a wildcard pattern of `patterns` and no
    `exclude` pattern, every exact path of `patterns`, and the `forced` patterns (reuse machinery,
    hashFiles() patterns, support jobs' inputs) unconditionally."""

    def __init__(self, patterns, exclude=(), forced=()):
        self.patterns, self.exclude, self.forced = sorted(set(patterns)), sorted(set(exclude)), sorted(set(forced))
        exact = [p for p in self.patterns if not set(p) & set('*?')]
        self._include = [glob_regex(p) for p in self.patterns if p not in exact]
        self._exclude = [glob_regex(p) for p in self.exclude]
        self._forced = [glob_regex(p) for p in self.forced + exact]

    def content(self, path):
        return (any(r.fullmatch(path) for r in self._forced)
                or any(r.fullmatch(path) for r in self._include) and not any(r.fullmatch(path) for r in self._exclude))

    def describe(self):
        return {'inputs': self.patterns, 'exclude': self.exclude, 'forced': self.forced}


def hashfiles_patterns(text):
    """The literal patterns of every hashFiles(...) call in a job's text (format() holes -> `*`)."""
    patterns, start = set(), 0
    while True:
        start = text.find('hashFiles(', start)
        if start < 0:
            return patterns
        depth, end = 0, start + len('hashFiles')
        for end in range(start + len('hashFiles'), len(text)):
            depth += {'(': 1, ')': -1}.get(text[end], 0)
            if depth == 0:
                break
        for literal in re.findall(r"'((?:[^']|'')*)'", text[start:end]):
            if not literal.startswith('!'):
                patterns.add(re.sub(r'\{\d+\}', '*', literal.replace("''", "'")))
        start = end


# --- The workflow, its parts and their declarations: from the worktree, or (revision given) from
# --- a commit, as a restricted checkout may withhold them. ---

def blob(root, revision, path):
    if revision is None:
        return Path(root, path).read_text(encoding='utf-8')
    return git(root, 'show', '%s:%s' % (revision, path)).decode('utf-8')


def load_workflow(root, revision=None):
    return RR.parse_workflow_yaml(blob(root, revision, WORKFLOW))


def job_rows(job):
    strategy = job.get('strategy') or {}
    return ((strategy.get('matrix') or {}).get('include')) or [None]


def part_id(job_id, row):
    if not row:
        return job_id
    return '/'.join([job_id] + [str(row[k]) for k in ('zig', 'part', 'shard') if row.get(k) not in (None, '')])


def parts(workflow):
    """{part id: (job id, row or None)} for every job row that is a part."""
    found = {}
    for job_id, job in (workflow.get('jobs') or {}).items():
        if job_id in SUPPORT_JOBS:
            continue
        for row in job_rows(job):
            found[part_id(job_id, row)] = (job_id, row)
    return found


def load_declarations(root, revision=None):
    data = json.loads(blob(root, revision, DECLARATIONS))
    if data.get('schema') != DECLARATIONS_SCHEMA:
        raise ReuseError('%s: unknown schema %r' % (DECLARATIONS, data.get('schema')))
    return data


def declaration(data, part):
    entry = (data.get('parts') or {}).get(part)
    if entry is None:
        raise ReuseError('%s declares no part %r' % (DECLARATIONS, part))
    unknown = set(entry) - DECLARATION_KEYS
    if unknown:
        raise ReuseError('%s: part %r has unknown keys %s' % (DECLARATIONS, part, ', '.join(sorted(unknown))))
    if entry.get('reuse') is not False and not entry.get('inputs'):
        raise ReuseError('%s: reusable part %r declares no inputs' % (DECLARATIONS, part))
    return entry


def support_inputs(data, job_id):
    entry = (data.get('support') or {}).get(job_id)
    if not entry or not entry.get('inputs') or set(entry) - {'inputs', 'note'}:
        raise ReuseError('%s: support job %r needs exactly "inputs" (and a "note")' % (DECLARATIONS, job_id))
    return list(entry['inputs'])


def needs_of(job):
    needs = job.get('needs') or []
    return [needs] if isinstance(needs, str) else list(needs)


def may_run(step, context):
    """False only when the step's `if` is false for this row in every executing run: it reads
    nothing but the row's own matrix values, a fixed runner's OS and the reuse decision
    (`env.AIR2LEAN_REUSED` is empty in an executing run). A status function, another step's
    output, a matrix value the row lacks (GitHub's null coercion) or any other context: True."""
    condition = step.get('if', True)
    if isinstance(condition, bool):
        return condition
    if re.search(r'\w\s*\(', condition):  # the evaluator's status functions have fixed values
        return True
    if context['runner.os'] is None and 'runner.os' in condition:
        return True
    if any(name not in context['matrix'] for name in re.findall(r'\bmatrix\.([\w-]+)', condition)):
        return True
    try:
        return TM.condition(condition, context)
    except TM.Unknown:
        return True


def job_definition(job, row):
    """The job with its matrix replaced by this row and without the steps that never run for it:
    other rows, and the steps other rows' conditions select, are not inputs of this part."""
    job = json.loads(canonical(job))
    if row is not None:
        job['strategy']['matrix']['include'] = [row]
        host = TM.runner_host(str(job.get('runs-on', '')))
        context = {'matrix': row, 'runner.os': host and TM.RUNNER_OS[host.split('-', 1)[1]]}
        job['steps'] = [step for step in job.get('steps') or [] if may_run(step, context)]
    return job


def tracked_tree(root, revision='HEAD'):
    """{path: (mode, object id)} of the commit's tree."""
    out = git(root, 'ls-tree', '-r', '-z', '--full-tree', revision).decode('utf-8', 'surrogateescape')
    tree = {}
    for item in out.split('\0'):
        if item:
            meta, path = item.split('\t', 1)
            mode, _kind, oid = meta.split()
            tree[path] = (mode, oid)
    return tree


def runner_identity(environ=os.environ):
    return {key: environ.get(key, 'local') for key in ('ImageOS', 'ImageVersion', 'RUNNER_OS', 'RUNNER_ARCH')}


def generated_digests(root):
    """{path: sha256 or None} of the whole-tree generated files in the worktree (installed from
    the run's `generated` job, which derives them from the whole tree; docs/ci.md)."""
    found = {}
    for rel in sorted(GENERATED.paths(root)):
        path = Path(root, rel)
        found[rel] = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    return found


def part_inputs(root, data, job_id, revision=None, entry=None, workflow=None):
    """The Inputs of a part (`entry`) or a restricted support job (entry None) of `job_id`."""
    workflow = workflow or load_workflow(root, revision)
    job = workflow['jobs'][job_id]
    forced = list(MACHINERY) + sorted(hashfiles_patterns(canonical(
        {'job': job, 'needs': {n: workflow['jobs'][n] for n in needs_of(job)}})))
    for need in needs_of(job):
        if need in RESTRICTED_SUPPORT:
            forced += support_inputs(data, need)
    defaults = data.get('defaults') or {}
    if entry is None:
        return Inputs(list(defaults.get('inputs', [])) + support_inputs(data, job_id), (), forced)
    return Inputs(list(defaults.get('inputs', [])) + list(entry.get('inputs', [])), entry.get('exclude', ()), forced)


def manifest(root, part, environ=os.environ, revision=None):
    """The key preimage of `part` at `revision` (default: HEAD's tree, the worktree's workflow and
    declarations); None for a part declared "reuse": false."""
    workflow = load_workflow(root, revision)
    found = parts(workflow)
    if part not in found:
        raise ReuseError('%s has no part %r' % (WORKFLOW, part))
    data = load_declarations(root, revision)
    entry = declaration(data, part)
    if entry.get('reuse') is False:
        return None
    job_id, row = found[part]
    jobs = workflow['jobs']
    needs = needs_of(jobs[job_id])
    definitions = {'job': job_definition(jobs[job_id], row), 'needs': {n: jobs[n] for n in needs},
                   'workflow': {k: v for k, v in workflow.items() if k != 'jobs'}}
    inputs = part_inputs(root, data, job_id, revision, entry, workflow)
    return {
        'schema': SCHEMA, 'part': part, 'job_name': RR.job_name(job_id, row) if row else job_id,
        'definitions': definitions, 'runner': runner_identity(environ),
        **content_preimage(root, inputs, revision or 'HEAD'),
        'generated': generated_digests(root) if 'generated' in needs else {},
    }


def content_preimage(root, inputs, revision='HEAD', tree=None):
    """The part of a key that the restricted checkout of `revision` shows: the declaration, the
    (path, mode, object id) of every declared file and the digest of all tracked names."""
    tree = tree or tracked_tree(root, revision)
    return {'declaration': inputs.describe(),
            'content': sorted([path, *tree[path]] for path in tree if inputs.content(path)),
            'names': sha256('\0'.join(sorted(tree)))}


def key_of(preimage):
    return sha256(canonical(preimage))


# --- Local runs (scripts/gate.sh): the checkout as a commit, restricted worktrees, records. ---

def snapshot(root):
    """A commit of the checkout's current content (tracked and new files, not ignored; HEAD its
    parent), made without touching the index or the worktree: what a local restricted run and
    its key see, as CI sees the tested commit."""
    root = Path(root)
    with tempfile.TemporaryDirectory() as scratch:
        index = Path(scratch) / 'index'
        if (git_dir(root) / 'index').is_file():
            index.write_bytes((git_dir(root) / 'index').read_bytes())  # stat data: rehash changed files only
        env = dict(os.environ, GIT_INDEX_FILE=str(index), **IDENTITY)
        git(root, 'add', '-A', env=env)
        tree = git(root, 'write-tree', env=env).decode().strip()
    return git(root, 'commit-tree', tree, '-p', 'HEAD', env=dict(os.environ, **IDENTITY),
               input=b'air2lean snapshot of the checkout\n').decode().strip()


class RestrictedWorktree:
    """`with RestrictedWorktree(root, inputs, label, revision) as dest:` a fresh worktree of
    `revision` restricted to `inputs` (restrict()); on exit `problems` lists the withheld files
    that were changed (check_restricted()), then the worktree is removed."""

    def __init__(self, root, inputs, label, revision):
        self.root, self.inputs, self.label, self.revision = Path(root), inputs, label, revision
        self.scratch = Path(tempfile.mkdtemp(prefix='air2lean-restricted.'))
        self.dest, self.problems = self.scratch / 'tree', []

    def __enter__(self):
        try:
            # No checkout: restrict() writes the tree, once.
            git(self.root, 'worktree', 'add', '--quiet', '--no-checkout', '--detach', str(self.dest), self.revision)
            with open(os.devnull, 'w') as null, contextlib.redirect_stdout(null):
                restrict(self.dest, self.inputs, self.label)
        except BaseException:
            self.remove()
            raise
        return self.dest

    def __exit__(self, *_exc):
        try:
            self.problems = check_restricted(self.dest)
            state = restricted_state(self.dest)
            for rel in (state or {}).get('withheld', []):
                if os.path.lexists(self.dest / rel) and not os.path.islink(self.dest / rel):
                    os.chmod(self.dest / rel, 0o644)
        finally:
            self.remove()
        return False

    def remove(self):
        git(self.root, 'worktree', 'remove', '--force', str(self.dest), check=False)
        shutil.rmtree(self.scratch, ignore_errors=True)


LOCAL_DECLARATIONS = 'assurance/gate-inputs.json'
LOCAL_SCHEMA = 'air2lean-gate-inputs/1'
LOCAL_KEYS = {'inputs', 'exclude', 'lean', 'note'}


def local_declarations(root):
    """{unit: entry} of the local units (scripts/gate.sh) with declared inputs: `inputs` and
    `exclude` patterns as a part's (after the `defaults` inputs, as in ci-inputs.json), and `lean`,
    modules, .lean files or directories whose package imports (transitively) are inputs too."""
    data = json.loads(Path(root, LOCAL_DECLARATIONS).read_text())
    if data.get('schema') != LOCAL_SCHEMA:
        raise ReuseError('%s: unknown schema %r' % (LOCAL_DECLARATIONS, data.get('schema')))
    defaults = (data.get('defaults') or {}).get('inputs', [])
    units = {}
    for unit, entry in (data.get('units') or {}).items():
        if set(entry) - LOCAL_KEYS or not entry.get('inputs'):
            raise ReuseError('%s: unit %r needs "inputs" (and only %s)' % (LOCAL_DECLARATIONS, unit,
                                                                          ', '.join(sorted(LOCAL_KEYS))))
        units[unit] = dict(entry, inputs=list(defaults) + list(entry['inputs']))
    return units


def changed_files(root, revision):
    """The files that differ between REVISION and the checkout (committed, staged or not; both
    paths of a rename) and the new ones (not ignored), sorted."""
    out = git(root, 'diff', '--name-only', '--no-renames', '-z', revision) + b'\0' \
        + git(root, 'ls-files', '-o', '--exclude-standard', '-z')
    return sorted({f for f in out.decode('utf-8', 'surrogateescape').split('\0') if f})


LOCAL_KIND = 'ci-reuse'


def local_store():
    """The store of local records: scripts/cas.py's (kind `ci-reuse`), in $AIR2LEAN_CAS_DIR (shared
    by the worktrees, evicted by `cas.py gc`), else in .lake/cas."""
    return GENERATED.CAS.Store(GENERATED.CAS.cas_dir() or ROOT / '.lake' / 'cas')


def record_local(key, body, files=()):
    """Publish a passing execution under KEY with the given (relative path, source) files: staged,
    then one rename (a concurrent publisher's record of the same key stands)."""
    store = local_store()
    staged = store.stage(LOCAL_KIND, key)
    for rel, source in files:
        (staged / 'files' / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, staged / 'files' / rel)
    store.publish(staged, LOCAL_KIND, key, dict(body, key=key))


def lookup_local(key):
    """The entry of KEY's local record (its `files/`), marked used, or None."""
    return local_store().lookup(LOCAL_KIND, key)


def withdraw_local(key):
    """Unpublish KEY's record at once (one rename), then delete it."""
    store = local_store()
    grave = store.stage('withdrawn', key)
    with contextlib.suppress(FileNotFoundError):
        os.rename(store.entry(LOCAL_KIND, key), grave / 'entry')
    shutil.rmtree(grave, ignore_errors=True)


# --- The restricted checkout (docs/ci.md#restricted-checkout). ---

def restrict(root, inputs, label, revision='HEAD', seal=False):
    """Check out a parentless commit with fixed metadata whose tree is `revision`'s with every
    file outside `inputs` replaced by the WITHHELD placeholder; make those files unreadable and
    skip-worktree, and record them. Returns the synthetic commit."""
    root = Path(root)
    state = git_dir(root) / RESTRICTED_STATE
    if state.exists():
        raise ReuseError('the checkout is already restricted (%s)' % state)
    tested = git(root, 'rev-parse', '--verify', revision + '^{commit}').decode().strip()
    tree = tracked_tree(root, revision)
    placeholder = git(root, 'hash-object', '-w', '--stdin', input=WITHHELD).decode().strip()
    withheld = sorted(path for path in tree if not inputs.content(path))
    hidden = set(withheld)
    lines = ['%s %s\t%s' % (*tree[path], path) if path not in hidden else '100644 %s\t%s' % (placeholder, path)
             for path in sorted(tree)]
    with tempfile.TemporaryDirectory() as scratch:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(scratch) / 'index'), **IDENTITY)
        git(root, 'update-index', '-z', '--index-info', env=env,
            input=''.join(line + '\0' for line in lines).encode('utf-8', 'surrogateescape'))
        restricted_tree = git(root, 'write-tree', env=env).decode().strip()
    commit = git(root, 'commit-tree', restricted_tree, env=dict(os.environ, **IDENTITY),
                 input=('air2lean restricted checkout of %s\n' % label).encode()).decode().strip()
    git(root, 'checkout', '--quiet', '--force', '--detach', commit)
    if withheld:
        git(root, 'update-index', '--skip-worktree', '-z', '--stdin',
            input=''.join(p + '\0' for p in withheld).encode('utf-8', 'surrogateescape'))
    for path in withheld:  # unreadable; an access time before the mtime makes any read update it
        os.chmod(root / path, 0)
        os.utime(root / path, ns=(0, os.stat(root / path).st_mtime_ns))
    if seal:
        seal_history(root, tested)
    since = max([os.stat(root / p, follow_symlinks=False).st_ctime_ns for p in withheld] or [0])
    state.write_text(canonical({'label': label, 'tested_commit': tested, 'commit': commit, 'placeholder': placeholder,
                                'withheld': withheld, 'since_ns': since}))
    print('restricted checkout of %s: HEAD %s (tested %s), %d of %d tracked files withheld'
          % (label, commit[:12], tested[:12], len(withheld), len(tree)))
    return commit


def discover(root, inputs, label):
    """Local diagnostic: leave the checkout whole, but report (check-restricted) every file outside
    `inputs` that the steps read, so that one passing run lists what a declaration lacks. Never
    used for a key or a record."""
    root = Path(root)
    state = git_dir(root) / RESTRICTED_STATE
    if state.exists():
        raise ReuseError('the checkout is already restricted (%s)' % state)
    tested = git(root, 'rev-parse', '--verify', 'HEAD^{commit}').decode().strip()
    withheld = sorted(path for path in tracked_tree(root) if not inputs.content(path))
    if withheld:  # git then never stats or reads them; an access time before the mtime updates on any read
        git(root, 'update-index', '--skip-worktree', '-z', '--stdin',
            input=''.join(p + '\0' for p in withheld).encode('utf-8', 'surrogateescape'))
    for path in withheld:
        if not os.path.islink(root / path):
            os.utime(root / path, ns=(0, os.stat(root / path).st_mtime_ns))
    state.write_text(canonical({'label': label, 'tested_commit': tested, 'commit': tested, 'discover': True,
                                'withheld': withheld, 'since_ns': 1}))
    print('discovery for %s: %d tracked files outside the declared inputs are watched' % (label, len(withheld)))


def seal_history(root, tested):
    """Drop every remote (with the credentials actions/checkout configured for it), ref, reflog
    and unreachable object, so that the withheld content is not in the repository at all (not
    even through `git show $GITHUB_SHA:path`) and no `git fetch origin` brings it back; CI only."""
    for remote in git(root, 'remote').decode().split():
        git(root, 'remote', 'remove', remote)
    for key in git(root, 'config', '--local', '--name-only', '--get-regexp', r'^(http\..*\.extraheader|includeif\..*)$',
                   check=False).decode().split():
        git(root, 'config', '--local', '--unset-all', key)
    for ref in git(root, 'for-each-ref', '--format=%(refname)').decode().split():
        git(root, 'update-ref', '-d', ref)
    git(root, 'reflog', 'expire', '--expire=now', '--all')
    git(root, 'repack', '-a', '-d', '-q')
    git(root, 'prune', '--expire=now')
    shallow = git_dir(root) / 'shallow'
    if shallow.exists():
        shallow.unlink()
    if subprocess.run(['git', '-C', str(root), 'cat-file', '-e', tested + '^{tree}'],
                      capture_output=True).returncode == 0:
        raise ReuseError('the tested commit %s is still in the repository after sealing' % tested)


def unrestrict(root):
    """Undo restrict(): back to the tested commit with every file readable (local runs)."""
    state = restricted_state(root)
    if state is None:
        return
    for rel in state['withheld']:
        if os.path.lexists(Path(root, rel)) and not state.get('discover'):
            os.chmod(Path(root, rel), 0o644)
    if state['withheld']:
        git(root, 'update-index', '--no-skip-worktree', '-z', '--stdin',
            input=''.join(p + '\0' for p in state['withheld']).encode('utf-8', 'surrogateescape'))
    git(root, 'checkout', '--quiet', '--force', state['tested_commit'])
    (git_dir(root) / RESTRICTED_STATE).unlink()


def restricted_state(root):
    state = git_dir(root) / RESTRICTED_STATE
    return json.loads(state.read_text()) if state.is_file() else None


def check_restricted(root, as_root=None, reset=False):
    """Problems: withheld files that a step changed, or (when the steps run as root, which the
    missing permission does not stop) read: atime after the checkout. As another user a read
    already failed, and an access time can come from a system daemon (Spotlight on macOS).
    Empty when the checkout is not restricted."""
    as_root = os.geteuid() == 0 if as_root is None else as_root
    state = restricted_state(root)
    if state is None:
        return []
    problems = []
    if state.get('discover'):  # symlinks keep their checkout atime; a removed file was not read
        read = [rel for rel in state['withheld'] if os.path.isfile(Path(root, rel)) and not os.path.islink(Path(root, rel))
                and os.stat(Path(root, rel)).st_atime_ns > state['since_ns']]
        if reset:  # the next check reports only what later steps read
            for rel in read:
                os.utime(Path(root, rel), ns=(0, os.stat(Path(root, rel)).st_mtime_ns))
        return ['%s: undeclared file was read' % rel for rel in read]
    for rel in state['withheld']:
        path = Path(root, rel)
        try:
            info = os.stat(path, follow_symlinks=False)
        except FileNotFoundError:
            problems.append('%s: withheld file was removed' % rel)
            continue
        if info.st_mode & 0o777 or info.st_size != len(WITHHELD):
            problems.append('%s: withheld file was changed' % rel)
        elif as_root and info.st_atime_ns > state['since_ns']:
            problems.append('%s: withheld file was read' % rel)
    return problems


# --- Workflow checks: declarations complete, steps guarded, no run-specific expressions. ---

def check_workflow(root, revision=None):
    workflow = load_workflow(root, revision)
    data = load_declarations(root, revision)
    errors = []
    found = parts(workflow)
    declared = set((data.get('parts') or {}))
    for part in sorted(set(found) - declared):
        errors.append('part %s has no declaration in %s' % (part, DECLARATIONS))
    for part in sorted(declared - set(found)):
        errors.append('%s declares %s, which is not a part of %s' % (DECLARATIONS, part, WORKFLOW))
    for part in sorted(set(found) & declared):
        try:
            declaration(data, part)
        except ReuseError as error:
            errors.append(str(error))
    for job_id in RESTRICTED_SUPPORT:
        try:
            support_inputs(data, job_id)
        except ReuseError as error:
            errors.append(str(error))
        names = [s.get('name') for s in workflow['jobs'].get(job_id, {}).get('steps') or []]
        if names[1:2] != [RESTRICT_STEP]:
            errors.append('support job %s does not run %r right after its checkout' % (job_id, RESTRICT_STEP))
    for job_id in sorted({job for job, _ in found.values()}):
        steps = workflow['jobs'][job_id].get('steps') or []
        names = [s.get('name') for s in steps]
        if DECISION_STEP not in names:
            errors.append('job %s has no %r step' % (job_id, DECISION_STEP))
            continue
        start = names.index(DECISION_STEP)
        for step in steps[start + 1:]:
            condition = str(step.get('if', ''))
            if step.get('name') == REFERENCE_STEP:
                if condition != "${{ env.AIR2LEAN_REUSED != '' }}":
                    errors.append('job %s step %r must run exactly when the part was reused' % (job_id, REFERENCE_STEP))
                continue
            if GUARD not in condition:
                errors.append('job %s step %r runs after %r without %s in its if'
                              % (job_id, step.get('name'), DECISION_STEP, GUARD))
            elif '||' in condition and not all(GUARD in d for d in condition.split('||')):
                errors.append('job %s step %r: every || branch of its if needs %s' % (job_id, step.get('name'), GUARD))
            if step.get('name') not in RECORD_STEPS and RUN_SPECIFIC.search(canonical(step)):
                errors.append('job %s step %r uses a run-specific github.* expression' % (job_id, step.get('name')))
        if RUN_SPECIFIC.search(canonical({k: v for k, v in workflow['jobs'][job_id].items() if k != 'steps'})):
            errors.append('job %s uses a run-specific github.* expression outside its steps' % job_id)
    return errors


# --- CI steps: decide (lookup), record. ---

def api(path, token, base=None):
    base = base or os.environ.get('GITHUB_API_URL', 'https://api.github.com')
    request = urllib.request.Request(base + path, headers={
        'Accept': 'application/vnd.github+json', 'Authorization': 'Bearer ' + token,
        'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.loads(response.read())


def on_main(repository, commit, token, fetch=api):
    """Whether `commit` is main or an ancestor of it (GitHub compare API)."""
    compared = fetch('/repos/%s/compare/%s...main' % (repository, commit), token)
    return compared.get('status') in ('identical', 'ahead')


def lookup(key, job_name, repository, token, fetch=api, events=RECORD_EVENTS, require_main=False):
    """The newest acceptable record of `key`: (run id, run URL, job id, job URL) or None.

    Accepted only from this repository's CI workflow (never a fork's head repository), from a
    run of one of `events`, whose job `job_name` completed with success, per the GitHub API;
    with `require_main`, only from a run whose head commit is on main.
    """
    listed = fetch('/repos/%s/actions/artifacts?name=ci-reuse-%s&per_page=30' % (repository, key), token)
    for artifact in sorted(listed.get('artifacts', []), key=lambda a: a.get('created_at', ''), reverse=True):
        source = artifact.get('workflow_run') or {}
        if artifact.get('expired') or artifact.get('name') != 'ci-reuse-' + key:
            continue
        if source.get('head_repository_id') != source.get('repository_id') or not source.get('id'):
            continue
        run = fetch('/repos/%s/actions/runs/%d' % (repository, source['id']), token)
        if (run.get('path') != WORKFLOW or run.get('name') != WORKFLOW_NAME or run.get('event') not in events
                or (run.get('head_repository') or {}).get('full_name') != repository):
            continue
        if require_main and not on_main(repository, run.get('head_sha', ''), token, fetch):
            continue
        page = 1
        while True:
            jobs = fetch('/repos/%s/actions/runs/%d/jobs?filter=all&per_page=100&page=%d'
                         % (repository, source['id'], page), token)
            for job in jobs.get('jobs', []):
                if job.get('name') == job_name and job.get('status') == 'completed' and job.get('conclusion') == 'success':
                    return source['id'], run.get('html_url'), job.get('id'), job.get('html_url')
            if len(jobs.get('jobs', [])) < 100:
                break
            page += 1
    return None


def self_check_part(environ, all_parts):
    """The one part this run executes even when a record exists (same choice in every row)."""
    seed = '%s:%s' % (environ.get('GITHUB_RUN_ID', ''), environ.get('GITHUB_RUN_ATTEMPT', ''))
    ordered = sorted(all_parts)
    return ordered[int(sha256(seed), 16) % len(ordered)] if ordered else None


def append(path, text):
    if path:
        with open(path, 'a', encoding='utf-8') as handle:
            handle.write(text)


def decide(root, job_id, row_json, environ=os.environ, fetch=api):
    row = json.loads(row_json) if row_json else None
    part = part_id(job_id, row or None)
    if not environ.get('GITHUB_RUN_ID'):
        print('%s: not a GitHub Actions run: the checkout stays unrestricted, no record' % part)
        return 0
    env_file, summary = environ.get('GITHUB_ENV'), environ.get('GITHUB_STEP_SUMMARY')
    data = load_declarations(root)
    entry = declaration(data, part)
    preimage = manifest(root, part, environ)
    event = environ.get('AIR2LEAN_EVENT', '')
    if preimage is None:
        append(summary, '**%s** always runs (`"reuse": false` in %s).\n' % (part, DECLARATIONS))
        return 0
    if event in FULL_EVENTS:
        append(summary, '**%s** runs on the whole checkout (%s run: no reuse, no restriction, no record).\n'
               % (part, event))
        return 0
    key = key_of(preimage)
    out = Path(environ['RUNNER_TEMP']) / 'ci-reuse'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'manifest.json').write_text(canonical(preimage))
    tested = git(root, 'rev-parse', 'HEAD').decode().strip()
    lines = ['AIR2LEAN_PART=' + part, 'AIR2LEAN_REUSE_KEY=' + key, 'AIR2LEAN_TESTED_COMMIT=' + tested]
    message = '**%s** input key `%s`' % (part, key)
    if event in ('pull_request',) + MAIN_EVENTS:
        queue = event in MAIN_EVENTS
        found = None
        try:
            found = lookup(key, preimage['job_name'], environ['GITHUB_REPOSITORY'], environ.get('GH_TOKEN', ''), fetch,
                           QUEUE_RECORD_EVENTS if queue else RECORD_EVENTS, require_main=queue)
        except (urllib.error.URLError, OSError, ValueError, KeyError) as error:
            print('record lookup failed (%s): the part runs' % error)
        chosen = None if queue else self_check_part(
            environ, [p for p in parts(load_workflow(root)) if (data['parts'].get(p) or {}).get('reuse') is not False])
        if found and part != chosen:
            run_id, run_url, job_id_, job_url = found
            (out / 'reference.json').write_text(canonical({
                'schema': SCHEMA, 'part': part, 'job_name': preimage['job_name'], 'key': key, 'tested_commit': tested,
                'reused_in_run': environ.get('GITHUB_RUN_ID'), 'run_id': run_id, 'run_url': run_url,
                'job_id': job_id_, 'job_url': job_url}))
            append(env_file, '\n'.join(lines + ['AIR2LEAN_REUSED=%s' % run_url]) + '\n')
            append(summary, '%s: **reused** - passed in run [%s](%s), job [%s](%s), on a tree with the same '
                   'input key. Every later step is skipped (docs/ci.md#where-records-live-and-how-a-reused-'
                   'result-is-attested).\n' % (message, run_id, run_url, job_id_, job_url))
            print('reused: %s passed in run %s (%s) with key %s' % (part, run_id, job_url, key))
            return 0
        if found:
            lines.append('AIR2LEAN_SELF_CHECK=%s' % found[1])
            message += ': **self-check** - recorded green in run [%s](%s); executing it again' % (found[0], found[1])
        else:
            message += ': no record, executing'
    restrict(root, part_inputs(root, data, job_id, entry=entry), part, seal=True)
    if event in RECORD_EVENTS:
        lines.append('AIR2LEAN_RECORD=1')
    append(env_file, '\n'.join(lines) + '\n')
    append(summary, message + ' in a restricted checkout.\n')
    print(message)
    return 0


def record(root, out, environ=os.environ):
    part, key, tested = (environ.get('AIR2LEAN_PART'), environ.get('AIR2LEAN_REUSE_KEY'),
                         environ.get('AIR2LEAN_TESTED_COMMIT'))
    if not part or not key or not tested:
        raise ReuseError('no part, key or tested commit in the environment: the decision step did not arm a record')
    state = restricted_state(root)
    if state is None or state['tested_commit'] != tested or state['label'] != part:
        raise ReuseError('%s did not run in its restricted checkout; no record' % part)
    problems = check_restricted(root)
    if problems:
        raise ReuseError('%s touched withheld files; no record: %s' % (part, '; '.join(problems[:5])))
    preimage = json.loads(Path(environ['RUNNER_TEMP'], 'ci-reuse', 'manifest.json').read_text())
    head = git(root, 'rev-parse', 'HEAD').decode().strip()
    if key_of(preimage) != key or head != state['commit'] or (
            preimage['generated'] and generated_digests(root) != preimage['generated']):
        raise ReuseError('the inputs of %s changed during the run; no record' % part)
    body = {'schema': SCHEMA, 'key': key, 'part': part, 'job_name': preimage['job_name'],
            'run_id': environ.get('GITHUB_RUN_ID'), 'run_attempt': environ.get('GITHUB_RUN_ATTEMPT'),
            'event': environ.get('AIR2LEAN_EVENT'), 'tested_commit': tested, 'restricted_commit': state['commit'],
            'withheld': len(state['withheld']), 'manifest': preimage}
    Path(out).write_text(canonical(body))
    print('record ci-reuse-%s for %s' % (key, part))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--root', type=Path, default=ROOT)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('key')
    p.add_argument('--part', required=True)
    p.add_argument('--manifest', type=Path)
    p = sub.add_parser('decide')
    p.add_argument('--job', required=True)
    p.add_argument('--row', default='')
    p = sub.add_parser('restrict')
    target = p.add_mutually_exclusive_group(required=True)
    target.add_argument('--part')
    target.add_argument('--support', choices=RESTRICTED_SUPPORT)
    p.add_argument('--seal', action='store_true', help='CI: remove the tested commit from the repository')
    p.add_argument('--discover', action='store_true',
                   help='local diagnostic: keep the checkout whole, list the undeclared files read')
    p = sub.add_parser('check-restricted')
    p.add_argument('--reset', action='store_true', help='discover mode: forget the reads reported')
    sub.add_parser('unrestrict')
    p = sub.add_parser('record')
    p.add_argument('--out', type=Path, required=True)
    sub.add_parser('check-workflow')
    args = parser.parse_args(argv)
    try:
        if args.command == 'key':
            preimage = manifest(args.root, args.part)
            if preimage is None:
                print('%s: "reuse": false' % args.part)
                return 0
            if args.manifest:
                args.manifest.write_text(canonical(preimage))
            print(key_of(preimage))
            return 0
        if args.command == 'decide':
            return decide(args.root, args.job, args.row)
        if args.command == 'restrict':
            data = load_declarations(args.root)
            if args.support:
                restrict(args.root, part_inputs(args.root, data, args.support), args.support, seal=args.seal)
            else:
                job_id, _row = parts(load_workflow(args.root))[args.part]
                entry = declaration(data, args.part)
                if entry.get('reuse') is False:
                    raise ReuseError('%s is "reuse": false: it runs on the whole checkout' % args.part)
                inputs = part_inputs(args.root, data, job_id, entry=entry)
                if args.discover:
                    discover(args.root, inputs, args.part)
                else:
                    restrict(args.root, inputs, args.part, seal=args.seal)
            return 0
        if args.command == 'unrestrict':
            unrestrict(args.root)
            return 0
        if args.command == 'check-restricted':
            problems = check_restricted(args.root, reset=args.reset)
            for problem in problems:
                print('error: %s (declare it in %s if the part needs it)' % (problem, DECLARATIONS), file=sys.stderr)
            return 1 if problems else 0
        if args.command == 'record':
            return record(args.root, args.out)
        if args.command == 'check-workflow':
            errors = check_workflow(args.root)
            for error in errors:
                print('error: ' + error, file=sys.stderr)
            if not errors:
                print('OK: every part of %s is declared and every step after the reuse decision is guarded' % WORKFLOW)
            return 1 if errors else 0
    except (ReuseError, RR.ReleaseError, OSError, ValueError) as error:
        print('error: %s' % error, file=sys.stderr)
        return 2
    return 2


if __name__ == '__main__':
    sys.exit(main())
