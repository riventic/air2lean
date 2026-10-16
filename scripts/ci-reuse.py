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
  ci-reuse.py trace SPEC                        (local runs) one traced unit: scripts/gate.py, fixture-checks.py

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

Local runs (scripts/gate.sh, scripts/fixture-checks.py; docs/ci.md#traced-records) key a unit by
what it read instead: the checkout's content is a parentless commit (`snapshot`); the unit runs
in a fresh repository of it, with copy-on-write clones of the Lake builds and generated files,
under a sandbox that lets it read nothing outside but roots keyed by identity and
content-addressed caches (`Outside`); every file and directory of the tree starts with an access
time before its modification time, so the run's reads are those whose access time moved
(`watch`, which `discover` uses too). A pass is a *record* (`Records`): the digest of every file
the unit read and of the names in every directory a probe could have looked in, stored under
the unit's *pre-key* (what it runs, its environment, the identities outside, this machinery) in
scripts/cas.py's store, kind `ci-reuse`.
"""
import argparse
import concurrent.futures
import contextlib
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
    tree = tracked_tree(root, revision or 'HEAD')
    return {
        'schema': SCHEMA, 'part': part, 'job_name': RR.job_name(job_id, row) if row else job_id,
        'definitions': definitions, 'runner': runner_identity(environ), 'declaration': inputs.describe(),
        'content': sorted([path, *tree[path]] for path in tree if inputs.content(path)),
        'names': sha256('\0'.join(sorted(tree))),
        'generated': generated_digests(root) if 'generated' in needs else {},
    }


def key_of(preimage):
    return sha256(canonical(preimage))


# --- Local runs (scripts/gate.sh, scripts/fixture-checks.py): traced records. --------------------
# ---- key-relevant: begin
# From here to `key-relevant: end`: how a traced unit runs and what its record covers. The text
# is part of every pre-key (MACHINERY_KEY), so a change here reruns every unit.

TRACE_SCHEMA = 'air2lean-traced/1'
LOCAL_KIND = 'ci-reuse'
NOISE = {'__pycache__', '.DS_Store'}
# The caller's environment a traced unit keeps: these variables and the prefixed ones, every one
# keyed but the scheduling ones (worker counts, memory slots, locks); every other one is dropped.
ENV_NAMES = frozenset({'PATH', 'HOME', 'USER', 'LOGNAME', 'SHELL', 'LANG', 'TZ'})
ENV_PREFIXES = ('LC_', 'AIR2LEAN_', 'ELAN_', 'LEAN_', 'LAKE_', 'ZIG_')
SCHEDULING = frozenset({'AIR2LEAN_JOBS', 'AIR2LEAN_MEM_MIB', 'AIR2LEAN_LOCK_WAIT', 'AIR2LEAN_BUILD_LOCK',
                        'LEAN_NUM_THREADS'})


def snapshot(root):
    """A commit of the checkout's current content (tracked and new files, not ignored) with no
    parent and fixed metadata, so that its id is a function of that content; made without
    touching the index or the worktree."""
    root = Path(root)
    with tempfile.TemporaryDirectory() as scratch:
        index = Path(scratch) / 'index'
        if (git_dir(root) / 'index').is_file():
            index.write_bytes((git_dir(root) / 'index').read_bytes())  # stat data: rehash changed files only
        env = dict(os.environ, GIT_INDEX_FILE=str(index), **IDENTITY)
        git(root, 'add', '-A', env=env)
        tree = git(root, 'write-tree', env=env).decode().strip()
    return git(root, 'commit-tree', tree, env=dict(os.environ, **IDENTITY),
               input=b'air2lean snapshot of the checkout\n').decode().strip()


def changed_files(root, revision):
    """The files that differ between REVISION and the checkout (committed, staged or not; both
    paths of a rename) and the new ones (not ignored), sorted."""
    out = git(root, 'diff', '--name-only', '--no-renames', '-z', revision) + b'\0' \
        + git(root, 'ls-files', '-o', '--exclude-standard', '-z')
    return sorted({f for f in out.decode('utf-8', 'surrogateescape').split('\0') if f})


def local_store():
    """The store of local records: scripts/cas.py's (kind `ci-reuse`), in $AIR2LEAN_CAS_DIR (shared
    by the worktrees, evicted by `cas.py gc`), else in .lake/cas."""
    return GENERATED.CAS.Store(GENERATED.CAS.cas_dir() or ROOT / '.lake' / 'cas')


def object_dir(root):
    """The object store of ROOT's repository (shared by its worktrees)."""
    return Path(git(root, 'rev-parse', '--path-format=absolute', '--git-common-dir').decode().strip()) / 'objects'


def file_id(path):
    """'mode:git object id' of the file or symlink PATH (as a tree lists it), None when absent."""
    path = Path(path)
    if path.is_symlink():
        mode, data = '120000', os.readlink(path).encode('utf-8', 'surrogateescape')
    elif path.is_file():
        mode, data = '100755' if os.access(path, os.X_OK) else '100644', path.read_bytes()
    else:
        return None
    return '%s:%s' % (mode, hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest())


def cloned_entries(root):
    """The ignored entries a traced tree gets as copy-on-write clones: every package's Lake build
    (`<package>/.lake/build`) and the whole-tree generated files (assurance/generated.json) the
    checkout has; nothing else that git ignores (tool caches, scratch output)."""
    packages = {str(Path(f).parent) for f in git(root, 'ls-files', '-z', '-co', '--exclude-standard', '--',
                                                  '*lakefile.toml', '*lakefile.lean')
                .decode('utf-8', 'surrogateescape').split('\0') if f}
    builds = sorted(('' if p == '.' else p + '/') + '.lake/build' for p in packages)
    return [b for b in builds if Path(root, b).is_dir()] + sorted(p for p in GENERATED.paths(Path(root))
                                                                   if Path(root, p).is_file())


def clone_state(root, entries):
    """{entry: digest} of the cloned ENTRIES of ROOT: a build's path-size-mtime digest, a file's id."""
    return {rel: GENERATED.CAS.tree_stat(Path(root, rel)) if Path(root, rel).is_dir() else file_id(Path(root, rel))
            for rel in entries}


def tree_paths(dest):
    """Every file (not symlink) and directory (`DIR/`, the top `./`) under DEST but `.git`."""
    out = []
    for dirpath, dirnames, filenames in os.walk(dest):
        here = Path(dirpath)
        rel = here.relative_to(dest).as_posix()
        if rel == '.':
            dirnames[:] = [d for d in dirnames if d != '.git']
            filenames = [f for f in filenames if f != '.git']
        out.append(rel + '/')
        out += [f if rel == '.' else rel + '/' + f for f in filenames if not (here / f).is_symlink()]
    return out


def watch(root, paths):
    """Give each of PATHS (relative to ROOT; a directory `DIR/`) an access time before its
    modification time, so that a read, mmap, exec or listing of it (not a stat) moves it."""
    for rel in paths:
        path = Path(root, rel)
        with contextlib.suppress(FileNotFoundError):
            if not path.is_symlink():
                os.utime(path, ns=(0, os.stat(path).st_mtime_ns))


def read_since(root, paths):
    """Those of PATHS whose access time moved since watch() (one removed since counts as read)."""
    out = []
    for rel in paths:
        try:
            if os.stat(Path(root, rel), follow_symlinks=False).st_atime_ns != 0:
                out.append(rel)
        except FileNotFoundError:
            out.append(rel)
    return out


def _quote(path):
    return '"%s"' % str(path).replace('\\', '\\\\').replace('"', '\\"')


class Outside:
    """What a traced unit may read outside its tree (docs/ci.md#traced-records). *Keyed roots*
    enter every pre-key by identity: the sealed system volume by the OS build, the developer
    directories by their version and receipt files, a Homebrew prefix by its formulas' install
    receipts and every other file's path, size and modification time, every other root (Elan, the
    stock Zig toolchains, /etc, /usr/local) by that path-size-mtime digest (scripts/cas.py
    tree_stat). *Caches* are content-addressed (the CAS, Zig's global cache, git's objects, xcrun's
    lookup cache) or coordinate (build-guard's locks); they are read and written, never keyed.
    The sandbox (macOS sandbox-exec) makes every other path read as absent (ENOENT, also for one
    that exists) and refuses writes outside the unit's own directory and the caches. Where it does
    not apply (another OS; inside a sandbox already), `available()` is false: nothing is recorded
    or reused."""

    SYSTEM = ('/System', '/usr', '/bin', '/sbin', '/System/Volumes/Preboot/Cryptexes')
    HIDDEN = ('/System/Volumes',)  # other volumes, the data volume's firmlinks among them
    BREW_HIDDEN = ('Caskroom', 'Library', '.git', 'var/homebrew')

    def __init__(self, root, keyed=None):
        self.root = Path(root)
        home, real = Path.home(), os.path.realpath
        self.keyed, self.hidden, self.files = {}, [], {}  # keyed, files: real path -> identity kind
        self.given = []  # the paths as named (through symlinks such as /var)

        def add(path, kind, into=None):  # a single file (INTO): the path itself, not a link's target
            if path and os.path.lexists(path):
                self.given.append(str(path))
                path = real(path) if into is None else os.path.join(real(os.path.dirname(path)), os.path.basename(path))
                (self.keyed if into is None else into)[path] = kind

        for p in self.SYSTEM:
            add(p, 'system')
        self.hidden += [real(p) for p in self.HIDDEN]
        developer = real('/var/db/xcode_select_link') if os.path.islink('/var/db/xcode_select_link') else ''
        add(developer[:developer.index('.app/') + 4] if '.app/' in developer else developer, 'developer')
        add('/Library/Developer/CommandLineTools', 'developer')
        add('/', 'listing', self.files)
        add('/private/var/db/xcode_select_link', 'link', self.files)
        add('/Library/Preferences/com.apple.dt.Xcode.plist', 'file', self.files)  # the license acceptance
        brew = os.environ.get('HOMEBREW_PREFIX') or ('/opt/homebrew' if os.path.isdir('/opt/homebrew') else '')
        add(brew, 'homebrew')
        self.hidden += [real(Path(brew, p)) for p in self.BREW_HIDDEN] if brew else []
        add(os.environ.get('ELAN_HOME') or home / '.elan', 'tree')
        cache = Path(os.environ.get('AIR2LEAN_CACHE') or home / '.cache/air2lean')
        for p in sorted(cache.glob('host-*')):
            add(p, 'tree')
        for name, value in sorted(os.environ.items()):
            if name.startswith('AIR2LEAN_HOST_ZIG_') and value:
                add(Path(value).parent, 'tree')
        for p in ('/private/etc', '/usr/local', '/private/var/db/timezone'):
            add(p, 'tree')
        for path, kind in (keyed or {}).items():
            add(path, kind)
        lock = Path(os.environ.get('AIR2LEAN_BUILD_LOCK') or cache / 'build.lock')
        zig_cache = os.environ.get('ZIG_GLOBAL_CACHE_DIR') or \
            Path(os.environ.get('XDG_CACHE_HOME') or home / '.cache') / 'zig'
        caches = [str(p) for p in (GENERATED.CAS.cas_dir() or self.root / '.lake' / 'cas', zig_cache, lock,
                                   str(lock) + '.d', '/dev')]
        stores = [str(object_dir(self.root))]  # read only
        self.given += caches + stores
        self.caches, self.stores = [real(p) for p in caches], [real(p) for p in stores]
        user_temp = subprocess.run(['getconf', 'DARWIN_USER_TEMP_DIR'], capture_output=True, text=True).stdout.strip()
        self.xcrun = '^%s/xcrun_db' % re.escape(real(user_temp).rstrip('/')) if user_temp else None
        # The top-level symlinks (/var, /tmp, /etc: part of the keyed listing of /) and the temporary
        # directory xcrun names.
        self.given += [os.path.join('/', n) for n in os.listdir('/') if os.path.islink(os.path.join('/', n))]
        self.given += [user_temp] if user_temp else []
        self._identity, self._available = None, None

    def readable(self, path):
        """Whether PATH lies in a keyed root, a cache or a store (and in no hidden part)."""
        path = os.path.realpath(path)

        def under(roots):
            return max((len(r) for r in roots if path == r or path.startswith(r.rstrip('/') + '/')), default=-1)
        return max(under(self.keyed), under(self.caches), under(self.stores)) > under(self.hidden)

    def environment(self):
        """(env, keyed): the caller's variables a traced unit keeps (ENV_NAMES, ENV_PREFIXES), PATH
        without the directories that read as absent; keyed: all but the SCHEDULING ones."""
        env = {k: v for k, v in os.environ.items() if k in ENV_NAMES or k.startswith(ENV_PREFIXES)}
        if 'PATH' in env:
            env['PATH'] = os.pathsep.join(p for p in env['PATH'].split(os.pathsep) if p and self.readable(p))
        return env, {k: v for k, v in env.items() if k not in SCHEDULING}

    def _identify(self, item):
        path, kind = item
        if kind == 'system':
            return [platform.platform()] + [subprocess.run(argv, capture_output=True, text=True).stdout for argv in
                                            (['sysctl', '-n', 'kern.osversion', 'kern.osproductversion'], ['sw_vers'])
                                            if shutil.which(argv[0])]
        if kind == 'developer' and path.endswith('.app'):
            return [file_id(Path(path, 'Contents', f)) for f in ('version.plist', 'Info.plist')]
        if kind == 'developer' and path == '/Library/Developer/CommandLineTools':  # its packages' receipts
            return [[str(r), file_id(r)] for d in ('/Library/Apple/System/Library/Receipts', '/private/var/db/receipts')
                    for r in sorted(Path(d).glob('com.apple.pkg.CLTools_*.plist'))]
        if kind == 'homebrew':
            kegs = sorted(Path(path, 'Cellar').glob('*/*'))
            return [GENERATED.CAS.tree_stat(path, exclude=[Path(path, p) for p in ('Cellar',) + self.BREW_HIDDEN]),
                    [[k.relative_to(path).as_posix(), file_id(k / 'INSTALL_RECEIPT.json')] for k in kegs]]
        if kind == 'listing':
            return sorted(os.listdir(path))
        if kind == 'link':
            return os.readlink(path)
        if kind == 'file':
            return file_id(path)
        return GENERATED.CAS.tree_stat(path)

    def identity(self, fresh=False):
        """{path: identity} of every keyed root and file (computed once; FRESH: again)."""
        if self._identity is None or fresh:
            items = sorted(self.keyed.items()) + sorted(self.files.items())
            with concurrent.futures.ThreadPoolExecutor(8) as pool:
                values = list(pool.map(self._identify, items))
            identity = {path: [kind, value] for (path, kind), value in zip(items, values)}
            if fresh:
                return identity
            self._identity = identity
        return self._identity

    def profile(self, private, extra=()):
        """The sandbox profile (SBPL) of a unit whose own directory is PRIVATE, which may also read
        the EXTRA directories (content-addressed, such as a patched compiler outside the CAS)."""
        given = [*self.given, str(private), *map(str, extra)]
        private = os.path.realpath(private)
        rules = [(p, 'allow') for p in [*self.keyed, *self.caches, *self.stores, private,
                                        *map(os.path.realpath, extra)]]
        rules += [(p, 'hide') for p in self.hidden]
        lines = ['(version 1)', '(allow default)', '(deny file-read* (with errno ENOENT))']
        # The last matching rule wins: broader paths first.
        for path, rule in sorted(rules, key=lambda r: (r[0].count('/'), r[0])):
            lines.append('(%s file-read* (subpath %s)%s)' % ('allow' if rule == 'allow' else 'deny', _quote(path),
                                                             '' if rule == 'allow' else ' (with errno ENOENT)'))
        lines.append('(allow file-read* %s)' % ' '.join('(literal %s)' % _quote(p) for p in self.files))
        # A path lookup (realpath, getcwd) stats each directory above what the unit may read, as
        # named and as resolved, and reads each symlink on the way; it sees their metadata, never
        # a directory's entries.
        above = {str(a) for p in given for q in (p, os.path.realpath(p)) for a in Path(q).parents}
        above |= {p for p in given if os.path.islink(p)}
        lines.append('(allow file-read-metadata %s)' % ' '.join('(literal %s)' % _quote(a) for a in sorted(above)))
        lines.append('(deny file-write* (with errno EACCES))')
        lines.append('(allow file-write* %s)' % ' '.join('(subpath %s)' % _quote(p) for p in [private, *self.caches]))
        if self.xcrun:
            lines.append('(allow file-read* file-write* (regex #"%s"))' % self.xcrun.replace('\\', '\\\\'))
        return '\n'.join(lines) + '\n'

    def available(self):
        """Whether the sandbox applies here and hides what it must: under it, the checkout's
        repository HEAD reads as absent."""
        if self._available is None:
            self._available = False
            head = git_dir(self.root) / 'HEAD'
            if platform.system() == 'Darwin' and shutil.which('sandbox-exec') and head.is_file():
                with tempfile.TemporaryDirectory() as private:
                    profile = Path(private) / 'profile.sb'
                    profile.write_text(self.profile(private))
                    probe = subprocess.run(['sandbox-exec', '-f', str(profile), '/bin/test', '-e', str(head)],
                                           capture_output=True)
                    self._available = probe.returncode == 1
        return self._available


def trace(spec_path):
    """`ci-reuse.py trace SPEC`: SPEC's command in a fresh repository of SPEC's commit at SPEC's
    `dest` (no history, no refs; objects shared with ROOT), with the cloned entries, under SPEC's
    sandbox profile. Then {reads, record, reason} go to SPEC's `trace` (the record of a pass, None
    with the reason when the run cannot have one: no sandbox, or what it cloned changed), a pass
    copies SPEC's `outputs` back to the checkout, and the tree is removed. Exit status: the
    command's."""
    s = json.loads(Path(spec_path).read_text())
    root, dest, private = Path(s['root']), Path(s['dest']), Path(s['private'])
    _spec = importlib.util.spec_from_file_location('air2lean_check_tree', ROOT / 'scripts/check-tree.py')
    check_tree = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(check_tree)
    # The tree is the commit's content whatever the user's or system's git configuration says.
    hermetic = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1')
    try:
        subprocess.run(['git', 'init', '--quiet', '--template=', str(dest)], check=True, env=hermetic)
        (dest / '.git/objects/info/alternates').write_text('%s\n' % object_dir(root))
        git(dest, 'update-ref', '--no-deref', 'HEAD', s['commit'], env=hermetic)
        # Resetting access times changes inode change times; git still compares modification
        # time, size and inode.
        git(dest, 'config', 'core.trustctime', 'false', env=hermetic)
        git(dest, 'checkout', '--quiet', '--force', 'HEAD', env=hermetic)
        before = clone_state(root, s['clone'])
        for rel in s['clone']:
            check_tree.clone_tree(root / rel, dest / rel)
        # The unit's `git status` must reread no unchanged file: every file is older than the
        # index, which is refreshed (no racily clean entry).
        for rel in git(dest, 'ls-files', '-z').decode('utf-8', 'surrogateescape').split('\0'):
            path = dest / rel
            if rel and path.is_file() and not path.is_symlink():
                info = os.stat(path)
                os.utime(path, ns=(info.st_atime_ns, info.st_mtime_ns - 2_000_000_000))
        git(dest, 'update-index', '-q', '--refresh', env=hermetic, check=False)
        (private / 'tmp').mkdir(exist_ok=True)
        env = dict(s['env'], TMPDIR=str(private / 'tmp'), PYTHONDONTWRITEBYTECODE='1')
        argv = s['argv']
        if s.get('profile'):
            (private / 'profile.sb').write_text(s['profile'])
            argv = ['sandbox-exec', '-f', str(private / 'profile.sb'), *argv]
        paths = tree_paths(dest)
        watch(dest, paths)
        code = subprocess.run(argv, cwd=dest, env=env).returncode
        reads = read_since(dest, paths)
        for log in sorted(f for pattern in s.get('logs', ()) for f in dest.glob(pattern)) if code else ():
            print('--- %s (tail; the tree is removed)' % log.relative_to(dest), flush=True)  # the logs it kept there
            sys.stdout.buffer.write(b'\n'.join(log.read_bytes().splitlines()[-40:]) + b'\n')
        # The record, at once: what the clones were cloned from is unchanged, so its digests of
        # the files the unit read there are those of what it read.
        record, reason = None, None
        if not s.get('profile'):
            reason = 'no sandbox applied'
        elif clone_state(root, s['clone']) != before:
            reason = "the checkout's Lake builds or generated files changed during the run"
        elif code == 0:
            record = Records(root, s['commit']).record(reads, s.get('outputs', ()))
        if code == 0:
            for rel in s.get('outputs', ()):
                if (dest / rel).is_file():
                    (root / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(dest / rel, root / rel)
        Path(s['trace']).write_text(json.dumps({'reads': reads, 'record': record, 'reason': reason}))
        return code
    finally:
        shutil.rmtree(dest, ignore_errors=True)


class Records:
    """Traced records over one state of ROOT, the snapshot COMMIT (docs/ci.md#traced-records): the
    record of a pass, whether one matches, and their store (scripts/cas.py's, kind `ci-reuse`,
    entries `<pre-key>.<record digest>`)."""

    def __init__(self, root, commit):
        self.root, self.commit = Path(root), commit
        self.tree = tracked_tree(root, commit)
        self.cloned = cloned_entries(root)
        self.children = {}
        for path in [*self.tree, *self.cloned]:
            parts = path.split('/')
            for i in range(len(parts)):
                self.children.setdefault('/'.join(parts[:i]), set()).add(parts[i])
        self.digests, self.store = {}, local_store()

    def digest(self, path):
        """'mode:object id' of a file as a traced tree shows it (tracked or new: the snapshot's; in
        a clone: the checkout's file now), None when absent; of a directory `DIR/`, the digest of
        its entries' names."""
        if path not in self.digests:
            if path.endswith('/'):
                names = self.names('' if path == './' else path[:-1])
                value = None if names is None else sha256('\0'.join(names))
            elif path in self.tree:
                value = '%s:%s' % self.tree[path]
            else:
                value = file_id(self.root / path) if self.in_clone(path) else None
            self.digests[path] = value
        return self.digests[path]

    def in_clone(self, path):
        return any(path == c or path.startswith(c + '/') for c in self.cloned)

    def names(self, directory):
        """The entries of DIRECTORY in a traced tree: the snapshot's and the clones' (inside a
        cloned build, the directory's own but tool caches); None when there is no such directory."""
        if self.in_clone(directory):
            path = self.root / directory
            return sorted(set(os.listdir(path)) - NOISE) if path.is_dir() and not path.is_symlink() else None
        names = self.children.get(directory)
        return None if names is None else sorted(names)

    def record(self, reads, outputs=()):
        """The record of a pass that read READS (relative paths; a listed directory `DIR/`) and
        wrote OUTPUTS: {path: digest} of every input it covers (docs/ci.md#traced-records)."""
        files = {p for p in reads if not p.endswith('/') and p not in outputs}
        # The names in every directory a probe could have looked in (a stat of an absent path moves
        # no access time): each directory it listed and each ancestor of a file it read, up to the
        # top; and, for a module it loaded from a Lake build, the same directories in every build
        # (Lean's search path probed them in order).
        listed = {p for p in reads if p.endswith('/')}
        builds = [c for c in self.cloned if c.endswith('.lake/build')]
        for f in files:
            listed |= {'%s/' % d if str(d) != '.' else './' for d in Path(f).parents}
            if (i := ('/' + f).find('/.lake/build/lib/lean/')) >= 0:
                module = Path(f[i + len('.lake/build/lib/lean/'):])
                listed |= {'%s/lib/lean/%s' % (b, '' if str(d) == '.' else str(d) + '/') for b in builds
                           for d in module.parents}
        # A read through a symlink touches its target only, and git applies the attributes while
        # it checks the tree out, before any access is watched: the tracked links and attribute
        # files are inputs too.
        fixed = {p for p, (mode, _) in self.tree.items() if mode == '120000' or Path(p).name == '.gitattributes'}
        return {p: self.digest(p) for p in sorted(files | listed | fixed)}

    def matches(self, record):
        return all(self.digest(p) == d for p, d in record.items())

    def prekey(self, outside, unit):
        """The pre-key of a unit (UNIT: what the caller runs, as a JSON value): with the caller's
        keyed environment, the identities outside the checkout and this machinery."""
        return key_of({'schema': TRACE_SCHEMA, 'machinery': MACHINERY_KEY, 'unit': unit,
                       'environment': outside.environment()[1], 'outside': outside.identity(),
                       'host': [platform.system(), platform.machine()]})

    def entries(self, prekey):
        """The published records under PREKEY, newest first."""
        found = [p for p in (self.store.path / LOCAL_KIND).glob(prekey + '.*')
                 if (p / GENERATED.CAS.MARKER).is_file() and (p / 'record.json').is_file()]
        return sorted(found, key=lambda p: (p / GENERATED.CAS.USED).stat().st_mtime
                      if (p / GENERATED.CAS.USED).exists() else 0, reverse=True)

    def lookup(self, prekey):
        """The entry of a record under PREKEY that matches the checkout (marked used), or None."""
        for entry in self.entries(prekey):
            if self.matches(json.loads((entry / 'record.json').read_text())):
                return self.store.lookup(LOCAL_KIND, entry.name)
        return None

    def changed(self, prekey):
        """The paths whose digest differs from the newest record under PREKEY (None: no record)."""
        found = self.entries(prekey)
        if not found:
            return None
        return sorted(p for p, d in json.loads((found[0] / 'record.json').read_text()).items() if self.digest(p) != d)

    def publish(self, prekey, record, body, outputs=(), keep=8):
        """Store RECORD (trace()'s of a pass) under PREKEY, with the OUTPUTS the pass wrote (their
        current content); keep the newest KEEP records of the pre-key."""
        text = canonical(record)
        name = '%s.%s' % (prekey, sha256(text)[:32])
        staged = self.store.stage(LOCAL_KIND, name)
        (staged / 'record.json').write_text(text)
        for rel in outputs:
            if (self.root / rel).is_file():
                (staged / 'files' / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(self.root / rel, staged / 'files' / rel)
        self.store.publish(staged, LOCAL_KIND, name, dict(body, prekey=prekey))
        for old in self.entries(prekey)[keep:]:
            grave = self.store.stage('withdrawn', old.name)
            with contextlib.suppress(FileNotFoundError):
                os.rename(old, grave / 'entry')
            shutil.rmtree(grave, ignore_errors=True)
        return name

# ---- key-relevant: end


def _machinery_key():
    text = Path(__file__).read_text()
    return sha256(text[text.index('# ---- key-relevant: begin'):text.index('# ---- key-relevant: end')])


MACHINERY_KEY = _machinery_key()


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
    if withheld:  # git then never stats or reads them
        git(root, 'update-index', '--skip-worktree', '-z', '--stdin',
            input=''.join(p + '\0' for p in withheld).encode('utf-8', 'surrogateescape'))
    watch(root, withheld)
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
        read = read_since(root, [rel for rel in state['withheld'] if os.path.isfile(Path(root, rel))
                                 and not os.path.islink(Path(root, rel))])
        if reset:  # the next check reports only what later steps read
            watch(root, read)
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
    p = sub.add_parser('trace')
    p.add_argument('spec', type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == 'trace':
            return trace(args.spec)
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
