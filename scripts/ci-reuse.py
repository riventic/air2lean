#!/usr/bin/env python3
"""CI result reuse: input keys, traced observations, coverage and records (docs/ci.md).

  ci-reuse.py key --part ID [--manifest F]      the input key of a part at HEAD (--manifest: its preimage)
  ci-reuse.py decide --job JOB --row JSON       (CI step) reuse a recorded result or arm the tracer
  ci-reuse.py reduce --workspace DIR --out F    (scripts/ci-trace.sh) strace stream on stdin -> observations
  ci-reuse.py check-trace [--part ID] [DIR]     every traced observation lies in the part's declared inputs
  ci-reuse.py record --out F                    (CI step) the record a passing execution uploads
  ci-reuse.py check-workflow                    every part is declared; every step after the decision is guarded
  ci-reuse.py suggest --part ID DIR             declaration patterns that would cover a trace

A *part* is one CI job row: `test/<zig>/<part>[/<shard>]`, `macos/<zig>`, or a matrix-free job
name. .github/ci-inputs.json declares each part's inputs (content patterns, listed directories,
whether it lists all tracked names) or `"commit_bound": true` (its key is the tested commit) or
`"reuse": false` (always runs). The key hashes the declared inputs at HEAD, the part's job
definition (its own matrix row only) and the jobs it needs, every hashFiles() pattern of those
jobs, the reuse machinery and the runner image. A record is the artifact `ci-reuse-<key>` of a
passing execution whose syscall trace showed no observation outside the declared inputs. Offline
except `decide` (GitHub REST API, with GH_TOKEN); stdlib only.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 'air2lean-ci-reuse/1'
DECLARATIONS = '.github/ci-inputs.json'
WORKFLOW = '.github/workflows/ci.yml'
WORKFLOW_NAME = 'CI'
MACHINERY = ('scripts/ci-reuse.py', 'scripts/ci-trace.sh', DECLARATIONS)
# Jobs that are not parts: they build what the parts consume, or aggregate results.
SUPPORT_JOBS = ('lake', 'zig-air', 'preflight', 'all-checks')
DECISION_STEP = 'Reuse a recorded result'
COVERAGE_STEP = 'Declared inputs cover every observation'
RECORD_STEPS = (COVERAGE_STEP, 'Record the result for reuse')  # the only untraced steps after the decision
GUARD = '!env.AIR2LEAN_REUSED'
# A `github.*` value inside an expression other than the workspace path differs per run.
RUN_SPECIFIC = re.compile(r'\$\{\{[^}]*\bgithub\.(?!workspace\b)')
# Producer events whose records a pull_request run may reuse (never a fork: see lookup()).
RECORD_EVENTS = ('pull_request', 'merge_group', 'workflow_dispatch')
DECLARATION_KEYS = {'reuse', 'inputs', 'listings', 'tree_names', 'commit_bound', 'note'}

_spec = importlib.util.spec_from_file_location('air2lean_release_record', ROOT / 'scripts/release-record.py')
RR = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(RR)
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


def git(root, *args):
    result = subprocess.run(['git', '-C', str(root), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ReuseError('git %s: %s' % (' '.join(args), result.stderr.decode(errors='replace').strip()))
    return result.stdout


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
    """A part's declared inputs: content patterns, listed directories, all tracked names."""

    def __init__(self, patterns, listings=(), tree_names=False):
        self.patterns = sorted(set(patterns))
        self.regexes = [glob_regex(p) for p in self.patterns]
        self.listings = sorted({d.strip('/') if d not in ('', '.', '/') else '' for d in listings})
        self.tree_names = tree_names

    def content(self, path):
        return any(r.fullmatch(path) for r in self.regexes)

    def subtree(self, directory):
        """Every path below `directory` is content (a `d/**` pattern at or above it, or `**`)."""
        probe = (directory + '/' if directory else '') + '\0any/\0path'
        return any(r.fullmatch(probe) for r in self.regexes)

    def listing(self, directory):
        return self.tree_names or directory in self.listings or self.subtree(directory)


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


# --- The workflow, its parts and their declarations. ---

def load_workflow(root):
    return RR.parse_workflow_yaml((Path(root) / WORKFLOW).read_text(encoding='utf-8'))


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


def load_declarations(root):
    data = json.loads((Path(root) / DECLARATIONS).read_text(encoding='utf-8'))
    if data.get('schema') != 'air2lean-ci-inputs/1':
        raise ReuseError('%s: unknown schema %r' % (DECLARATIONS, data.get('schema')))
    return data


def declaration(data, part):
    entry = (data.get('parts') or {}).get(part)
    if entry is None:
        raise ReuseError('%s declares no part %r' % (DECLARATIONS, part))
    unknown = set(entry) - DECLARATION_KEYS
    if unknown:
        raise ReuseError('%s: part %r has unknown keys %s' % (DECLARATIONS, part, ', '.join(sorted(unknown))))
    return entry


def part_inputs(data, entry, hashfiles=()):
    defaults = data.get('defaults') or {}
    return Inputs(list(defaults.get('inputs', [])) + list(entry.get('inputs', [])) + list(MACHINERY) + list(hashfiles),
                  list(defaults.get('listings', [])) + list(entry.get('listings', [])),
                  bool(entry.get('tree_names')))


def may_run(step, context):
    """False only when the step's `if` is false for this row in every executing run: it reads
    nothing but the row, the runner OS and the reuse decision (`env.AIR2LEAN_REUSED` is empty in
    an executing run). A status function, another step's output or any other context: True."""
    condition = step.get('if', True)
    if isinstance(condition, bool):
        return condition
    if re.search(r'\w\s*\(', condition):
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
        context = {'matrix': row, 'runner.os': 'macOS' if str(job.get('runs-on', '')).startswith('macos') else 'Linux'}
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


def tree_dirs(tree):
    dirs = {''}
    for path in tree:
        parts_ = path.split('/')[:-1]
        for i in range(1, len(parts_) + 1):
            dirs.add('/'.join(parts_[:i]))
    return dirs


def children(tree, directory):
    prefix = directory + '/' if directory else ''
    return sorted({p[len(prefix):].split('/', 1)[0] for p in tree if p.startswith(prefix)})


def runner_identity(environ=os.environ):
    return {key: environ.get(key, 'local') for key in ('ImageOS', 'ImageVersion', 'RUNNER_OS', 'RUNNER_ARCH')}


def manifest(root, part, environ=os.environ, revision='HEAD'):
    """The key preimage of `part` at `revision`; None for a part declared "reuse": false."""
    workflow = load_workflow(root)
    found = parts(workflow)
    if part not in found:
        raise ReuseError('%s has no part %r' % (WORKFLOW, part))
    data = load_declarations(root)
    entry = declaration(data, part)
    if entry.get('reuse') is False:
        return None
    job_id, row = found[part]
    jobs = workflow['jobs']
    needs = jobs[job_id].get('needs') or []
    needs = [needs] if isinstance(needs, str) else needs
    definitions = {'job': job_definition(jobs[job_id], row), 'needs': {n: jobs[n] for n in needs},
                   'workflow': {k: v for k, v in workflow.items() if k != 'jobs'}}
    hashfiles = sorted(hashfiles_patterns(canonical(definitions)))
    inputs = part_inputs(data, entry, hashfiles)
    tree = tracked_tree(root, revision)
    result = {
        'schema': SCHEMA, 'part': part, 'job_name': RR.job_name(job_id, row) if row else job_id,
        'definitions': definitions, 'runner': runner_identity(environ),
        'declaration': {'inputs': inputs.patterns, 'listings': inputs.listings, 'tree_names': inputs.tree_names},
        'content': sorted([path, *tree[path]] for path in tree if inputs.content(path)),
        'listings': {d: children(tree, d) for d in inputs.listings},
    }
    if inputs.tree_names:
        result['tree_names'] = sha256('\0'.join(sorted(tree)))
    if entry.get('commit_bound'):
        result['commit'] = git(root, 'rev-parse', '--verify', revision + '^{commit}').decode().strip()
    return result


def key_of(preimage):
    return sha256(canonical(preimage))


# --- Trace reduction: one strace stream -> the workspace observations of one step. ---

# (dirfd argument index or None, path argument index) of each path a syscall names.
PATH_ARGS = {
    'open': [(None, 0)], 'creat': [(None, 0)], 'openat': [(0, 1)], 'openat2': [(0, 1)],
    'stat': [(None, 0)], 'lstat': [(None, 0)], 'stat64': [(None, 0)], 'lstat64': [(None, 0)],
    'newfstatat': [(0, 1)], 'fstatat64': [(0, 1)], 'statx': [(0, 1)], 'statfs': [(None, 0)],
    'access': [(None, 0)], 'faccessat': [(0, 1)], 'faccessat2': [(0, 1)],
    'readlink': [(None, 0)], 'readlinkat': [(0, 1)], 'execve': [(None, 0)], 'execveat': [(0, 1)],
    'chdir': [(None, 0)], 'mkdir': [(None, 0)], 'mkdirat': [(0, 1)], 'rmdir': [(None, 0)],
    'unlink': [(None, 0)], 'unlinkat': [(0, 1)], 'rename': [(None, 0), (None, 1)],
    'renameat': [(0, 1), (2, 3)], 'renameat2': [(0, 1), (2, 3)], 'link': [(None, 0), (None, 1)],
    'linkat': [(0, 1), (2, 3)], 'symlink': [(None, 1)], 'symlinkat': [(1, 2)], 'truncate': [(None, 0)],
    'chmod': [(None, 0)], 'fchmodat': [(0, 1)], 'fchmodat2': [(0, 1)], 'chown': [(None, 0)],
    'lchown': [(None, 0)], 'fchownat': [(0, 1)], 'utime': [(None, 0)], 'utimes': [(None, 0)],
    'utimensat': [(0, 1)], 'futimesat': [(0, 1)], 'mknod': [(None, 0)], 'mknodat': [(0, 1)],
    'getxattr': [(None, 0)], 'lgetxattr': [(None, 0)], 'listxattr': [(None, 0)], 'llistxattr': [(None, 0)],
    'setxattr': [(None, 0)], 'lsetxattr': [(None, 0)], 'removexattr': [(None, 0)], 'lremovexattr': [(None, 0)],
    'inotify_add_watch': [(None, 1)], 'name_to_handle_at': [(0, 1)],
}
WRITES = {'creat', 'mkdir', 'mkdirat', 'rmdir', 'unlink', 'unlinkat', 'rename', 'renameat', 'renameat2',
          'link', 'linkat', 'symlink', 'symlinkat', 'truncate', 'chmod', 'fchmodat', 'fchmodat2', 'chown',
          'lchown', 'fchownat', 'utime', 'utimes', 'utimensat', 'futimesat', 'mknod', 'mknodat',
          'setxattr', 'lsetxattr', 'removexattr', 'lremovexattr'}
READS = {'execve', 'execveat', 'readlink', 'readlinkat', 'getxattr', 'lgetxattr', 'listxattr', 'llistxattr'}
LINE = re.compile(r'(\d+)\s+(.*)')
CALL = re.compile(r'([a-z_0-9]+)\((.*)\)\s+=\s+(.*)', re.S)
FD = re.compile(r'(AT_FDCWD|-?\d+)<(.*)>')
GIT_GLOBAL_WITH_VALUE = {'-C', '-c', '--git-dir', '--work-tree', '--namespace', '--exec-path', '--config-env'}
GIT_NAMES_FLAGS = {'-z', '--cached', '-c', '--others', '-o', '--exclude-standard', '--full-name', '--'}
GIT_NEUTRAL_REV_PARSE = {'--show-toplevel', '--git-dir', '--absolute-git-dir', '--is-inside-work-tree',
                         '--show-prefix', '--show-cdup', '--git-common-dir'}


def split_args(text):
    """Top-level comma-separated arguments of one strace call (quotes and brackets respected)."""
    args, depth, quote, start, i = [], 0, False, 0, 0
    while i < len(text):
        c = text[i]
        if quote:
            if c == '\\':
                i += 1
            elif c == '"':
                quote = False
        elif c == '"':
            quote = True
        elif c in '([{<':
            depth += 1
        elif c in ')]}>':
            depth -= 1
        elif c == ',' and depth == 0:
            args.append(text[start:i].strip())
            start = i + 1
        i += 1
    args.append(text[start:].strip())
    return args


def c_string(arg):
    """The value of a strace-quoted string argument, or None (NULL, a pointer, an elided string)."""
    m = re.fullmatch(r'"((?:[^"\\]|\\.)*)"(\.\.\.)?', arg, re.S)
    if not m or m.group(2):
        return None
    raw = m.group(1)
    out, i = bytearray(), 0
    while i < len(raw):
        if raw[i] == '\\' and i + 1 < len(raw):
            nxt = raw[i + 1]
            if nxt == 'x':
                out.append(int(raw[i + 2:i + 4], 16))
                i += 4
                continue
            if nxt in '01234567':
                digits = re.match(r'[0-7]{1,3}', raw[i + 1:]).group(0)
                out.append(int(digits, 8))
                i += 1 + len(digits)
                continue
            out += {'n': b'\n', 't': b'\t', 'r': b'\r', 'v': b'\v', 'f': b'\f'}.get(nxt, nxt.encode())
            i += 2
            continue
        out += raw[i].encode()
        i += 1
    return out.decode('utf-8', 'surrogateescape')


def git_class(argv):
    """What a git command observes of the checkout: none, names (tracked names), status, commit."""
    args, i = list(argv[1:]), 0
    while i < len(args) and args[i].startswith('-'):
        flag = args[i].split('=', 1)[0]
        i += 2 if flag in GIT_GLOBAL_WITH_VALUE and '=' not in args[i] else 1
    if i >= len(args):
        return 'none' if any(a in ('--version', '--exec-path') for a in args) else 'commit'
    command, rest = args[i], args[i + 1:]
    if command == 'version':
        return 'none'
    if command == 'status':
        return 'status'
    if command == 'ls-files':
        return 'names' if all(a in GIT_NAMES_FLAGS or not a.startswith('-') for a in rest) else 'commit'
    if command == 'rev-parse' and rest and all(a in GIT_NEUTRAL_REV_PARSE for a in rest):
        return 'none'
    if command == 'remote' and rest[:1] == ['get-url']:
        return 'none'
    # Content-addressed objects named by full ids (a ledger's reviewed revisions): what they read
    # depends only on the ids, which come from observed tracked files.
    positional = [a for a in rest if not a.startswith('-')]
    if command in ('fetch', 'show', 'cat-file', 'rev-parse') and positional and all(
            a == 'origin' or re.fullmatch(r'[0-9a-f]{40}(\^\{commit\}|:[^\0]*)?', a) for a in positional) \
            and any(a != 'origin' for a in positional):
        return 'none'
    return 'commit'


class Reducer:
    """Folds strace -f -y lines into {path: kinds}, git commands and unresolved paths."""

    def __init__(self, workspace):
        self.workspace = os.path.normpath(workspace)
        self.pending = {}         # pid -> text of an <unfinished ...> call
        self.cwd = {}             # pid -> last known working directory
        self.deferred = {}        # pid -> [(relative path, kind)] before its cwd is known
        self.exe = {}             # pid -> (executable, argv) of its image (last execve, else its parent's)
        self.inherited = {}       # pid -> [(path, kind)] before its clone returned: its parent's image
        self.parent = {}          # child pid -> parent pid
        self.clone_entry = {}     # pid -> its cwd when it entered an unfinished clone
        self.observed = {}        # workspace-relative path -> set of kinds
        self.git = {}             # canonical argv json -> class, for git commands touching .git
        self.gitdir_by_others = set()
        self.unresolved = []
        self.lines = 0

    # The relative path in the workspace, '' for the workspace itself, None outside.
    def relative(self, path):
        path = os.path.normpath(path)
        if path == self.workspace:
            return ''
        if path.startswith(self.workspace + '/'):
            return path[len(self.workspace) + 1:]
        return None

    def note(self, pid, path, kind):
        # A process or thread runs its parent's image until its own execve. Until the parent's
        # clone returns (strace may print the child first), that image is not known yet.
        if pid not in self.exe:
            self.inherited.setdefault(pid, []).append((path, kind))
            return
        self.attribute(self.exe[pid], path, kind)

    def attribute(self, image, path, kind):
        """One observation by a process running `image` ((executable, argv) or None: unknown)."""
        rel = self.relative(path)
        if rel is None:
            return
        argv = image[1] if image and (os.path.basename(image[0]) == 'git' or '/git-core/' in image[0]) else None
        if rel == '.git' or rel.startswith('.git/'):
            if argv is not None:
                self.git[canonical(argv)] = git_class(argv)
            else:
                self.gitdir_by_others.add(rel)
            return
        if argv is not None and git_class(argv) in ('status', 'names', 'none'):
            return  # modelled by the command (docs/ci.md): status reads what the traced writes changed
        self.observed.setdefault(rel, set()).add(kind)

    def resolve(self, pid, path, kind):
        if path.startswith('/'):
            self.note(pid, path, kind)
        elif pid in self.cwd:
            self.note(pid, os.path.join(self.cwd[pid], path), kind)
        else:
            self.deferred.setdefault(pid, []).append((path, kind))

    def learn_cwd(self, pid, cwd):
        self.cwd[pid] = cwd
        for path, kind in self.deferred.pop(pid, []):
            self.note(pid, os.path.join(cwd, path), kind)

    def feed(self, line):
        self.lines += 1
        m = LINE.match(line.rstrip('\n'))
        if not m:
            return
        pid, text = int(m.group(1)), m.group(2)
        if text.startswith(('---', '+++')):
            return
        if text.endswith('<unfinished ...>'):
            self.pending[pid] = text[:-len('<unfinished ...>')].rstrip()
            name = re.match(r'([a-z_0-9]+)\(', text)
            if name and name.group(1) in ('clone', 'clone3', 'fork', 'vfork') and pid in self.cwd:
                self.clone_entry[pid] = self.cwd[pid]
            return
        resumed = re.match(r'<\.\.\. ([a-z_0-9]+) resumed>(.*)', text, re.S)
        if resumed:
            text = self.pending.pop(pid, resumed.group(1) + '(') + resumed.group(2)
        self.call(pid, text)

    def call(self, pid, text):
        m = CALL.fullmatch(text.strip())
        if not m:
            return
        name, args, result = m.group(1), split_args(m.group(2)), m.group(3)
        failed = result.startswith('-1')
        for arg in args[:1]:
            fd = FD.match(arg)
            if fd and fd.group(1) == 'AT_FDCWD' and pid not in self.cwd:
                self.learn_cwd(pid, fd.group(2))
            elif fd and fd.group(1) == 'AT_FDCWD':
                self.cwd[pid] = fd.group(2)
        if name in ('clone', 'clone3', 'fork', 'vfork'):
            child = re.match(r'(\d+)', result)
            if child:
                child = int(child.group(1))
                self.parent[child] = pid
                cwd = self.clone_entry.pop(pid, self.cwd.get(pid))
                if cwd is not None and child not in self.cwd:
                    self.learn_cwd(child, cwd)
                # E.g. git's index-preload threads stat every tracked file as part of its command.
                image = self.exe.get(pid)
                self.exe.setdefault(child, image)
                for path, kind in self.inherited.pop(child, []):
                    self.attribute(image, path, kind)
            return
        if name == 'getcwd':
            return
        if name in ('getdents64', 'getdents'):
            fd = FD.match(args[0])
            if fd:
                self.note(pid, fd.group(2), 'list')
            return
        if name == 'fchdir':
            fd = FD.match(args[0])
            if fd and not failed:
                self.learn_cwd(pid, fd.group(2))
            return
        if name == 'execve' and not failed:
            path = c_string(args[0]) or ''
            argv = [c_string(a) or '' for a in split_args(args[1][1:-1])] if args[1:2] and args[1].startswith('[') else []
            if not path.startswith('/') and pid in self.cwd:
                path = os.path.join(self.cwd[pid], path)
            self.exe[pid] = (path, argv)
        specs = PATH_ARGS.get(name)
        if specs is None:
            # Any other %file call: every string naming a path counts as a write (the strictest kind).
            specs = [(None, i) for i, a in enumerate(args) if a.startswith('"')]
            kind = 'write'
        elif name in WRITES:
            kind = 'write'
        elif name in ('open', 'openat', 'openat2'):
            index = 1 if name == 'open' else 2
            flags = args[index] if len(args) > index else ''
            kind = 'write' if re.search(r'O_WRONLY|O_RDWR|O_CREAT|O_TRUNC|O_APPEND', flags) else \
                'probe' if 'O_DIRECTORY' in flags or failed else 'read'
            # A read-write open of an existing file can read its old content too.
            if 'O_RDWR' in flags and 'O_TRUNC' not in flags and not failed:
                fd = FD.match(result)
                if fd:
                    self.note(pid, fd.group(2), 'read')
        elif name in READS:
            kind = 'probe' if failed else 'read'
        else:
            kind = 'probe'
        for dirfd, index in specs:
            if index >= len(args):
                continue
            path = c_string(args[index])
            if path is None:
                continue
            if name == 'chdir' and not failed:
                base = self.cwd.get(pid)
                if path.startswith('/') or base is not None:
                    self.learn_cwd(pid, os.path.normpath(os.path.join(base or '/', path)))
            if dirfd is not None and not path.startswith('/'):
                fd = FD.match(args[dirfd])
                if fd:
                    self.note(pid, os.path.join(fd.group(2), path), kind)
                else:
                    self.unresolved.append('%s(%s) in pid %d' % (name, path, pid))
                continue
            self.resolve(pid, path, kind)
        if name in ('open', 'openat', 'openat2', 'creat') and not failed:
            fd = FD.match(result)
            if fd:  # the resolved path (through symlinks) of the opened file
                self.note(pid, fd.group(2), 'read' if kind == 'probe' else kind)

    def finish(self):
        for pid, items in self.deferred.items():
            base = self.cwd.get(self.parent.get(pid))
            for path, kind in items:
                if base is None:
                    self.unresolved.append('relative %s in pid %d with unknown cwd' % (path, pid))
                else:
                    self.note(pid, os.path.join(base, path), kind)
        self.deferred = {}
        for pid, items in self.inherited.items():  # a clone that never returned: image unknown
            for path, kind in items:
                self.attribute(None, path, kind)
        self.inherited = {}
        return {'complete': True, 'lines': self.lines,
                'observed': {p: sorted(k) for p, k in sorted(self.observed.items())},
                'git': {argv: cls for argv, cls in sorted(self.git.items())},
                'gitdir_by_others': sorted(self.gitdir_by_others), 'unresolved': self.unresolved}


# --- Coverage of observations by a declaration. ---

def deepest_tracked_dir(path, dirs):
    parent = str(PurePosixPath(path).parent) if '/' in path else ''
    while parent not in dirs:
        parent = str(PurePosixPath(parent).parent) if '/' in parent else ''
    return parent


def coverage(observations, inputs, tree, commit_bound=False, generated=()):
    """Violations: (path, kinds, what the declaration lacks) for every uncovered observation.

    `generated` are the whole-tree generated files (assurance/generated.json): untracked, but
    derived from the whole tree by the `generated` job, so only a whole-tree declaration covers them."""
    dirs = tree_dirs(tree)
    problems = []
    for step in observations:
        if not step.get('complete'):
            problems.append(('<step %s>' % step.get('step'), [], 'trace incomplete'))
            continue
        for path in step.get('unresolved', []):
            problems.append((path, [], 'path not resolvable to the workspace'))
        if not commit_bound:
            for argv, cls in step.get('git', {}).items():
                if cls == 'commit':
                    problems.append(('git ' + ' '.join(json.loads(argv)[1:]), [],
                                     'reads commit identity: declare "commit_bound": true'))
                elif cls == 'names' and not inputs.tree_names:
                    problems.append(('git ' + ' '.join(json.loads(argv)[1:]), [],
                                     'lists every tracked name: declare "tree_names": true'))
            for path in step.get('gitdir_by_others', []):
                problems.append((path, [], 'a non-git process reads .git: declare "commit_bound": true'))
        if commit_bound:
            continue
        for path, kinds in step.get('observed', {}).items():
            if path in tree:
                if not inputs.content(path):
                    problems.append((path, kinds, 'content not declared (add an inputs pattern)'))
            elif path in dirs:
                if 'list' in kinds and not inputs.listing(path):
                    problems.append((path, kinds, 'listing not declared (add it to listings)'))
                if 'write' in kinds and not inputs.subtree(path):
                    problems.append((path, kinds, 'tracked directory changed: declare %s/**' % path))
                if set(kinds) - {'list', 'write'}:
                    parent = str(PurePosixPath(path).parent) if '/' in path else ''
                    if path and not inputs.listing(parent):
                        problems.append((path, kinds, 'listing of %r not declared' % (parent or '.')))
            elif path in generated:
                # Installing one (`scripts/generated.py install` only writes it) reveals nothing.
                if set(kinds) - {'write'} and not inputs.subtree(''):
                    problems.append((path, kinds, 'whole-tree generated file (%s): declare "**"' % GENERATED.REGISTRY))
            else:
                anchor = deepest_tracked_dir(path, dirs)
                if not inputs.listing(anchor):
                    problems.append((path, kinds, 'untracked path: listing of %r not declared' % (anchor or '.')))
    return sorted({(p, tuple(k), w) for p, k, w in problems})


def read_traces(directory):
    directory = Path(directory)
    steps = []
    for started in sorted(directory.glob('*.started')):
        step = started.stem
        reduced = directory / (step + '.json')
        data = json.loads(reduced.read_text()) if reduced.is_file() else {'complete': False}
        data['step'] = step
        steps.append(data)
    return steps


def suggest(observations, tree):
    """A declaration covering a trace: content patterns (`dir/**` per observed file's directory,
    and per written tracked directory), listings, and `tree_names` when git listed every name."""
    dirs, patterns, listings, names = tree_dirs(tree), set(), set(), False
    for step in observations:
        names = names or 'names' in step.get('git', {}).values()
        for path, kinds in step.get('observed', {}).items():
            if path in tree:
                parent = str(PurePosixPath(path).parent) if '/' in path else ''
                patterns.add(parent + '/**' if parent else path)
            elif path in dirs:
                if 'list' in kinds:
                    listings.add(path or '.')
                if 'write' in kinds:
                    patterns.add(path + '/**' if path else '**')
                if set(kinds) - {'list'} and path:
                    parent = str(PurePosixPath(path).parent) if '/' in path else ''
                    listings.add(parent or '.')
            else:
                listings.add(deepest_tracked_dir(path, dirs) or '.')
    collapsed = {p for p in patterns if not any(
        q != p and q.endswith('/**') and p.startswith(q[:-2]) for q in patterns)}
    declaration = {'inputs': sorted(collapsed), 'listings': sorted(listings)}
    return {**declaration, 'tree_names': True} if names else declaration


# --- Workflow checks: declarations complete, steps guarded, no run-specific expressions. ---

def check_workflow(root):
    workflow = load_workflow(root)
    data = load_declarations(root)
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
    for job_id in sorted({job for job, _ in found.values()}):
        steps = workflow['jobs'][job_id].get('steps') or []
        names = [s.get('name') for s in steps]
        if DECISION_STEP not in names:
            errors.append('job %s has no %r step' % (job_id, DECISION_STEP))
            continue
        start = names.index(DECISION_STEP)
        traced = workflow['jobs'][job_id].get('defaults', {}).get('run', {}).get('shell') == 'bash scripts/ci-trace.sh {0}'
        if str(workflow['jobs'][job_id].get('runs-on', '')).startswith('ubuntu') and not traced:
            errors.append('job %s runs on Linux without the traced shell (defaults.run.shell)' % job_id)
        if traced and COVERAGE_STEP not in names:
            errors.append('traced job %s has no %r step' % (job_id, COVERAGE_STEP))
        end = names.index(COVERAGE_STEP) if COVERAGE_STEP in names else len(steps)
        for index, step in enumerate(steps[start + 1:], start + 1):
            condition = str(step.get('if', ''))
            if GUARD not in condition:
                errors.append('job %s step %r runs after %r without %s in its if'
                              % (job_id, step.get('name'), DECISION_STEP, GUARD))
            elif '||' in condition and not all(GUARD in d for d in condition.split('||')):
                errors.append('job %s step %r: every || branch of its if needs %s' % (job_id, step.get('name'), GUARD))
            if 'AIR2LEAN_UNTRACED' in canonical(step) and step.get('name') not in RECORD_STEPS:
                errors.append('job %s step %r opts out of the tracer' % (job_id, step.get('name')))
            if 'shell' in step:
                errors.append('job %s step %r sets its own shell (it would escape the tracer)' % (job_id, step.get('name')))
            if start < index < end and RUN_SPECIFIC.search(canonical(step)):
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


def lookup(key, job_name, repository, token, fetch=api):
    """The newest acceptable record of `key`: (run id, run URL, job id) or None.

    Accepted only from this repository's CI workflow (never a fork's head repository), from a
    RECORD_EVENTS run, whose job `job_name` completed with success, per the GitHub API.
    """
    listed = fetch('/repos/%s/actions/artifacts?name=ci-reuse-%s&per_page=30' % (repository, key), token)
    for artifact in sorted(listed.get('artifacts', []), key=lambda a: a.get('created_at', ''), reverse=True):
        source = artifact.get('workflow_run') or {}
        if artifact.get('expired') or artifact.get('name') != 'ci-reuse-' + key:
            continue
        if source.get('head_repository_id') != source.get('repository_id') or not source.get('id'):
            continue
        run = fetch('/repos/%s/actions/runs/%d' % (repository, source['id']), token)
        if (run.get('path') != WORKFLOW or run.get('name') != WORKFLOW_NAME or run.get('event') not in RECORD_EVENTS
                or (run.get('head_repository') or {}).get('full_name') != repository):
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
        print('%s: not a GitHub Actions run: every step runs untraced, no record' % part)
        return 0
    env_file, summary = environ.get('GITHUB_ENV'), environ.get('GITHUB_STEP_SUMMARY')
    data = load_declarations(root)
    entry = declaration(data, part)
    preimage = manifest(root, part, environ)
    event = environ.get('AIR2LEAN_EVENT', '')
    if preimage is None:
        append(summary, '**%s** always runs (`"reuse": false` in %s).\n' % (part, DECLARATIONS))
        return 0
    key = key_of(preimage)
    out = Path(environ['RUNNER_TEMP']) / 'ci-reuse'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'manifest.json').write_text(canonical(preimage))
    lines = ['AIR2LEAN_PART=' + part, 'AIR2LEAN_REUSE_KEY=' + key]
    message = '**%s** input key `%s`' % (part, key)
    if event == 'pull_request':
        found = None
        try:
            found = lookup(key, preimage['job_name'], environ['GITHUB_REPOSITORY'], environ.get('GH_TOKEN', ''), fetch)
        except (urllib.error.URLError, OSError, ValueError, KeyError) as error:
            print('record lookup failed (%s): the part runs' % error)
        chosen = self_check_part(environ, [p for p in parts(load_workflow(root))
                                           if (data['parts'].get(p) or {}).get('reuse') is not False])
        if found and part != chosen:
            run_id, run_url, job_id_, job_url = found
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
    traced = environ.get('RUNNER_OS') == 'Linux' and not entry.get('commit_bound')
    if event in RECORD_EVENTS and (traced or entry.get('commit_bound')):
        lines.append('AIR2LEAN_RECORD=1')
    if traced:
        if not shutil.which('strace'):
            subprocess.run(['sudo', 'apt-get', 'install', '-y', '--no-install-recommends', 'strace'], check=False)
            if not shutil.which('strace'):
                subprocess.run(['sudo', 'apt-get', 'update', '-q'], check=True)
                subprocess.run(['sudo', 'apt-get', 'install', '-y', '--no-install-recommends', 'strace'], check=True)
        traces = out / 'traces'
        traces.mkdir(exist_ok=True)
        lines += ['AIR2LEAN_TRACE_DIR=%s' % traces, 'AIR2LEAN_REUSE_TOOL=%s' % (Path(root).resolve() / 'scripts/ci-reuse.py')]
    append(env_file, '\n'.join(lines) + '\n')
    append(summary, message + ('; traced' if traced else '') + '.\n')
    print(message)
    return 0


def check_trace(root, part, directory, environ=os.environ):
    if not directory:
        print('untraced run: nothing to check, no record will be written')
        return 0
    data = load_declarations(root)
    entry = declaration(data, part)
    preimage = manifest(root, part, environ)
    if preimage is None:
        print('%s always runs: nothing to check' % part)
        return 0
    inputs = part_inputs(data, entry, hashfiles_patterns(canonical(preimage['definitions'])))
    steps = read_traces(directory)
    problems = coverage(steps, inputs, tracked_tree(root), bool(entry.get('commit_bound')), GENERATED.paths(root))
    observed = sum(len(s.get('observed', {})) for s in steps)
    Path(directory, 'coverage.json').write_text(canonical(
        {'part': part, 'steps': len(steps), 'observed': observed, 'problems': problems}))
    if problems:
        print('error: %s observed %d path(s) outside its declared inputs (%s); fix the declaration '
              'or the step:' % (part, len(problems), DECLARATIONS), file=sys.stderr)
        for path, kinds, what in problems[:200]:
            print('  %s [%s]: %s' % (path, ','.join(kinds), what), file=sys.stderr)
        print('suggested declaration: %s' % canonical(suggest(steps, tracked_tree(root))), file=sys.stderr)
        return 1
    print('OK: %d traced steps of %s, %d workspace paths observed, all inside the declared inputs'
          % (len(steps), part, observed))
    return 0


def record(root, out, environ=os.environ):
    part, key = environ.get('AIR2LEAN_PART'), environ.get('AIR2LEAN_REUSE_KEY')
    if not part or not key:
        raise ReuseError('no part or key in the environment: the decision step did not arm a record')
    preimage = manifest(root, part, environ)
    if key_of(preimage) != key:
        raise ReuseError('the inputs of %s changed during the run; no record' % part)
    trace_dir = environ.get('AIR2LEAN_TRACE_DIR')
    coverage_file = Path(trace_dir, 'coverage.json') if trace_dir else None
    if trace_dir and not coverage_file.is_file():
        raise ReuseError('traced run without a coverage check; no record')
    body = {'schema': SCHEMA, 'key': key, 'part': part, 'job_name': preimage['job_name'],
            'run_id': environ.get('GITHUB_RUN_ID'), 'run_attempt': environ.get('GITHUB_RUN_ATTEMPT'),
            'event': environ.get('AIR2LEAN_EVENT'), 'tested_commit': git(root, 'rev-parse', 'HEAD').decode().strip(),
            'coverage': json.loads(coverage_file.read_text()) if coverage_file else None, 'manifest': preimage}
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
    p = sub.add_parser('reduce')
    p.add_argument('--workspace', required=True)
    p.add_argument('--out', type=Path, required=True)
    p = sub.add_parser('check-trace')
    p.add_argument('--part', default=os.environ.get('AIR2LEAN_PART'))
    p.add_argument('directory', nargs='?', default=os.environ.get('AIR2LEAN_TRACE_DIR'))
    p = sub.add_parser('record')
    p.add_argument('--out', type=Path, required=True)
    sub.add_parser('check-workflow')
    p = sub.add_parser('suggest')
    p.add_argument('--part', required=True)
    p.add_argument('directory', type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == 'reduce':
            reducer = Reducer(args.workspace)
            for line in sys.stdin.buffer:
                reducer.feed(line.decode('utf-8', 'surrogateescape'))
            temp = args.out.with_suffix('.part')
            temp.write_text(canonical(reducer.finish()))
            temp.replace(args.out)
            return 0
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
        if args.command == 'check-trace':
            return check_trace(args.root, args.part, args.directory)
        if args.command == 'record':
            return record(args.root, args.out)
        if args.command == 'check-workflow':
            errors = check_workflow(args.root)
            for error in errors:
                print('error: ' + error, file=sys.stderr)
            if not errors:
                print('OK: every part of %s is declared and every step after the reuse decision is guarded' % WORKFLOW)
            return 1 if errors else 0
        if args.command == 'suggest':
            print(json.dumps(suggest(read_traces(args.directory), tracked_tree(args.root)), indent=2))
            return 0
    except (ReuseError, RR.ReleaseError, OSError, ValueError) as error:
        print('error: %s' % error, file=sys.stderr)
        return 2
    return 2


if __name__ == '__main__':
    sys.exit(main())
