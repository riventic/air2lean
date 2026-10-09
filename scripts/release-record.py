#!/usr/bin/env python3
"""Revision-bound release record: CI gates, their evidence, unavailable checks and the review ledger.

  release-record.py plan   [--root DIR] [--json]          list the release gates of HEAD's workflow
  release-record.py record [--root DIR] [--github-run F]... [--local-ci DIR]...
                           [--unavailable 'JOB[::STEP]=REASON']... [--out F]
  release-record.py verify RECORD [--root DIR]            re-check a published record against its revision
  release-record.py ledger [--root DIR] [--allow-unfetched | --revisions]

The profile is the CI matrix of .github/workflows/ci.yml at the recorded revision; every matrix
row is one job and every `run:` step whose condition holds for that row is a gate (actions and the
tool-setup recipes that scripts/local-ci.sh substitutes are not gates); the matrix-free `macos`
and `aarch64-linux` jobs are native-runner jobs that only GitHub evidence covers. `record` requires a clean
checkout and binds to HEAD. A gate is passed only with evidence for that exact commit: GitHub
Actions run JSON (`gh run view ID --json databaseId,headSha,headBranch,conclusion,status,event,
workflowName,url,jobs`) or a scripts/local-ci.sh results directory. Gates without evidence are
missing unless declared unavailable with a reason; a failure can never be declared unavailable.
`ledger` checks that every REVIEW_COVERAGE.tsv entry names its reviewed revision and that the
recorded baseline hash is the file's content at that revision. No builds or network access.
"""
import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SCHEMA = 'air2lean-release-record/1'
WORKFLOW = '.github/workflows/ci.yml'
STEPS_SCRIPT = 'scripts/local-ci-steps.py'
LEDGER = 'REVIEW_COVERAGE.tsv'
LEDGER_HEADER = ['path', 'reviewer', 'method', 'baseline_sha256', 'reviewed_revision']
SHA1 = re.compile(r'[0-9a-f]{40}')
SHA256 = re.compile(r'[0-9a-f]{64}')
GATE_STATUSES = ('passed', 'failed', 'missing', 'unavailable')


class ReleaseError(Exception):
    pass


def git(root, *args, data=None):
    result = subprocess.run(['git', '-C', str(root), *args], input=data, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    if result.returncode:
        raise ReleaseError('git %s: %s' % (' '.join(args), result.stderr.decode(errors='replace').strip()))
    return result.stdout


def git_text(root, *args):
    return git(root, *args).decode().strip()


def show(root, revision, path):
    return git(root, 'show', '%s:%s' % (revision, path)).decode()


def clean_head(root):
    """HEAD of a checkout without tracked changes or untracked files; otherwise ReleaseError."""
    revision = git_text(root, 'rev-parse', '--verify', 'HEAD^{commit}')
    changes = git(root, 'status', '--porcelain=v1', '--untracked-files=all', '-z').decode()
    if changes:
        paths = sorted({item[3:] for item in changes.split('\0') if len(item) > 3})
        raise ReleaseError('dirty tree at %s; a release record binds only a clean revision: %s'
                           % (revision, ', '.join(paths[:10]) + (' ...' if len(paths) > 10 else '')))
    return revision


# --- Workflow subset parser: block mappings/sequences, plain/quoted scalars, `|` blocks. ---

def _scalar(text, where):
    text = text.strip()
    if text[:1] in ('"', "'"):
        end = text.find(text[0], 1)
        rest = text[end + 1:].strip() if end > 0 else '?'
        if end < 0 or (rest and not rest.startswith('#')) or (text[0] == '"' and '\\' in text[1:end]):
            raise ReleaseError('%s: unsupported quoted scalar' % where)
        return text[1:end]
    # `|` here is a block scalar with a comment, indentation or keep indicator: unsupported.
    if text[:1] in ('&', '*', '!', '>', '|', '{', '%', '@', '`'):
        raise ReleaseError('%s: unsupported YAML syntax %r' % (where, text))
    if text.startswith('['):
        if not text.endswith(']'):
            raise ReleaseError('%s: unsupported flow sequence' % where)
        return [_scalar(item, where) for item in text[1:-1].split(',') if item.strip()]
    text = re.sub(r'\s+#.*$', '', text)
    if text in ('true', 'false'):
        return text == 'true'
    if re.fullmatch(r'-?[0-9]+', text):
        return int(text)
    return text


def parse_workflow_yaml(text):
    lines = text.split('\n')
    pos = 0

    def indent(line):
        return len(line) - len(line.lstrip(' '))

    def skip():
        nonlocal pos
        while pos < len(lines) and (not lines[pos].strip() or lines[pos].lstrip().startswith('#')):
            pos += 1

    def node(level):
        skip()
        if pos >= len(lines) or indent(lines[pos]) != level:
            raise ReleaseError('%s:%d: unexpected indentation' % (WORKFLOW, pos + 1))
        if '\t' in lines[pos][:level + 1]:
            raise ReleaseError('%s:%d: tab indentation' % (WORKFLOW, pos + 1))
        body = lines[pos][level:]
        return sequence(level) if body == '-' or body.startswith('- ') else mapping(level)

    def sequence(level):
        nonlocal pos
        items = []
        while True:
            skip()
            if pos >= len(lines) or indent(lines[pos]) < level:
                return items
            body = lines[pos][level:]
            if indent(lines[pos]) != level or not body.startswith('- '):
                raise ReleaseError('%s:%d: unsupported sequence entry' % (WORKFLOW, pos + 1))
            lines[pos] = ' ' * (level + 2) + body[2:]
            items.append(node(level + 2))

    def mapping(level):
        nonlocal pos
        result = {}
        while True:
            skip()
            if pos >= len(lines) or indent(lines[pos]) < level:
                return result
            where = '%s:%d' % (WORKFLOW, pos + 1)
            match = re.fullmatch(r'([A-Za-z0-9_.-]+):(?:[ ]+(.*))?', lines[pos][level:])
            if indent(lines[pos]) != level or not match:
                raise ReleaseError('%s: unsupported mapping entry' % where)
            key, value = match[1], (match[2] or '').strip()
            if key in result:
                raise ReleaseError('%s: duplicate key %s' % (where, key))
            pos += 1
            if value in ('|', '|-'):
                result[key] = block(level, value == '|-')
            elif not value or value.startswith('#'):
                skip()
                deeper = pos < len(lines) and indent(lines[pos]) > level
                result[key] = node(indent(lines[pos])) if deeper else None
            else:
                result[key] = _scalar(value, where)

    def block(level, strip):
        nonlocal pos
        content = []
        width = None
        while pos < len(lines):
            line = lines[pos]
            if line.strip():
                if indent(line) <= level:
                    break
                width = indent(line) if width is None else width
                if indent(line) < width:
                    raise ReleaseError('%s:%d: under-indented block scalar' % (WORKFLOW, pos + 1))
                content.append(line[width:])
            else:
                content.append('')
            pos += 1
        text = '\n'.join(content).rstrip('\n')
        return text if strip or not text else text + '\n'

    result = node(0)
    skip()
    if pos != len(lines):
        raise ReleaseError('%s:%d: trailing content' % (WORKFLOW, pos + 1))
    return result


# --- Profile and gate plan, all read from Git objects at one revision. ---

def local_ci_helpers(source):
    """The local runner's condition evaluator and substituted setup step names."""
    tree = ast.parse(source)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'expression']
    setups = [n.value for n in tree.body if isinstance(n, ast.Assign) and isinstance(n.value, ast.Dict)
              and [getattr(t, 'id', None) for t in n.targets] == ['setup']]
    if len(functions) != 1 or len(setups) != 1:
        raise ReleaseError('%s: expression() or the setup recipe table changed' % STEPS_SCRIPT)
    namespace = {'re': re}
    exec(compile(ast.Module(body=functions, type_ignores=[]), STEPS_SCRIPT, 'exec'), namespace)
    return namespace['expression'], {ast.literal_eval(key) for key in setups[0].keys}


def job_name(job_id, row):
    """GitHub's default matrix job name: non-empty matrix values in order."""
    values = [str(v).lower() if isinstance(v, bool) else str(v) for v in row.values() if v != '']
    return '%s (%s)' % (job_id, ', '.join(values))


def reproduce(row):
    if row.get('mutate'):
        return 'scripts/local-ci.sh mutations'
    return 'scripts/local-ci.sh full %s' % row['zig']


MACOS_REPRODUCE = 'GitHub Actions macos-14 runner only; scripts/local-ci.sh runs the Linux test job'
# Matrix-free jobs on native runners that scripts/local-ci.sh cannot reproduce: Q05 `macos` and
# T04 `aarch64-linux` (ubuntu-24.04-arm).
NATIVE_JOBS = {
    'macos': MACOS_REPRODUCE,
    'aarch64-linux': 'GitHub Actions ubuntu-24.04-arm runner only; scripts/local-ci.sh runs the x86_64 test job',
}


def native_plan(name, job, commands):
    """A matrix-free native job (`NATIVE_JOBS`): GitHub names it `name`; only GitHub evidence covers it.

    Its commands are keyed `<name>::<step>` (step names may repeat the test job's). A step whose
    condition reads another step's outputs (a cache hit) is tool setup, not a gate.
    """
    if job.get('strategy') is not None:
        raise ReleaseError('%s: the %s job must not have a matrix' % (WORKFLOW, name))
    steps = job.get('steps') or []
    names = [step.get('name') for step in steps]
    if None in names or len(set(names)) != len(names):
        raise ReleaseError('%s: every %s step needs a unique name' % (WORKFLOW, name))
    gates = []
    for step in steps:
        if 'run' not in step:
            continue
        condition = step.get('if', True)
        if not isinstance(condition, bool) and 'steps.' in str(condition):
            continue
        if condition is not True:
            raise ReleaseError('%s: %s step %r: unsupported condition %r' % (WORKFLOW, name, step['name'], condition))
        commands[name + '::' + step['name']] = {key: step[key] for key in ('env', 'run') if key in step}
        gates.append(step['name'])
    return {'name': name, 'matrix': None, 'reproduce': NATIVE_JOBS[name], 'gates': gates, 'not_applicable': []}


def build_plan(root, revision):
    workflow = parse_workflow_yaml(show(root, revision, WORKFLOW))
    expression, setup = local_ci_helpers(show(root, revision, STEPS_SCRIPT))
    jobs = workflow.get('jobs') or {}
    if set(jobs) - set(NATIVE_JOBS) != {'test'}:
        raise ReleaseError('%s: only the test, macos and aarch64-linux jobs are qualified for release records'
                           % WORKFLOW)
    job = jobs['test']
    rows = (((job.get('strategy') or {}).get('matrix') or {}).get('include')) or []
    steps = job.get('steps') or []
    names = [step.get('name') for step in steps]
    if not rows or any(not isinstance(row, dict) for row in rows):
        raise ReleaseError('%s: the test job needs a matrix include list' % WORKFLOW)
    if None in names or len(set(names)) != len(names):
        raise ReleaseError('%s: every step needs a unique name' % WORKFLOW)
    commands = {step['name']: {key: step[key] for key in ('if', 'env', 'run') if key in step}
                for step in steps if 'run' in step and step['name'] not in setup}
    plan_jobs = []
    for row in rows:
        context = {'matrix.%s' % key: value for key, value in row.items()}
        context.update({'runner.os': 'Linux', 'github.workspace': '/work'})
        gates, skipped = [], []
        for step in steps:
            if step['name'] not in commands:
                continue
            try:
                condition = step.get('if', True)
                applies = condition if isinstance(condition, bool) else bool(expression(str(condition), context))
            except (ValueError, IndexError) as error:
                raise ReleaseError('%s: step %r: unsupported condition: %s' % (WORKFLOW, step['name'], error))
            (gates if applies else skipped).append(step['name'])
        plan_jobs.append({'name': job_name('test', row), 'matrix': row, 'reproduce': reproduce(row),
                          'gates': gates, 'not_applicable': skipped})
    if len({j['name'] for j in plan_jobs}) != len(plan_jobs):
        raise ReleaseError('%s: matrix rows have identical job names' % WORKFLOW)
    for name in NATIVE_JOBS:
        if name in jobs:
            plan_jobs.append(native_plan(name, jobs[name], commands))
    blob = lambda path: git_text(root, 'rev-parse', '%s:%s' % (revision, path))
    compatibility = json.loads(show(root, revision, 'compatibility.json'))
    return {'workflow': WORKFLOW, 'workflow_name': workflow.get('name'), 'workflow_blob': blob(WORKFLOW),
            'local_ci_steps_blob': blob(STEPS_SCRIPT), 'compatibility_blob': blob('compatibility.json'),
            'translation': compatibility.get('translation'), 'zig_default': compatibility['zig']['default'],
            'jobs': plan_jobs, 'commands': commands}


# --- Evidence ingestion: every source must name exactly the recorded revision. ---

def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def github_evidence(path, revision, plan):
    raw = Path(path).read_bytes()
    try:
        data = json.loads(raw)
    except ValueError as error:
        raise ReleaseError('%s: invalid run JSON: %s' % (path, error))
    missing = [k for k in ('databaseId', 'headSha', 'status', 'event', 'workflowName', 'jobs') if k not in data]
    if missing:
        raise ReleaseError('%s: run JSON lacks %s (use gh run view --json ...,jobs)' % (path, ', '.join(missing)))
    if data['headSha'] != revision:
        raise ReleaseError('%s: run %s is for %s, not the recorded revision %s'
                           % (path, data['databaseId'], data['headSha'], revision))
    if data['event'] not in ('push', 'workflow_dispatch'):
        # pull_request runs test a merge with the base branch, not the head commit itself.
        raise ReleaseError('%s: run %s is a %s run; it did not test %s itself'
                           % (path, data['databaseId'], data['event'], revision))
    if data['status'] != 'completed':
        raise ReleaseError('%s: run %s is %s, not completed' % (path, data['databaseId'], data['status']))
    if data['workflowName'] != plan['workflow_name']:
        raise ReleaseError('%s: run %s is workflow %r, not %r'
                           % (path, data['databaseId'], data['workflowName'], plan['workflow_name']))
    by_name = {job['name']: job for job in plan['jobs']}
    results = {}
    seen = set()
    for job in data['jobs']:
        name = job.get('name')
        if name not in by_name or name in seen:
            raise ReleaseError('%s: job %r is unknown or repeated in the workflow at %s' % (path, name, revision))
        seen.add(name)
        conclusions = {}
        for step in job.get('steps') or []:
            if step.get('name') in conclusions:
                raise ReleaseError('%s: job %r repeats step %r' % (path, name, step.get('name')))
            conclusions[step.get('name')] = step.get('conclusion')
        for step in by_name[name]['not_applicable']:
            if conclusions.get(step, 'skipped') != 'skipped':
                raise ReleaseError('%s: job %r ran step %r whose condition is false at %s; '
                                   'the run used another workflow' % (path, name, step, revision))
        for step in by_name[name]['gates']:
            if step in conclusions:
                conclusion = conclusions[step]
                results[(name, step)] = ('passed' if conclusion == 'success' else 'failed',
                                         'GitHub step conclusion: %s' % (conclusion or 'none'))
    source = {'kind': 'github-actions', 'run_id': data['databaseId'], 'url': data.get('url'),
              'head_sha': data['headSha'], 'head_branch': data.get('headBranch'), 'event': data.get('event'),
              'conclusion': data.get('conclusion'), 'jobs': sorted(seen), 'file_sha256': sha256_bytes(raw)}
    return source, results


HEADER = re.compile(r'== CI (\{.*\}): (.*) ==')


def local_ci_evidence(directory, revision, plan):
    directory = Path(directory)
    try:
        stamp = dict(line.split('=', 1) for line in (directory / 'source-revision').read_text().splitlines()
                     if '=' in line)
        status_text = (directory / 'exit-status').read_text().strip()
        log = (directory / 'container.log').read_bytes()
    except OSError as error:
        raise ReleaseError('%s: incomplete local CI results: %s' % (directory, error))
    if stamp.get('revision') != revision:
        raise ReleaseError('%s: local CI ran %s, not the recorded revision %s'
                           % (directory, stamp.get('revision'), revision))
    if stamp.get('tracked_clean') != 'yes':
        raise ReleaseError('%s: local CI snapshot had tracked changes; not evidence for %s' % (directory, revision))
    mode, version = stamp.get('mode'), stamp.get('version')
    if mode not in ('full', 'matrix', 'mutations'):
        raise ReleaseError('%s: local CI mode %r does not run workflow gates' % (directory, mode))
    if not re.fullmatch(r'[0-9]+', status_text):
        raise ReleaseError('%s: invalid exit status %r' % (directory, status_text))
    status = int(status_text)
    by_name = {job['name']: job for job in plan['jobs']}
    order = []
    started = {}
    for line in log.decode(errors='replace').splitlines():
        match = HEADER.fullmatch(line.rstrip('\r'))
        if not match:
            continue
        try:
            row = ast.literal_eval(match[1])
        except (ValueError, SyntaxError):
            raise ReleaseError('%s: unreadable step header %r' % (directory, line))
        name = job_name('test', row) if isinstance(row, dict) else None
        if name not in by_name or by_name[name]['matrix'] != row:
            raise ReleaseError('%s: header row %r is not a matrix row at %s' % (directory, row, revision))
        started.setdefault(name, []).append(match[2])
        order.append((name, match[2]))
    for name, steps in started.items():
        if steps != by_name[name]['gates'][:len(steps)]:
            raise ReleaseError('%s: job %r ran steps out of the workflow order at %s' % (directory, name, revision))
    rows = [j for j in plan['jobs'] if j['matrix'] is not None]  # local CI runs only the test job
    if mode == 'full':
        expected = [j['name'] for j in rows if j['matrix'].get('zig') == version and not j['matrix'].get('mutate')]
    elif mode == 'mutations':
        expected = [j['name'] for j in rows if j['matrix'].get('mutate')]
    else:
        expected = [j['name'] for j in rows]
    if set(started) - set(expected):
        raise ReleaseError('%s: %s run started jobs outside its rows' % (directory, mode))
    if status == 0 and any(started.get(name) != by_name[name]['gates'] for name in expected):
        raise ReleaseError('%s: exit status 0 but not every gate of %s started' % (directory, ', '.join(expected)))
    results = {}
    for index, key in enumerate(order):
        if status and index == len(order) - 1:
            results[key] = ('failed', 'local CI exited %d after this step started' % status)
        else:
            results[key] = ('passed', 'local CI completed this step')
    source = {'kind': 'local-ci', 'directory': str(directory), 'head_sha': revision, 'mode': mode,
              'version': version, 'exit_status': status, 'jobs': sorted(started),
              'log_sha256': sha256_bytes(log)}
    return source, results


def parse_unavailable(items, plan):
    by_name = {job['name']: job for job in plan['jobs']}
    declared = []
    for item in items:
        target, sep, reason = item.partition('=')
        name, _, step = target.partition('::')
        reason = reason.strip()
        if not sep or not reason:
            raise ReleaseError('unavailable check %r needs JOB[::STEP]=REASON' % item)
        if name not in by_name or (step and step not in by_name[name]['gates']):
            raise ReleaseError('unavailable check %r names no gate of this revision' % item)
        declared.append((name, step or None, reason))
    return declared


def combine(plan, evidence, declared):
    """Gate list: failed if any evidence failed, passed only with passing evidence."""
    found = {}
    for index, (_, results) in enumerate(evidence):
        for key, (status, detail) in results.items():
            found.setdefault(key, []).append((index, status, detail))
    gates = []
    for job in plan['jobs']:
        for step in job['gates']:
            entries = found.get((job['name'], step), [])
            statuses = {status for _, status, _ in entries}
            gate = {'job': job['name'], 'step': step, 'evidence': [index for index, _, _ in entries],
                    'details': [detail for _, _, detail in entries]}
            gate['status'] = 'failed' if 'failed' in statuses else 'passed' if statuses else 'missing'
            # A step-level declaration must not contradict evidence; a job-level one covers
            # only that job's gates without evidence. Failures are never hidden.
            for_step = [reason for name, target, reason in declared if name == job['name'] and target == step]
            for_job = [reason for name, target, reason in declared if name == job['name'] and target is None]
            if for_step and entries:
                raise ReleaseError('gate %r of %s was declared unavailable but has evidence' % (step, job['name']))
            if gate['status'] == 'missing' and (for_step or for_job):
                gate.update(status='unavailable', reason=(for_step or for_job)[-1])
            gates.append(gate)
    return gates


# --- Review ledger. ---

def read_ledger(root, revision=None):
    """Ledger rows at a revision, or of the checkout's file when revision is None."""
    text = show(root, revision, LEDGER) if revision else (Path(root) / LEDGER).read_text()
    rows = [line.split('\t') for line in text.split('\n') if line]
    if not rows or rows[0] != LEDGER_HEADER:
        raise ReleaseError('%s: header must be %s' % (LEDGER, '\t'.join(LEDGER_HEADER)))
    return rows[1:]


def check_ledger(root, revision=None, allow_unfetched=False):
    """Errors, unverified revisions and per-revision entry counts for the review ledger."""
    errors = []
    rows = read_ledger(root, revision)
    seen = set()
    revisions = {}
    for number, row in enumerate(rows, 2):
        where = '%s:%d' % (LEDGER, number)
        if len(row) != len(LEDGER_HEADER):
            errors.append('%s: expected %d tab-separated fields' % (where, len(LEDGER_HEADER)))
            continue
        path, reviewer, method, digest, reviewed = row
        if not path or path in seen:
            errors.append('%s: empty or duplicate path %r' % (where, path))
        seen.add(path)
        if not reviewer or not method:
            errors.append('%s: %s needs a reviewer and method' % (where, path))
        if not SHA256.fullmatch(digest):
            errors.append('%s: %s has no baseline SHA-256' % (where, path))
        if not SHA1.fullmatch(reviewed):
            errors.append('%s: %s does not name its reviewed revision' % (where, path))
            continue
        revisions.setdefault(reviewed, []).append((where, path, digest))
    unverified = []
    for reviewed, entries in sorted(revisions.items()):
        present = subprocess.run(['git', '-C', str(root), 'cat-file', '-e', reviewed + '^{commit}'],
                                 stderr=subprocess.DEVNULL).returncode == 0
        if not present:
            if allow_unfetched:
                unverified.append(reviewed)
            else:
                errors.append('%s: reviewed revision %s is not available (fetch it, or --allow-unfetched)'
                              % (LEDGER, reviewed))
            continue
        request = ''.join('%s:%s\n' % (reviewed, path) for _, path, _ in entries).encode()
        output = git(root, 'cat-file', '--batch', data=request)
        offset = 0
        for where, path, digest in entries:
            end = output.index(b'\n', offset)
            header = output[offset:end].split()
            if header[-1] == b'missing':
                errors.append('%s: %s does not exist at reviewed revision %s' % (where, path, reviewed))
                offset = end + 1
                continue
            size = int(header[2])
            if sha256_bytes(output[end + 1:end + 1 + size]) != digest:
                errors.append('%s: %s at %s does not have the recorded baseline SHA-256' % (where, path, reviewed))
            offset = end + 2 + size
    return errors, unverified, {rev: len(entries) for rev, entries in sorted(revisions.items())}


def tree_blobs(root, revision):
    out = git(root, 'ls-tree', '-r', '-z', '--full-tree', revision).decode()
    blobs = {}
    for item in out.split('\0'):
        if item:
            meta, path = item.split('\t', 1)
            blobs[path] = meta.split()[2]
    return blobs


def review_summary(root, revision):
    errors, unverified, counts = check_ledger(root, revision)
    if errors:
        raise ReleaseError('review ledger: ' + '; '.join(errors[:5]) + (' ...' if len(errors) > 5 else ''))
    current = tree_blobs(root, revision)
    reviewed = {}
    changed = []
    for path, *_, rev in read_ledger(root, revision):
        reviewed[path] = rev
    for rev in counts:
        before = tree_blobs(root, rev)
        changed += sorted(path for path, r in reviewed.items() if r == rev and current.get(path) != before.get(path))
    return {'ledger': LEDGER, 'ledger_blob': git_text(root, 'rev-parse', '%s:%s' % (revision, LEDGER)),
            'reviewed_revisions': counts, 'entries': len(reviewed),
            'changed_since_review': changed, 'not_in_ledger': sorted(set(current) - set(reviewed))}


# --- Record assembly and verification. ---

def summarize(gates):
    summary = {status: 0 for status in GATE_STATUSES}
    for gate in gates:
        summary[gate['status']] += 1
    return summary


def build_record(root, github_runs=(), local_runs=(), unavailable=()):
    revision = clean_head(root)
    plan = build_plan(root, revision)
    declared = parse_unavailable(unavailable, plan)
    evidence = [github_evidence(path, revision, plan) for path in github_runs]
    evidence += [local_ci_evidence(path, revision, plan) for path in local_runs]
    gates = combine(plan, evidence, declared)
    summary = summarize(gates)
    return {
        'schema': SCHEMA, 'revision': revision, 'tree': 'clean',
        'profile': {key: plan[key] for key in ('workflow', 'workflow_name', 'workflow_blob', 'local_ci_steps_blob',
                                               'compatibility_blob', 'translation', 'zig_default')},
        'jobs': [{key: job[key] for key in ('name', 'matrix', 'reproduce', 'not_applicable')} for job in plan['jobs']],
        'commands': plan['commands'],
        'evidence': [source for source, _ in evidence],
        'gates': gates,
        'unavailable': [{'job': name, 'step': step, 'reason': reason} for name, step, reason in declared],
        'review': review_summary(root, revision),
        'summary': summary,
        'status': 'complete' if summary['failed'] == summary['missing'] == 0 else 'incomplete',
    }


def verify_record(root, record):
    """Problems of a published record relative to its own revision; [] when consistent."""
    problems = []
    if record.get('schema') != SCHEMA:
        return ['schema is %r, not %s' % (record.get('schema'), SCHEMA)]
    revision = record.get('revision', '')
    if not SHA1.fullmatch(revision or ''):
        return ['record does not name a full revision']
    plan = build_plan(root, revision)
    for key in ('workflow_blob', 'local_ci_steps_blob', 'compatibility_blob'):
        if record.get('profile', {}).get(key) != plan[key]:
            problems.append('profile %s does not match revision %s' % (key, revision))
    evidence = record.get('evidence') or []
    for index, source in enumerate(evidence):
        if source.get('head_sha') != revision or source.get('kind') not in ('github-actions', 'local-ci'):
            problems.append('evidence %d is not %s evidence for %s' % (index, source.get('kind'), revision))
    expected = [(job['name'], step) for job in plan['jobs'] for step in job['gates']]
    gates = record.get('gates') or []
    if [(g.get('job'), g.get('step')) for g in gates] != expected:
        problems.append('gate list differs from the workflow at %s' % revision)
    for gate in gates:
        label = '%s / %s' % (gate.get('job'), gate.get('step'))
        refs = gate.get('evidence')
        status = gate.get('status')
        if status not in GATE_STATUSES or not isinstance(refs, list):
            problems.append('%s: invalid status or evidence list' % label)
            continue
        if any(not isinstance(ref, int) or not 0 <= ref < len(evidence) for ref in refs):
            problems.append('%s: references unknown evidence' % label)
        elif status in ('passed', 'failed') and not refs:
            problems.append('%s: %s without evidence for %s' % (label, status, revision))
        elif status in ('missing', 'unavailable') and refs:
            problems.append('%s: %s but cites evidence' % (label, status))
        if status == 'unavailable' and not str(gate.get('reason') or '').strip():
            problems.append('%s: unavailable without a reason' % label)
        if status == 'passed' and any(evidence[ref].get('jobs') is not None and gate.get('job') not in evidence[ref]['jobs']
                                      for ref in refs if isinstance(ref, int) and 0 <= ref < len(evidence)):
            problems.append('%s: cited evidence does not cover this job' % label)
    summary = summarize([g for g in gates if g.get('status') in GATE_STATUSES])
    if record.get('summary') != summary:
        problems.append('summary does not match the gate list')
    wanted = 'complete' if summary['failed'] == summary['missing'] == 0 else 'incomplete'
    if record.get('status') != wanted:
        problems.append('status is %r but the gates make it %r' % (record.get('status'), wanted))
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('plan', 'record', 'verify', 'ledger'):
        command = sub.add_parser(name)
        command.add_argument('--root', default=str(Path(__file__).resolve().parents[1]))
    sub.choices['plan'].add_argument('--json', action='store_true')
    sub.choices['plan'].add_argument('--revision', default='HEAD')
    sub.choices['record'].add_argument('--github-run', action='append', default=[], metavar='RUN_JSON')
    sub.choices['record'].add_argument('--local-ci', action='append', default=[], metavar='RESULTS_DIR')
    sub.choices['record'].add_argument('--unavailable', action='append', default=[], metavar='JOB[::STEP]=REASON')
    sub.choices['record'].add_argument('--out')
    sub.choices['verify'].add_argument('record')
    ledger = sub.choices['ledger'].add_mutually_exclusive_group()
    ledger.add_argument('--allow-unfetched', action='store_true', help='skip hash checks for absent revisions')
    ledger.add_argument('--revisions', action='store_true', help='print the reviewed revisions and exit')
    args = parser.parse_args(argv)
    root = Path(args.root)
    try:
        if args.command == 'plan':
            plan = build_plan(root, git_text(root, 'rev-parse', '--verify', args.revision + '^{commit}'))
            if args.json:
                print(json.dumps(plan, indent=2))
            else:
                for job in plan['jobs']:
                    print('%s: %d gates, %d not applicable; reproduce: %s'
                          % (job['name'], len(job['gates']), len(job['not_applicable']), job['reproduce']))
            return 0
        if args.command == 'record':
            record = build_record(root, args.github_run, args.local_ci, args.unavailable)
            text = json.dumps(record, indent=2) + '\n'
            if args.out:
                Path(args.out).write_text(text)
            else:
                sys.stdout.write(text)
            s = record['summary']
            print('%s at %s: %d passed, %d failed, %d missing, %d unavailable'
                  % (record['status'], record['revision'], s['passed'], s['failed'], s['missing'],
                     s['unavailable']), file=sys.stderr)
            return 0 if record['status'] == 'complete' else 1
        if args.command == 'verify':
            problems = verify_record(root, json.loads(Path(args.record).read_text()))
            for problem in problems:
                print('error: ' + problem, file=sys.stderr)
            if not problems:
                print('OK: release record is consistent with its revision')
            return 1 if problems else 0
        if args.revisions:
            print(' '.join(sorted({row[4] for row in read_ledger(root)
                                   if len(row) == 5 and SHA1.fullmatch(row[4])})))
            return 0
        errors, unverified, counts = check_ledger(root, allow_unfetched=args.allow_unfetched)
        for error in errors:
            print('error: ' + error, file=sys.stderr)
        for rev in unverified:
            print('note: reviewed revision %s is not fetched; hashes unverified' % rev, file=sys.stderr)
        if not errors:
            print('OK: %s names reviewed revisions for all entries: %s'
                  % (LEDGER, ', '.join('%s (%d)' % item for item in counts.items())))
        return 1 if errors else 0
    except ReleaseError as error:
        print('error: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
