#!/usr/bin/env python3
"""Declared-support target matrix (Q05): every supported path must be backed on its platform.

  target-matrix.py check [--root DIR] [--strict] [--json]

compatibility.json declares the supported Zig versions, their build hosts and the target
profiles. Each version x host x native target x profile path it declares must have one entry
in assurance/target-matrix.json naming a CI job of .github/workflows/ci.yml (and, for a matrix
job, its exact `include` row) whose steps provide, on that host:

  native_execution  a differential or native-only run of translated programs (check.sh with
                    the diff test, diff.sh, or a roadmap gate's `check.sh --native[-only]`);
  target_probe      scripts/floatprobe.sh or scripts/abi-probe.py observe;
  proof_check       `lake build ... Proofs`.

A step counts only when its job's runner is that host, its `if` holds for that row, it is
bound to the path's Zig version, and it does not compile another OS's `Gen-<os>.lean`: proofs
over a foreign golden compiled on another host are not platform support. A missing kind may
be recorded as an explicit gap (never `proof_check`); `--strict` fails on any gap. Profiles
without a native target (`unverified`) must be listed as input-only; targets that are not
declared (WASM until T02/T05) must stay undeclared. Offline: no Zig, Lake or Lean process.
Exit 0: consistent; 1: a path is unbacked or the map is stale; 2: an input is unreadable.
"""
import argparse
import json
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 'air2lean-target-matrix/1'
MAP = 'assurance/target-matrix.json'
WORKFLOW = '.github/workflows/ci.yml'
KINDS = ('native_execution', 'target_probe', 'proof_check')
GAPPABLE = ('native_execution', 'target_probe')
# `uname -s` in lower case, as scripts/check.sh names Gen-<os>.lean goldens.
HOST_OS = {'linux': 'linux', 'macos': 'darwin'}
RUNNER_OS = {'linux': 'Linux', 'macos': 'macOS'}
# The only step environment the checker evaluates: version binding and check.sh's diff switch.
BOUND_ENV = ('AIR2LEAN_ZIG_VERSION', 'AIR2LEAN_DIFF')


class Unreadable(Exception):
    pass


class Unknown(Exception):
    """An expression refers to a context this offline checker cannot know."""


# ---- GitHub Actions expressions (the subset ci.yml uses) --------------------------------------

TOKEN = re.compile(r"\s*(?:('(?:[^']|'')*')|(&&|\|\||==|!=|!|\(|\))|"
                   r"([A-Za-z_][\w.-]*(?:\(\))?)|(\d+(?:\.\d+)?))")
FUNCTIONS = {'success()': True, 'always()': True, 'failure()': False, 'cancelled()': False}


def tokenize(text):
    tokens, pos, text = [], 0, text.strip()
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m or m.end() == pos:
            raise Unknown(f'cannot parse expression {text!r}')
        string, op, ident, number = m.groups()
        if string is not None:
            tokens.append(('lit', string[1:-1].replace("''", "'")))
        elif op is not None:
            tokens.append(('op', op))
        elif number is not None:
            tokens.append(('lit', float(number)))
        else:
            tokens.append(('id', ident))
        pos = m.end()
    return tokens


def truthy(value):
    if isinstance(value, float) and math.isnan(value):
        return False
    return value not in (None, False, 0, '')


def number(value):
    if value is None or value == '':
        return 0.0
    if isinstance(value, (bool, int, float)):
        return float(value)
    try:
        return float(value)
    except ValueError:
        return math.nan


def equal(left, right):
    if isinstance(left, str) and isinstance(right, str):
        return left.lower() == right.lower()
    if left is None or right is None:
        return left is right
    return number(left) == number(right)


def evaluate(expression, context):
    """Value of one expression for a {matrix, runner.os} context (JavaScript-like && / ||)."""
    tokens = tokenize(expression)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else (None, None)

    def take():
        nonlocal pos
        pos += 1
        return tokens[pos - 1]

    def primary():
        kind, value = take() if pos < len(tokens) else (None, None)
        if kind == 'lit':
            return value
        if (kind, value) == ('op', '('):
            inner = disjunction()
            if take() != ('op', ')'):
                raise Unknown(f'unbalanced parentheses in {expression!r}')
            return inner
        if kind == 'id':
            if value in ('true', 'false'):
                return value == 'true'
            if value == 'null':
                return None
            if value in FUNCTIONS:
                return FUNCTIONS[value]
            if value == 'runner.os':
                return context['runner.os']
            if value.startswith('matrix.'):
                if context['matrix'] is None:
                    raise Unknown(f'{value} in a job without a matrix')
                return context['matrix'].get(value[len('matrix.'):])
        raise Unknown(f'unsupported term {value!r} in {expression!r}')

    def unary():
        if peek() == ('op', '!'):
            take()
            return not truthy(unary())
        return primary()

    def comparison():
        left = unary()
        if peek() in (('op', '=='), ('op', '!=')):
            op = take()[1]
            same = equal(left, unary())
            return same if op == '==' else not same
        return left

    def conjunction():
        value = comparison()
        while peek() == ('op', '&&'):
            take()
            right = comparison()
            value = right if truthy(value) else value
        return value

    def disjunction():
        value = conjunction()
        while peek() == ('op', '||'):
            take()
            right = conjunction()
            value = value if truthy(value) else right
        return value

    result = disjunction()
    if pos != len(tokens):
        raise Unknown(f'trailing tokens in {expression!r}')
    return result


def condition(text, context):
    if text is None:
        return True
    m = re.fullmatch(r'\s*\$\{\{(.*)\}\}\s*', text, re.S)
    return truthy(evaluate(m.group(1) if m else text, context))


def interpolate(text, context):
    def one(m):
        value = evaluate(m.group(1), context)
        if isinstance(value, bool):
            return 'true' if value else 'false'
        if isinstance(value, float) and value.is_integer():
            return str(int(value))
        return '' if value is None else str(value)
    return re.sub(r'\$\{\{(.*?)\}\}', one, text)


# ---- workflow (a narrow line parser for the layout ci.yml uses) ------------------------------

def scalar(text):
    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in '"\'':
        return text[1:-1]
    return text


def typed(text):
    text = text.strip()
    if text in ('true', 'false'):
        return text == 'true'
    if re.fullmatch(r'\d+', text):
        return int(text)
    return scalar(text)


def parse_workflow(text):
    """{job: {'runs-on', 'if', 'env', 'matrix' (list of rows or None), 'steps'}}."""
    lines = text.splitlines()
    try:
        start = lines.index('jobs:')
    except ValueError:
        raise Unreadable(f'{WORKFLOW}: no top-level jobs')
    jobs, job, step, section, block = {}, None, None, None, None
    for line in lines[start + 1:]:
        if block is not None:
            if not line.strip() or line.startswith(' ' * block[1]):
                block[0].append(line[block[1]:])
                continue
            block = None
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        indent = len(line) - len(line.lstrip())
        if indent == 0:
            break
        if indent == 2:
            m = re.fullmatch(r'  ([\w-]+):\s*', line)
            if not m:
                raise Unreadable(f'{WORKFLOW}: unexpected job line {line!r}')
            job = jobs[m.group(1)] = {'runs-on': None, 'if': None, 'env': {}, 'matrix': None,
                                      'steps': []}
            step, section = None, None
            continue
        if job is None:
            continue
        if indent == 4:
            key, _, value = line.strip().partition(':')
            section, step = key, None
            if key in ('runs-on', 'if'):
                job[key] = value.strip()
            continue
        if section == 'env' and indent == 6:
            key, _, value = line.strip().partition(':')
            job['env'][key] = scalar(value)
        elif section == 'strategy':
            row = re.fullmatch(r'\s*- ([\w-]+): (.*)', line)
            key = re.fullmatch(r'\s*([\w-]+): (.*)', line)
            if line.strip() == 'include:':
                job['matrix'] = []
            elif row and job['matrix'] is not None:
                job['matrix'].append({row.group(1): typed(row.group(2))})
            elif key and job['matrix'] and indent >= 12:
                job['matrix'][-1][key.group(1)] = typed(key.group(2))
        elif section == 'steps':
            m = re.fullmatch(r'      - ([\w-]+):(.*)', line)
            if m:
                step = {'env': {}, 'name': None, 'if': None, 'run': ''}
                job['steps'].append(step)
                line = '        ' + line[8:]
                indent = 8
            if step is None:
                continue
            if indent == 8:
                key, _, value = line.strip().partition(':')
                step['_key'] = key
                value = value.strip()
                if key == 'run' and value in ('|', '>'):
                    lines_out = []
                    step['run'] = lines_out
                    block = (lines_out, 10)
                elif key in ('name', 'if', 'run'):
                    step[key] = value if key == 'if' else scalar(value)
            elif indent == 10 and step.get('_key') == 'env':
                key, _, value = line.strip().partition(':')
                step['env'][key] = scalar(value)
    for job in jobs.values():
        for step in job['steps']:
            if isinstance(step['run'], list):
                step['run'] = '\n'.join(step['run'])
            step.pop('_key', None)
    return jobs


def runner_host(label):
    """GitHub-hosted runner label -> arch-os host, or None when it is not a fixed host."""
    m = re.fullmatch(r'ubuntu-[\d.]+(-arm)?', label)
    if m:
        return 'aarch64-linux' if m.group(1) else 'x86_64-linux'
    m = re.fullmatch(r'macos-(\d+)(-large|-xlarge)?', label)
    if m:
        intel = (int(m.group(1)) < 14 and m.group(2) != '-xlarge') or m.group(2) == '-large'
        return 'x86_64-macos' if intel else 'aarch64-macos'
    return None


# ---- evidence recognizers --------------------------------------------------------------------

def recognized(kind, run, env):
    if kind == 'native_execution':
        if re.search(r'(?<![\w/.-])scripts/check\.sh\b', run) and env.get('AIR2LEAN_DIFF', '1') != '0':
            return True
        return bool(re.search(r'(?<![\w/.-])scripts/diff\.sh\b|/check\.sh --native(-only)?\b', run))
    if kind == 'target_probe':
        return bool(re.search(r'(?<![\w/.-])scripts/(floatprobe\.sh|abi-probe\.py observe)\b', run))
    if kind == 'proof_check':
        return bool(re.search(r'\blake build\b[^\n]*(?<![\w.])Proofs(?![\w.])', run))
    raise ValueError(kind)


def foreign_goldens(run, host_os):
    return sorted({f'Gen-{os}.lean' for os in re.findall(r'\bGen-(\w+)\.lean\b', run)
                   if os != host_os})


# ---- declared paths --------------------------------------------------------------------------

def load_json(root, rel):
    try:
        return json.loads((root/rel).read_text(encoding='utf-8'))
    except (OSError, ValueError) as error:
        raise Unreadable(f'{rel}: {error}')


def declared(meta):
    """(paths, input-only profile names, errors) from compatibility.json."""
    errors, paths, input_only = [], [], []
    try:
        versions = meta['zig']['versions']
        profiles = meta['profiles']
        reference = meta['translation']['target']
    except (KeyError, TypeError):
        raise Unreadable('compatibility.json: zig.versions, profiles or translation.target missing')
    hosts = {h for v in versions for h in v.get('hosts', [])}
    profile_hosts = {}
    for profile in profiles:
        triples = profile.get('target_triples') or []
        if triples == ['unverified']:
            input_only.append(profile['name'])
            continue
        if not triples:
            errors.append(f'profile {profile["name"]} declares no target triples '
                          '(use ["unverified"] for an input-only profile)')
        targets = set()
        for triple in triples:
            arch_os = '-'.join(triple.split('-')[:2])
            targets.add(arch_os)
            if arch_os not in hosts:
                errors.append(f'profile {profile["name"]} declares target {triple} with no '
                              'supported native host (declare a host and its CI path first)')
        profile_hosts[profile['name']] = targets
    for version in versions:
        for host in version.get('hosts', []):
            for name, targets in profile_hosts.items():
                if host in targets:
                    paths.append((version['version'], host, host, name))
            if not any(host in t for t in profile_hosts.values()):
                errors.append(f'zig {version["version"]} host {host} has no target profile')
    if not any(p[1] == reference for p in paths):
        errors.append(f'reference translation target {reference} is not a declared path')
    return paths, input_only, errors


def path_id(path):
    return '/'.join(path)


# ---- checking --------------------------------------------------------------------------------

def check_entry(entry, path, jobs):
    """Errors and the gap kinds for one map entry."""
    pid = path_id(path)
    version, host = path[0], path[1]
    errors = []
    job = jobs.get(entry.get('job'))
    if job is None:
        return [f'{pid}: CI job {entry.get("job")!r} not found in {WORKFLOW}'], []
    label = scalar(job['runs-on'] or '')
    job_host = runner_host(label)
    if job_host != host:
        errors.append(f'{pid}: job {entry["job"]!r} runs on {label!r} ({job_host}), not {host}; '
                      'evidence from another host is foreign-golden compilation, not platform support')
        return errors, []
    os_name = host.split('-', 1)[1]
    selector = entry.get('matrix')
    if job['matrix'] is None:
        if selector:
            return [f'{pid}: job {entry["job"]!r} has no matrix, but the entry selects a row'], []
        row = None
    else:
        rows = [r for r in job['matrix'] if selector and all(r.get(k) == v for k, v in selector.items())]
        if len(rows) != 1:
            return [f'{pid}: matrix selector {selector!r} matches {len(rows)} rows of '
                    f'job {entry["job"]!r} (need exactly one)'], []
        row = rows[0]
        if str(row.get('zig')) != version:
            errors.append(f'{pid}: selected matrix row is Zig {row.get("zig")}, not {version}')
    context = {'matrix': row, 'runner.os': RUNNER_OS[os_name]}
    try:
        job_runs = condition(job['if'], context)
    except Unknown as error:
        return [f'{pid}: job condition: {error}'], []
    if not job_runs:
        return [f'{pid}: job {entry["job"]!r} does not run for this row'], []
    steps = {}
    for step in job['steps']:
        if step['name']:
            steps.setdefault(step['name'], []).append(step)
    evidence, gaps = entry.get('evidence') or {}, entry.get('gaps') or {}
    for kind in set(evidence) | set(gaps):
        if kind not in KINDS:
            errors.append(f'{pid}: unknown evidence kind {kind!r}')
    for kind in KINDS:
        names, gap = evidence.get(kind) or [], gaps.get(kind)
        if not isinstance(names, list) or not all(isinstance(n, str) for n in names):
            errors.append(f'{pid}: {kind} evidence must be a list of step names')
            continue
        if gap is not None:
            if kind not in GAPPABLE:
                errors.append(f'{pid}: {kind} cannot be waived as a gap')
            elif not isinstance(gap, str) or not gap.strip():
                errors.append(f'{pid}: {kind} gap needs a reason')
            if names:
                errors.append(f'{pid}: {kind} lists both evidence and a gap')
            continue
        if not names:
            errors.append(f'{pid}: no {kind} evidence and no recorded gap')
        for name in names:
            errors += [f'{pid}: {kind} step {name!r}: {e}'
                       for e in check_step(steps.get(name), job, context, version, kind, os_name)]
    if len(gaps) > 1:
        errors.append(f'{pid}: more than one gap ({", ".join(sorted(gaps))}); not a supported path')
    return errors, sorted(k for k in gaps if k in GAPPABLE)


def check_step(found, job, context, version, kind, os_name):
    if not found:
        return ['not found in the job']
    if len(found) > 1:
        return ['the step name is not unique in the job']
    step = found[0]
    try:
        if not condition(step['if'], context):
            return ['its `if` is false for this row']
        merged = {**job['env'], **step['env']}
        env = {k: interpolate(merged[k], context) for k in BOUND_ENV if k in merged}
    except Unknown as error:
        return [str(error)]
    errors = []
    bound = env.get('AIR2LEAN_ZIG_VERSION')
    if context['matrix'] is None and bound is None:
        errors.append('a job without a matrix must bind AIR2LEAN_ZIG_VERSION in the step env')
    elif bound is not None and bound != version:
        errors.append(f'bound to Zig {bound}, not {version}')
    foreign = foreign_goldens(step['run'], HOST_OS[os_name])
    if foreign:
        errors.append(f'compiles foreign golden {", ".join(foreign)} on {os_name}; '
                      'foreign-golden compilation is not platform support')
    if not recognized(kind, step['run'], env):
        errors.append(f'its commands do not perform {kind}')
    return errors


def check(root, strict=False):
    """(errors, report rows, input-only profiles)."""
    root = Path(root)
    meta = load_json(root, 'compatibility.json')
    matrix = load_json(root, MAP)
    try:
        jobs = parse_workflow((root/WORKFLOW).read_text(encoding='utf-8'))
    except OSError as error:
        raise Unreadable(f'{WORKFLOW}: {error}')
    if matrix.get('schema') != SCHEMA:
        return [f'{MAP}: schema must be {SCHEMA!r}'], [], []
    paths, input_only, errors = declared(meta)
    entries = {}
    for entry in matrix.get('paths', []):
        key = tuple(str(entry.get(k)) for k in ('zig', 'host', 'target', 'profile'))
        if key in entries:
            errors.append(f'{MAP}: duplicate entry {path_id(key)}')
        entries[key] = entry
    rows = []
    for path in paths:
        entry = entries.pop(path, None)
        if entry is None:
            errors.append(f'{path_id(path)}: declared supported in compatibility.json, '
                          f'but {MAP} maps it to no CI job')
            continue
        entry_errors, gaps = check_entry(entry, path, jobs)
        errors += entry_errors
        if strict and gaps:
            errors.append(f'{path_id(path)}: --strict: recorded gaps {", ".join(gaps)}')
        rows.append({'path': path_id(path), 'job': entry.get('job'), 'gaps': gaps,
                     'status': 'backed' if not gaps else 'partial'})
    for key in entries:
        errors.append(f'{MAP}: {path_id(key)} is not a path compatibility.json declares')
    listed = [p.get('profile') for p in matrix.get('input_only_profiles', [])]
    if sorted(listed) != sorted(input_only):
        errors.append(f'{MAP}: input_only_profiles {sorted(listed)} != compatibility.json '
                      f'profiles without native targets {sorted(input_only)}')
    declared_targets = {p[2] for p in paths} | {
        '-'.join(t.split('-')[:2]) for p in meta.get('profiles', []) for t in p.get('target_triples', [])}
    for item in matrix.get('not_declared', []):
        target = '-'.join(str(item.get('target')).split('-')[:2])
        if target in declared_targets:
            errors.append(f'{MAP}: {item.get("target")} is listed as not declared, '
                          'but compatibility.json declares it')
        if not item.get('depends_on') or not item.get('reason'):
            errors.append(f'{MAP}: not_declared {item.get("target")} needs depends_on and a reason')
    return errors, rows, sorted(input_only)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='action', required=True)
    run = sub.add_parser('check')
    run.add_argument('--root', type=Path, default=ROOT)
    run.add_argument('--strict', action='store_true', help='fail on any recorded gap')
    run.add_argument('--json', action='store_true')
    args = parser.parse_args(argv)
    try:
        errors, rows, input_only = check(args.root, args.strict)
    except (Unreadable, KeyError, TypeError, AttributeError) as error:
        # Malformed input shapes (a profile without a name, a non-object entry) are unreadable.
        print(f'target-matrix: {type(error).__name__}: {error}', file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({'ok': not errors, 'errors': errors, 'paths': rows,
                          'input_only_profiles': input_only}, indent=2))
    else:
        for row in rows:
            gaps = f' (gaps: {", ".join(row["gaps"])})' if row['gaps'] else ''
            print(f'{row["status"]:8} {row["path"]} <- {row["job"]}{gaps}')
        for error in errors:
            print(f'error: {error}', file=sys.stderr)
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
