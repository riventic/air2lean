#!/usr/bin/env python3
"""Declared-support target matrix (Q05): every supported path must be backed on its platform.

  target-matrix.py check [--root DIR] [--strict] [--json]

compatibility.json declares the supported Zig versions, their build hosts and the target
profiles. Each version x host x native target x profile path it declares must have one entry
in assurance/target-matrix.json naming a CI job of .github/workflows/ci.yml (and, for a matrix
job, its exact `include` row) whose steps provide, on that host:

  native_execution  a differential or native-only run of translated programs (check.sh with
                    the diff test, diff.sh, or a roadmap gate's `check.sh --native[-only]`);
  target_probe      scripts/floatprobe.sh, scripts/abi-probe.py observe or (T04)
                    scripts/aarch64-abi.py check;
  proof_check       `lake build ... Proofs`.

A step counts only when its job's runner is that host, its `if` holds for that row, it is
bound to the path's Zig version, and it does not compile another OS's `Gen-<os>.lean`: proofs
over a foreign golden compiled on another host are not platform support. A missing kind may
be recorded as an explicit gap (never `proof_check`); `--strict` fails on any gap. Profiles
without a native target (`unverified`) must be listed as input-only; targets that are not
declared (WASM until T02/T05) must stay undeclared.

`abi_profiles` (T04) lists ABI-qualified profiles, which need not be declared translation paths: each names its versioned expected file, a `probe` step on the profile's own
host running `scripts/aarch64-abi.py check --target TRIPLE`, and a `proof` step (any host: the
check is kernel/Lean only) running `tests/roadmap/aarch64-abi/Model.lean` on that file. Offline:
no Zig, Lake or Lean process.
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

# .NET Char.IsWhiteSpace, shared by numeric conversion and expression token boundaries.
WHITESPACE = ('\t\n\v\f\r \x85\xa0\u1680\u2000\u2001\u2002\u2003\u2004\u2005'
              '\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000')
SPACE = '[' + re.escape(WHITESPACE) + ']'
DECIMAL = r'[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)'
TOKEN = re.compile(SPACE + r"*(?:('(?:[^']|'')*')|(&&|\|\||==|!=|!|\(|\)|,)|"
                   r"([A-Za-z_][A-Za-z0-9_-]*(?:\.[A-Za-z_][A-Za-z0-9_-]*)*)|(" + DECIMAL + r"))")
FUNCTIONS = {'success': True, 'always': True, 'failure': False, 'cancelled': False}


def tokenize(text):
    tokens, pos, text = [], 0, text.strip(WHITESPACE)
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m or m.end() == pos:
            raise Unknown(f'cannot parse expression {text!r}')
        string, op, ident, numeric = m.groups()
        if string is not None:
            tokens.append(('lit', string[1:-1].replace("''", "'")))
        elif op is not None:
            tokens.append(('op', op))
        elif numeric is not None:
            tokens.append(('lit', number(numeric)))
        else:
            tokens.append(('id', ident))
        pos = m.end()
    return tokens


def expression_scalar(value):
    """Supported scalar kinds, with every numeric value canonicalized to finite binary64."""
    if value is None or isinstance(value, (str, bool)):
        return value
    if not isinstance(value, (int, float)):
        raise Unknown(f'unsupported expression scalar of {type(value).__name__}')
    try:
        value = float(value)
    except OverflowError as error:
        raise Unknown('number is outside the GitHub expression range') from error
    if not math.isfinite(value):
        raise Unknown('unsupported non-finite numeric value')
    return value


def truthy(value):
    return expression_scalar(value) not in (None, False, 0, '')


def number(value):
    """Only finite numeric values and trimmed decimal text; other conversions fail closed."""
    if isinstance(value, str):
        value = value.strip(WHITESPACE)
        if not value:
            return 0.0
        if not re.fullmatch(DECIMAL, value):
            raise Unknown(f'unsupported numeric string {value!r}')
        value = float(value)
    elif value is None or isinstance(value, bool):
        raise Unknown(f'unsupported numeric conversion of {type(value).__name__}')
    return expression_scalar(value)


def equal(left, right):
    left, right = expression_scalar(left), expression_scalar(right)
    if isinstance(left, float) and isinstance(right, str):
        right = number(right)
    elif isinstance(left, str) and isinstance(right, float):
        left = number(left)
    if type(left) is not type(right):
        raise Unknown(f'unsupported mixed-kind comparison of {type(left).__name__} and {type(right).__name__}')
    if isinstance(left, str):
        if not left.isascii() or not right.isascii():
            raise Unknown('unsupported non-ASCII string comparison')
        return left.lower() == right.lower()
    return left == right


def context_field(mapping, name):
    """One ASCII case-insensitive field, with ambiguous or unsupported keys rejected."""
    fields = {}
    for key, value in mapping.items():
        if not isinstance(key, str) or not key.isascii():
            raise Unknown(f'unsupported non-ASCII or non-string context key while reading {name!r}')
        folded = key.lower()
        if folded in fields:
            raise Unknown(f'ambiguous case variants of context field {key!r}')
        fields[folded] = value
    return fields.get(name.lower())


def expression_string(value):
    """GitHub scalar coercion, shared by interpolation and format()."""
    value = expression_scalar(value)
    if value is None:
        return ''
    if isinstance(value, str):
        return value
    if isinstance(value, bool):
        return 'true' if value else 'false'
    if isinstance(value, float):
        # actions/runner EvaluationResult.ConvertToString uses invariant NumberFormat="G15".
        return format(value, '.15G')
    raise Unknown(f'unsupported string conversion of {type(value).__name__}')


def format_string(template, arguments):
    """Positional fields and doubled braces; no Python format directives or traversal."""
    def field(match):
        token, index = match.group(0), match.group(1)
        if token in ('{{', '}}'):
            return token[0]
        if index is None:
            raise Unknown('invalid format string')
        try:
            index = int(index)
        except ValueError as error:
            raise Unknown('invalid format argument index') from error
        if index >= len(arguments):
            raise Unknown('missing format argument')
        return expression_string(arguments[index])
    return re.sub(r'\{\{|\}\}|\{([0-9]+)\}|[{}]', field, expression_string(template))


def evaluate(expression, context):
    """Value for a nested matrix and explicitly provided context keys (&& / || return values)."""
    tokens = tokenize(expression)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else (None, None)

    def take():
        nonlocal pos
        if pos == len(tokens):
            raise Unknown(f'incomplete expression {expression!r}')
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
            if peek() == ('op', '('):
                take()
                arguments = []
                if peek() != ('op', ')'):
                    while True:
                        arguments.append(disjunction())
                        if peek() != ('op', ','):
                            break
                        take()
                if take() != ('op', ')'):
                    raise Unknown(f'unbalanced function call in {expression!r}')
                name = value.lower()
                if name == 'format' and 1 <= len(arguments) <= 255:
                    return format_string(arguments[0], arguments[1:])
                if name in FUNCTIONS and not arguments:
                    status = context.get(name, FUNCTIONS[name])
                    if not isinstance(status, bool):
                        raise Unknown(f'unsupported status context: {name!r}')
                    return status
                raise Unknown(f'unsupported function or argument count: {value!r}')
            if value in ('true', 'false'):
                return value == 'true'
            if value == 'null':
                return None
            if value == 'env.AIR2LEAN_REUSED':
                return ''  # a path is backed by a part's executing run, never by a reused one (docs/ci.md)
            if value.startswith('matrix.'):
                if '.' in value[len('matrix.'):]:
                    raise Unknown(f'unsupported nested matrix reference {value!r} in {expression!r}')
                matrix = context.get('matrix')
                if matrix is None:
                    raise Unknown(f'{value} in a job without a matrix')
                if not isinstance(matrix, dict):
                    raise Unknown('unsupported matrix context')
                try:
                    resolved = context_field(matrix, value[len('matrix.'):])
                except Unknown as error:
                    raise Unknown(f'{value}: {error}') from error
            elif value in context:
                resolved = context[value]
            else:
                raise Unknown(f'unsupported term {value!r} in {expression!r}')
            try:
                return expression_scalar(resolved)
            except Unknown as error:
                raise Unknown(f'{value}: {error}') from error
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
            try:
                same = equal(left, unary())
            except Unknown as error:
                raise Unknown(f'{expression!r}: {error}') from error
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
    if isinstance(text, bool):
        return text
    if not isinstance(text, str):
        raise Unknown('unsupported condition type: %s' % type(text).__name__)
    m = re.fullmatch(SPACE + r'*\$\{\{(.*)\}\}' + SPACE + '*', text, re.S)
    return truthy(evaluate(m.group(1) if m else text, context))


def interpolate(text, context):
    # A closing delimiter inside a quoted expression string is ordinary string data.
    parts, end = [], 0
    while True:
        start = text.find('${{', end)
        if start < 0:
            return ''.join(parts) + text[end:]
        parts.append(text[end:start])
        position, quoted = start + 3, False
        while position < len(text):
            if text[position] == "'":
                if quoted and text.startswith("''", position):
                    position += 2
                    continue
                quoted = not quoted
            elif not quoted and text.startswith('}}', position):
                break
            position += 1
        else:
            raise Unknown('unterminated interpolation')
        parts.append(expression_string(evaluate(text[start + 3:position], context)))
        end = position + 2


# ---- shared workflow DATA subset (moved from release-record.py) -------------------------------

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False)


def selected_rows(rows, selector):
    """Match DATA identities; a missing field is distinct from an explicit null."""
    if not selector:
        return []
    if not isinstance(selector, dict):
        raise Unreadable('%s: matrix selector must be a mapping' % WORKFLOW)
    try:
        identity = {key: canonical(value) for key, value in selector.items()}
        return [row for row in rows if all(key in row and canonical(row[key]) == value
                                          for key, value in identity.items())]
    except (TypeError, ValueError) as error:
        raise Unreadable('%s: unsupported matrix selector DATA: %s' % (WORKFLOW, error)) from error


def _scalar(text, where):
    text = text.strip(' \t')
    if text[:1] in ('"', "'"):
        quote, position, content = text[0], 1, []
        while position < len(text):
            char = text[position]
            if char == quote:
                if quote == "'" and text.startswith("''", position):
                    content.append("'")
                    position += 2
                    continue
                rest = text[position + 1:]
                if rest and (rest[0] not in ' \t' or not rest.strip(' \t').startswith('#')):
                    raise Unreadable('%s: unsupported quoted scalar' % where)
                return ''.join(content)
            if quote == '"' and char == '\\':
                raise Unreadable('%s: unsupported quoted scalar escape' % where)
            content.append(char)
            position += 1
        raise Unreadable('%s: unterminated quoted scalar' % where)
    text = re.sub(r'(?<=[ \t])#.*$', '', text).rstrip(' \t')
    if text.startswith('['):
        # Existing workflows use simple flow lists of names; complex flow syntax is refused.
        if not re.fullmatch(r'\[[ \t]*(?:[A-Za-z0-9_.-]+(?:[ \t]*,[ \t]*[A-Za-z0-9_.-]+)*)?[ \t]*\]', text):
            raise Unreadable('%s: unsupported flow sequence' % where)
        return [_scalar(item, where) for item in text[1:-1].split(',') if item.strip(' \t')]
    if (text[:1] in ('&', '*', '!', '>', '|', '{', '}', ']', ',', '%', '@', '`')
            or re.search(r':(?:[ \t]|$)|^[?:-](?:[ \t]|$)', text)):
        raise Unreadable('%s: unsupported YAML syntax %r' % (where, text))
    if text in ('', '~', 'null', 'Null', 'NULL'):
        return None
    if text in ('true', 'True', 'TRUE', 'false', 'False', 'FALSE'):
        return text.lower() == 'true'
    if re.fullmatch(DECIMAL, text):
        try:
            # Preserve DATA integer identities; expressions canonicalize them to binary64.
            value = int(text) if re.fullmatch(r'[+-]?[0-9]+', text) else float(text)
            expression_scalar(value)
        except (ValueError, Unknown) as error:
            raise Unreadable('%s: unsupported non-finite or out-of-range YAML number' % where) from error
        return value
    if (re.fullmatch(r'0x[0-9a-fA-F]+|0o[0-7]+', text)
            or re.fullmatch(DECIMAL + r'[eE][+-]?[0-9]+', text)
            or text in ('.inf', '.Inf', '.INF', '+.inf', '+.Inf', '+.INF',
                        '-.inf', '-.Inf', '-.INF', '.nan', '.NaN', '.NAN')):
        raise Unreadable('%s: unsupported YAML numeric form %r' % (where, text))
    return text


def parse_workflow_yaml(text):
    """Pure, fail-closed reader of the workflow's existing block YAML subset."""
    lines = text.split('\n')
    terminal_break = text.endswith('\n')
    if terminal_break:
        lines.pop()  # Do not treat the split's EOF sentinel as a physical empty line.
    pos = 0
    for line_number, line in enumerate(lines, 1):
        if '\u2028' in line or '\u2029' in line:
            raise Unreadable('%s:%d: unsupported raw YAML Unicode line break' % (WORKFLOW, line_number))
        if '\t' in line:
            raise Unreadable('%s:%d: unsupported YAML tab' % (WORKFLOW, line_number))
        if any(ord(char) < 32 and char != '\t' or 127 <= ord(char) <= 159
               or 0xD800 <= ord(char) <= 0xDFFF or ord(char) in (0xFFFE, 0xFFFF) for char in line):
            raise Unreadable('%s:%d: unsupported YAML control character' % (WORKFLOW, line_number))

    def indent(line):
        return len(line) - len(line.lstrip(' '))

    def skip():
        nonlocal pos
        while pos < len(lines) and (not lines[pos].strip(' \t') or lines[pos].lstrip(' ').startswith('#')):
            pos += 1

    def node(level):
        skip()
        if pos >= len(lines) or indent(lines[pos]) != level:
            raise Unreadable('%s:%d: unexpected indentation' % (WORKFLOW, pos + 1))
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
                raise Unreadable('%s:%d: unsupported sequence entry' % (WORKFLOW, pos + 1))
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
                raise Unreadable('%s: unsupported mapping entry' % where)
            key, value = match[1], (match[2] or '').strip(' \t')
            if not isinstance(_scalar(key, where), str):
                raise Unreadable('%s: unsupported non-string mapping key %r' % (where, key))
            if key in result:
                raise Unreadable('%s: duplicate key %s' % (where, key))
            pos += 1
            if value in ('|', '|-', '|+'):
                result[key] = block(level, value)
            elif not value or value.startswith('#'):
                skip()
                deeper = pos < len(lines) and indent(lines[pos]) > level
                result[key] = node(indent(lines[pos])) if deeper else None
            else:
                result[key] = _scalar(value, where)

    def block(level, header):
        nonlocal pos
        start = pos
        width = None
        while pos < len(lines) and not lines[pos].strip(' '):
            pos += 1
        if pos < len(lines) and indent(lines[pos]) > level:
            width = indent(lines[pos])
        if width is None:
            # All-empty blocks have only chomped trailing lines; keep only real breaks.
            return ''.join('\n' for index in range(start, pos)
                           if header == '|+' and (index < len(lines) - 1 or terminal_break))
        for index in range(start, pos):
            if len(lines[index]) > width:
                raise Unreadable('%s:%d: over-indented leading empty block line' % (WORKFLOW, index + 1))
        pos = start
        content = []
        while pos < len(lines):
            line = lines[pos]
            if line.strip(' '):
                if indent(line) <= level:
                    break
                if indent(line) < width:
                    raise Unreadable('%s:%d: under-indented block scalar' % (WORKFLOW, pos + 1))
            # Spaces beyond content indentation are data, including all-space lines.
            content.append((line[width:], pos < len(lines) - 1 or terminal_break))
            pos += 1
        if header != '|+':
            while content and content[-1][0] == '':
                content.pop()
        return ''.join(value + ('\n' if ended and (index < len(content) - 1 or header != '|-') else '')
                       for index, (value, ended) in enumerate(content))

    result = node(0)
    skip()
    if pos != len(lines):
        raise Unreadable('%s:%d: trailing content' % (WORKFLOW, pos + 1))
    if isinstance(result, dict) and isinstance(result.get('jobs'), dict):
        for name, job in result['jobs'].items():
            if isinstance(job, dict):
                matrix_include(job, '%s: job %s' % (WORKFLOW, name))
    return result


def matrix_include(job, where):
    """The shared include-only matrix boundary; axes/exclusions need explicit support."""
    if 'strategy' not in job:
        return None
    strategy = job['strategy']
    if not isinstance(strategy, dict):
        raise Unreadable('%s: strategy must be a mapping' % where)
    if 'matrix' not in strategy:
        return None
    matrix = strategy['matrix']
    if not isinstance(matrix, dict):
        raise Unreadable('%s: strategy.matrix must be a mapping' % where)
    if set(matrix) != {'include'}:
        raise Unreadable('%s: only strategy.matrix.include is supported' % where)
    rows = matrix['include']
    if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
        raise Unreadable('%s: strategy.matrix.include must be a list of mappings' % where)
    return rows


def parse_workflow(text):
    """Target-checker shape projection; DATA decoding is exclusively parse_workflow_yaml."""
    workflow = parse_workflow_yaml(text)
    if not isinstance(workflow, dict) or not isinstance(workflow.get('jobs'), dict):
        raise Unreadable(f'{WORKFLOW}: no top-level jobs')
    jobs = {}
    for name, job in workflow['jobs'].items():
        where = '%s: job %s' % (WORKFLOW, name)
        if not isinstance(job, dict):
            raise Unreadable('%s must be a mapping' % where)

        def mapping(value, field):
            if not isinstance(value, dict):
                raise Unreadable('%s: %s must be a mapping' % (where, field))
            return value

        env = mapping(job.get('env', {}), 'env')
        matrix = matrix_include(job, where)
        steps = job.get('steps', [])
        if not isinstance(steps, list):
            raise Unreadable('%s: steps must be a list of mappings' % where)
        for index, step in enumerate(steps):
            if not isinstance(step, dict):
                raise Unreadable('%s: step %d must be a mapping' % (where, index))
            mapping(step.get('env', {}), 'step %d env' % index)
        jobs[name] = {'runs-on': job.get('runs-on'), 'if': job.get('if'),
                      'env': env, 'matrix': matrix,
                      'steps': [{'name': None, 'if': None, 'run': '', 'env': {}, **step}
                                for step in steps]}
    return jobs


def runner_host(label):
    """GitHub-hosted runner label -> arch-os host, or None when it is not a fixed host."""
    if not isinstance(label, str):
        return None
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
        return bool(re.search(r'(?<![\w/.-])scripts/(floatprobe\.sh|abi-probe\.py observe|'
                              r'aarch64-abi\.py check)\b', run))
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
    label = job['runs-on']
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
        rows = selected_rows(job['matrix'], selector)
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


ABI_PROBE = 'scripts/aarch64-abi.py'
ABI_MODEL = 'tests/roadmap/aarch64-abi/Model.lean'


def job_context(jobs, job_name, selector, host=None):
    """(job, {matrix, runner.os} context, errors) for one job (and matrix row), on `host` if given."""
    job = jobs.get(job_name)
    if job is None:
        return None, None, [f'CI job {job_name!r} not found in {WORKFLOW}']
    label = job['runs-on']
    job_host = runner_host(label)
    if job_host is None or (host is not None and job_host != host):
        return None, None, [f'job {job_name!r} runs on {label!r} ({job_host}), not {host or "a fixed host"}']
    if job['matrix'] is None:
        if selector:
            return None, None, [f'job {job_name!r} has no matrix, but the entry selects a row']
        row = None
    else:
        rows = selected_rows(job['matrix'], selector)
        if len(rows) != 1:
            return None, None, [f'matrix selector {selector!r} matches {len(rows)} rows of job {job_name!r}']
        row = rows[0]
    context = {'matrix': row, 'runner.os': RUNNER_OS[job_host.split('-', 1)[1]]}
    try:
        if not condition(job['if'], context):
            return None, None, [f'job {job_name!r} does not run for this row']
    except Unknown as error:
        return None, None, [f'job condition: {error}']
    return job, context, []


def check_abi_profiles(root, matrix, jobs):
    """Errors and report rows of the T04 `abi_profiles` entries."""
    errors, rows, seen = [], [], set()
    for item in matrix.get('abi_profiles', []):
        triple, version, host = item.get('target_triple'), item.get('zig'), item.get('host')
        mode, expected = item.get('mode'), item.get('expected')
        pid = f'abi {version}/{triple}/{mode}'
        if not all(isinstance(v, str) and v for v in (triple, version, host, mode, expected)):
            errors.append(f'{pid}: needs zig, host, target_triple, mode and expected')
            continue
        if (version, triple, mode) in seen:
            errors.append(f'{pid}: duplicate entry')
        seen.add((version, triple, mode))
        if '-'.join(triple.split('-')[:2]) != host:
            errors.append(f'{pid}: target {triple} is not native to host {host}')
        if expected != f'tests/roadmap/aarch64-abi/expected/{version}/{triple}-{mode}.txt':
            errors.append(f'{pid}: expected file {expected} is not the versioned file of this profile')
        elif not (root/expected).is_file():
            errors.append(f'{pid}: expected file {expected} is missing')
        line = r'(?:[^\n]|\\\n)*'  # one shell command, with `\` line continuations
        for kind, pattern, on in (
                ('probe', rf'(?<![\w/.-]){re.escape(ABI_PROBE)} check\b{line}--target {re.escape(triple)}(?![\w-])', host),
                ('proof', rf'(?<![\w/.-]){re.escape(ABI_MODEL)} {re.escape(triple)}\s+(?:\\\n\s*)?'
                          rf'{re.escape(expected)}(?!\S)', None)):
            ref = item.get(kind) or {}
            job, context, found = job_context(jobs, ref.get('job'), ref.get('matrix'), on)
            errors += [f'{pid}: {kind}: {e}' for e in found]
            if job is None:
                continue
            steps = [s for s in job['steps'] if s['name'] == ref.get('step')]
            if len(steps) != 1:
                errors.append(f'{pid}: {kind} step {ref.get("step")!r}: '
                              f'{"not found in the job" if not steps else "the step name is not unique"}')
                continue
            step = steps[0]
            try:
                runs = condition(step['if'], context)
                bound = interpolate(expression_string({**job['env'], **step['env']}.get('AIR2LEAN_ZIG_VERSION', '')), context)
            except Unknown as error:
                errors.append(f'{pid}: {kind} step: {error}')
                continue
            if not runs:
                errors.append(f'{pid}: {kind} step {step["name"]!r}: its `if` is false for this row')
            if bound != version and (context['matrix'] or {}).get('zig') != version:
                errors.append(f'{pid}: {kind} step {step["name"]!r} is not bound to Zig {version}')
            if not re.search(pattern, step['run']):
                errors.append(f'{pid}: {kind} step {step["name"]!r}: its commands do not run the '
                              f'{"native probe and compare" if kind == "probe" else "profile model check"} for {triple}')
            if re.search(r'\|\|\s*true\b|set \+e\b', step['run']):
                errors.append(f'{pid}: {kind} step {step["name"]!r} ignores a failure')
        rows.append({'profile': f'{version}/{triple}/{mode}', 'host': host,
                     'probe_job': (item.get('probe') or {}).get('job'),
                     'proof_job': (item.get('proof') or {}).get('job')})
    return errors, rows


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
        env = {k: interpolate(expression_string(merged[k]), context) for k in BOUND_ENV if k in merged}
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
    """(errors, report rows, input-only profiles, ABI-only profile rows)."""
    root = Path(root)
    meta = load_json(root, 'compatibility.json')
    matrix = load_json(root, MAP)
    try:
        jobs = parse_workflow((root/WORKFLOW).read_text(encoding='utf-8'))
    except OSError as error:
        raise Unreadable(f'{WORKFLOW}: {error}')
    if matrix.get('schema') != SCHEMA:
        return [f'{MAP}: schema must be {SCHEMA!r}'], [], [], []
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
    abi_errors, abi_rows = check_abi_profiles(root, matrix, jobs)
    return errors + abi_errors, rows, sorted(input_only), abi_rows


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='action', required=True)
    run = sub.add_parser('check')
    run.add_argument('--root', type=Path, default=ROOT)
    run.add_argument('--strict', action='store_true', help='fail on any recorded gap')
    run.add_argument('--json', action='store_true')
    args = parser.parse_args(argv)
    try:
        errors, rows, input_only, abi_rows = check(args.root, args.strict)
    except (Unreadable, KeyError, TypeError, AttributeError) as error:
        # Malformed input shapes (a profile without a name, a non-object entry) are unreadable.
        print(f'target-matrix: {type(error).__name__}: {error}', file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({'ok': not errors, 'errors': errors, 'paths': rows,
                          'input_only_profiles': input_only, 'abi_profiles': abi_rows}, indent=2))
    else:
        for row in rows:
            gaps = f' (gaps: {", ".join(row["gaps"])})' if row['gaps'] else ''
            print(f'{row["status"]:8} {row["path"]} <- {row["job"]}{gaps}')
        for row in abi_rows:
            print(f'abi-only {row["profile"]} on {row["host"]} <- {row["probe_job"]} (probe), '
                  f'{row["proof_job"]} (proof)')
        for error in errors:
            print(f'error: {error}', file=sys.stderr)
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
