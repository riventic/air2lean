#!/usr/bin/env python3
"""Float-semantics labels for numerical theorems (docs/float-semantics.md).

Every user-stated theorem whose checked dependency closure reaches `ZigLean.Float` states
which semantics it concerns: `ieee` (the model's IEEE 754 operation semantics),
`compiler-rt@<zig versions>` (the ported compiler_rt helpers of those Zig versions) or
`abstract-spec` (format, rounding and value facts that select no operation semantics).
Every label also lists the target profiles (`targets`: `x86_64-linux`, `aarch64-macos`) whose
float rules it holds for (docs/floats.md §Targets). Labels live in
`assurance/float-semantics.json`. Every label concerns the Lean model only: a binary, native or
shipped-compiler correspondence claim is rejected.

`check` is the light source-level gate (no Lean build). `scripts/assumptions.py` applies
the same registry to the compiled declaration graph, and `check-report` rejects reports
or receipts that are unlabeled or that claim binary correspondence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import sys

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = Path('assurance/float-semantics.json')
SEMANTICS = ('ieee', 'compiler-rt', 'abstract-spec')
TARGETS = ('aarch64-macos', 'x86_64-linux')
AARCH64 = 'aarch64-macos'
# The model functions that only an aarch64 translation calls (docs/floats.md §Targets). A
# theorem that names one concerns aarch64 rules, so its label must list aarch64-macos. This is a
# source check: a theorem stated for one target reaches both targets' rules through the target
# detection (`floatopsTarget`) in its premise, so the dependency closure cannot decide it.
AARCH64_ONLY = frozenset('Zig.Float.' + n for n in (
    'softF80Chk', 'divXf3', 'divTruncXf3', 'divFloorXf3', 'fmaFused', 'fmaRtFused', 'sqrtF80ViaF64'))
CORRESPONDENCE = 'model'
NOT_CLAIMED = 'not_claimed'
FLOAT_MODULE = 'ZigLean.Float'
OPS_MODULE = 'ZigLean.Float.Ops'
RT_MODULE = 'ZigLean.Float.CompilerRt'
FLOAT, OPS, RT = 1, 2, 4
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*')
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9!?']*(\.[A-Za-z_][A-Za-z_0-9!?']*)*")
# Lean-generated companions of a declaration: equation, injectivity, sizeOf, sparse-case
# and abstracted proof lemmas. They are reported, but their parent states the claim.
PRIVATE = re.compile(r'^_private(?:\.[^.]+)*?\.0\.')
GENERATED_PART = re.compile(r'_(?:proof|simp|sparseCasesOn|auxLemma)(?:_\d+)*')
AUXILIARY = re.compile(r'(^|\.)(eq_\d+|eq_def|inj|injEq|sizeOf_spec|else_eq|ofNat_ctorIdx|ctorIdx_ofNat)$')
# Source-level float vocabulary (the light check only; the audit uses the checked graph).
FLOAT_WORDS = re.compile(r'\bZig\.F(?:16|32|64|80|128)\b|\bF(?:16|32|64|80|128)\b|\bFloat\b|'
                         r'\bFloatFmt\b|\bisNaN\b|\bisInf\b|\bisFinite\b|\btoRat\?')
RT_WORDS = re.compile(r'\b\w+Rt(?:016)?(?:Chk|LegacyChk)?\b')
A64_WORDS = re.compile(r'\b(?:' + '|'.join(n.removeprefix('Zig.Float.') for n in sorted(AARCH64_ONLY)) + r')\b')
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                         r"(theorem|lemma|example)\b\s*([^\s:({\[]*)")
# A claim witness command (`ZigLean/Witness.lean`) declares the theorem `T.nonvacuous` or `T.returns`.
WITNESS = re.compile(r"^(nonvacuity_witness|liveness_witness)\s+(\S+)")
WITNESS_SUFFIX = {'nonvacuity_witness': '.nonvacuous', 'liveness_witness': '.returns'}
BINARY_KEYS = ('binary_correspondence', 'native_correspondence')
NOT_ATTESTED_KEYS = ('native_adequacy', 'source_correspondence')
VERSION = re.compile(r'^\["(\d+\.\d+\.\d+)"\]\s*$')


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def pairs(items):
    result = {}
    for key, value in items:
        demand(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def supported_versions(root=ROOT):
    lines = (Path(root) / 'zig-patch/versions.toml').read_text().splitlines()
    return {m.group(1) for m in map(VERSION.match, lines) if m}


def label_text(entry):
    if entry['semantics'] == 'compiler-rt':
        return 'compiler-rt@' + ','.join(entry['zig_versions'])
    return entry['semantics']


def split_key(key):
    demand(isinstance(key, str) and key.count('::') == 1, 'invalid registry key: ' + repr(key))
    module, name = key.split('::')
    demand(bool(MODULE.fullmatch(module)) and bool(NAME.fullmatch(name)), 'invalid registry key: ' + key)
    return module, name


def label_entry(key, entry, versions):
    demand(isinstance(entry, dict), 'label must be an object: ' + key)
    demand(entry.get('correspondence') == CORRESPONDENCE,
           'unsupported binary-correspondence claim: ' + key + ' (labels concern the Lean model only)')
    semantics = entry.get('semantics')
    demand(semantics in SEMANTICS, 'unknown float semantics for ' + key + ': ' + repr(semantics))
    targets = entry.get('targets')
    demand(isinstance(targets, list) and targets and targets == sorted(set(targets))
           and set(targets) <= set(TARGETS), 'label needs sorted unique targets of ' + ', '.join(TARGETS) + ': ' + key)
    if semantics == 'compiler-rt':
        demand(set(entry) == {'semantics', 'zig_versions', 'targets', 'correspondence'}, 'invalid label fields: ' + key)
        chosen = entry['zig_versions']
        demand(isinstance(chosen, list) and chosen and all(isinstance(v, str) for v in chosen)
               and chosen == sorted(set(chosen), key=lambda v: tuple(map(int, v.split('.')))),
               'compiler-rt label needs sorted unique Zig versions: ' + key)
        demand(set(chosen) <= versions, 'compiler-rt label names an unsupported Zig version: ' + key)
    else:
        demand(set(entry) == {'semantics', 'targets', 'correspondence'}, 'invalid label fields: ' + key)
    return entry


def load_registry(path=None, root=ROOT):
    root = Path(root)
    path = root / REGISTRY if path is None else Path(path)
    raw = path.read_bytes()
    registry = json.loads(raw, object_pairs_hook=pairs)
    demand(isinstance(registry, dict) and set(registry) == {'schema_version', 'theorems', 'non_numerical', 'checks'}
           and registry['schema_version'] == 1, 'unsupported float-semantics registry schema')
    versions = supported_versions(root)
    for field in ('theorems', 'non_numerical', 'checks'):
        demand(isinstance(registry[field], dict), 'registry ' + field + ' must be an object')
    for key, entry in registry['theorems'].items():
        split_key(key)
        label_entry(key, entry, versions)
    for key, reason in registry['non_numerical'].items():
        split_key(key)
        demand(key not in registry['theorems'], 'theorem is both labeled and exempt: ' + key)
        demand(isinstance(reason, str) and reason.strip(), 'non-numerical exemption needs a reason: ' + key)
    for check, entry in registry['checks'].items():
        demand(isinstance(check, str) and check.endswith('.lean') and not Path(check).is_absolute()
               and '..' not in Path(check).parts, 'invalid check path: ' + repr(check))
        demand(isinstance(entry, dict) and set(entry) == {'labels', 'correspondence'}
               and entry['correspondence'] == CORRESPONDENCE,
               'unsupported binary-correspondence claim: ' + check + ' (labels concern the Lean model only)')
        labels = entry['labels']
        demand(isinstance(labels, list) and labels and labels == sorted(set(labels)), 'invalid check labels: ' + check)
        for label in labels:
            semantics, _, chosen = label.partition('@') if isinstance(label, str) else ('', '', '')
            body = {'semantics': semantics, 'targets': list(TARGETS), 'correspondence': CORRESPONDENCE}
            if chosen:
                body['zig_versions'] = chosen.split(',')
            demand(label_text(label_entry(check, body, versions)) == label, 'invalid check label: ' + repr(label))
    registry['sha256'] = hashlib.sha256(raw).hexdigest()
    return registry


def user_name(node):
    return node.get('user_name') or node['name']


def is_auxiliary(name):
    # `private` declarations are hand-written: drop Lean's `_private.<module>.0.` mangling first.
    name = PRIVATE.sub('', name)
    return bool(AUXILIARY.search(name)) or any(GENERATED_PART.fullmatch(part) for part in name.split('.'))


def own_flags(module):
    bits = FLOAT if module == FLOAT_MODULE or module.startswith(FLOAT_MODULE + '.') else 0
    if module == OPS_MODULE:
        bits |= OPS
    if module == RT_MODULE:
        bits |= RT
    return bits


def closure_flags(nodes):
    """Reachable float/ops/compiler-rt flags per declaration.

    Iterative Tarjan: components are emitted after every component they reach, so each
    component's flags are its members' own flags plus those of already-emitted successors.
    """
    index, low, on_stack, stack, component, flags = {}, {}, set(), [], {}, {}
    for start in nodes:
        if start in index:
            continue
        index[start] = low[start] = len(index)
        stack.append(start)
        on_stack.add(start)
        work = [(start, iter(nodes[start]['dependencies']))]
        while work:
            name, children = work[-1]
            for child in children:
                if child not in index:
                    index[child] = low[child] = len(index)
                    stack.append(child)
                    on_stack.add(child)
                    work.append((child, iter(nodes[child]['dependencies'])))
                    break
                if child in on_stack:
                    low[name] = min(low[name], index[child])
            else:
                work.pop()
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[name])
                if low[name] == index[name]:
                    members = []
                    while True:
                        member = stack.pop()
                        on_stack.discard(member)
                        members.append(member)
                        if member == name:
                            break
                    bits = 0
                    for member in members:
                        component[member] = name
                    for member in members:
                        bits |= own_flags(nodes[member]['module'])
                        for child in nodes[member]['dependencies']:
                            if component.get(child) != name:
                                bits |= flags[child]
                    for member in members:
                        flags[member] = bits
    return flags


def dependency_flags(node, flags):
    bits = 0
    for dependency in node['dependencies']:
        bits |= flags[dependency]
    return bits


def label_theorems(nodes, theorems, modules, registry):
    """Return per-theorem float records, policy issues and the report summary."""
    flags = closure_flags(nodes)
    issues, records, labels, generated = {}, {}, {}, 0
    present = {}
    for theorem in theorems:
        node = nodes[theorem['name']]
        present[theorem['module'] + '::' + user_name(node)] = theorem['name']

    def issue(name, module, trust, reason):
        issues.setdefault(name, {'name': name, 'module': module, 'trust_class': trust, 'reason': reason})

    for theorem in theorems:
        name, module = theorem['name'], theorem['module']
        node = nodes[name]
        user = user_name(node)
        key = module + '::' + user
        bits = dependency_flags(node, flags)
        numerical = bool((bits | own_flags(module)) & FLOAT)
        if key in registry['non_numerical']:
            if numerical:
                issue(name, module, 'float-semantics-mismatch', 'exempt theorem depends on the float model')
            continue
        if not numerical:
            if key in registry['theorems']:
                issue(name, module, 'stale-float-semantics-label', 'labeled theorem does not depend on the float model')
            continue
        if is_auxiliary(user) and key not in registry['theorems']:
            generated += 1
            records[name] = {'scope': 'compiler-generated', 'correspondence': CORRESPONDENCE,
                             'binary_correspondence': NOT_CLAIMED}
            continue
        entry = registry['theorems'].get(key)
        if entry is None:
            issue(name, module, 'unlabeled-numerical-theorem',
                  'numerical theorem lacks a float-semantics label (assurance/float-semantics.json)')
            continue
        semantics = entry['semantics']
        if bits & RT and semantics != 'compiler-rt':
            issue(name, module, 'float-semantics-mismatch', 'depends on compiler-rt helper ports but is labeled ' + semantics)
        elif semantics == 'compiler-rt' and not bits & RT:
            issue(name, module, 'float-semantics-mismatch', 'compiler-rt label without a compiler-rt helper dependency')
        elif semantics == 'abstract-spec' and bits & (OPS | RT):
            issue(name, module, 'float-semantics-mismatch', 'abstract-spec label but depends on float operation semantics')
        text = label_text(entry)
        labels[text] = labels.get(text, 0) + 1
        record = {'scope': 'stated', 'label': text, 'semantics': semantics, 'targets': entry['targets']}
        if semantics == 'compiler-rt':
            record['zig_versions'] = entry['zig_versions']
        records[name] = dict(record, correspondence=CORRESPONDENCE, binary_correspondence=NOT_CLAIMED)
    for kind in ('theorems', 'non_numerical'):
        for key in registry[kind]:
            module, _ = split_key(key)
            if module in modules and key not in present:
                issue(key, module, 'stale-float-semantics-label', 'registry names no checked theorem')
    summary = {'schema_version': 1, 'registry_sha256': registry['sha256'],
               'numerical_theorems': sum(labels.values()), 'compiler_generated': generated,
               'labels': dict(sorted(labels.items())), 'correspondence': CORRESPONDENCE,
               'binary_correspondence': NOT_CLAIMED}
    return records, issues, summary


# ---------------------------------------------------------------------------------------
# Light source-level check (no Lean build).

SCANNED = ('ZigLean', 'Proofs', 'tests', 'tutorials', 'case-studies', 'examples')


def lean_files(root):
    """Lean sources that can state theorems (not goldens, caches or compiler checkouts)."""
    root = Path(root)
    for top in SCANNED:
        for path in sorted((root / top).rglob('*.lean')):
            relative = path.relative_to(root)
            if any(part.startswith('.') for part in relative.parts) or relative.parts[:2] == ('tests', 'golden'):
                continue
            yield relative


def declarations(text):
    """Yield (kind, full name, declaration text). Tracks `namespace`/`section` nesting."""
    lines = text.splitlines()
    scopes = []
    i = 0
    while i < len(lines):
        line = lines[i]
        words = line.split()
        if words[:1] == ['namespace'] and len(words) == 2:
            scopes.append(('namespace', words[1]))
        elif words[:1] == ['section'] or words[:2] == ['noncomputable', 'section']:
            scopes.append(('section', words[-1] if words[-1] != 'section' else ''))
        elif words == ['mutual']:
            scopes.append(('mutual', ''))  # Its `end` must not close the enclosing namespace.
        elif words[:1] == ['end'] and scopes:
            scopes.pop()
        match = DECLARATION.match(line)
        witness = WITNESS.match(line)
        if not match and not witness:
            i += 1
            continue
        j = i + 1
        while j < len(lines) and (not lines[j] or lines[j][0].isspace()):
            j += 1
        if witness:
            kind, declared = 'theorem', witness.group(2) + WITNESS_SUFFIX[witness.group(1)]
        else:
            kind, declared = match.groups()
        body = '\n'.join(lines[i:j])
        if kind == 'example':
            yield kind, None, body
        else:
            prefix = [] if declared.startswith('_root_.') else [n for k, n in scopes if k == 'namespace']
            yield kind, '.'.join(prefix + [declared.removeprefix('_root_.')]), body
        i = j


def generated_mode(root, module):
    """Float semantics selected for a `Proofs.<Ex>` module's translation, if any."""
    parts = module.split('.')
    if parts[0] != 'Proofs' or len(parts) < 3:
        return None
    gen = Path(root) / 'Proofs' / parts[1] / 'Gen.lean'
    if gen.is_file():
        first = gen.read_bytes().partition(b'\n')[0]
        if first.startswith(b'-- air2lean-profile: '):
            metadata = json.loads(first[len(b'-- air2lean-profile: '):], object_pairs_hook=pairs)
            demand(metadata.get('correspondence') == CORRESPONDENCE,
                   'generated code claims unsupported correspondence: ' + str(gen))
            return metadata.get('float_semantics')
    args = Path(root) / 'examples' / parts[1].lower() / 'translate.args'
    tokens = shlex.split(args.read_text()) if args.is_file() else []
    for i, token in enumerate(tokens):
        if token == '--float-semantics' and i + 1 < len(tokens):
            return tokens[i + 1]
        if token.startswith('--float-semantics='):
            return token.split('=', 1)[1]
    return 'ieee'


def check_sources(root=ROOT, registry=None):
    """Return source-level problems: unlabeled float theorems, stale labels, mode conflicts."""
    root = Path(root)
    registry = load_registry(root=root) if registry is None else registry
    problems, declared, checks_seen = [], set(), set()
    labeled = set(registry['theorems']) | set(registry['non_numerical'])
    for relative in lean_files(root):
        shipped = relative.parts[0] in ('ZigLean', 'Proofs')
        module = '.'.join(relative.with_suffix('').parts)
        in_float_library = relative.parts[:2] == ('ZigLean', 'Float')
        text = (root / relative).read_text()
        for kind, name, body in declarations(text):
            candidate = in_float_library or bool(FLOAT_WORDS.search(body))
            if not shipped:
                if candidate:
                    checks_seen.add(relative.as_posix())
                    check = registry['checks'].get(relative.as_posix())
                    if check is None:
                        problems.append(f'{relative}: float {kind} ({name or body.splitlines()[0][:60]}) '
                                        'in a check without float-semantics labels')
                    elif RT_WORDS.search(body) and not any(l.startswith('compiler-rt@') for l in check['labels']):
                        problems.append(f'{relative}: compiler-rt helper used but no compiler-rt label listed')
                continue
            if kind == 'example':
                if candidate:
                    problems.append(f'{relative}: anonymous float example in a shipped module cannot be labeled')
                continue
            key = module + '::' + name
            declared.add(key)
            if candidate and key not in labeled:
                problems.append(f'{key}: numerical theorem lacks a float-semantics label')
            entry = registry['theorems'].get(key)
            if entry and A64_WORDS.search(body) and AARCH64 not in entry['targets']:
                problems.append(f'{key}: uses an aarch64-only float rule but its label omits {AARCH64}')
    for key in sorted(labeled - declared):
        # A test module's theorem is named by its `lean -R` module (`BigEndian.Proofs::…`), which
        # this scan does not resolve; the compiled theorem-universe audit (F2) labels it and
        # reports a stale label.
        if not key.startswith(('ZigLean.', 'Proofs.')):
            continue
        problems.append(f'{key}: registry names no declared theorem')
    for check in sorted(registry['checks']):
        if check not in checks_seen:
            problems.append(f'{check}: listed check has no float example or theorem')
    modes = {}
    for key, entry in sorted(registry['theorems'].items()):
        module, _ = split_key(key)
        if module not in modes:
            modes[module] = generated_mode(root, module)
        mode = modes[module]
        if entry['semantics'] == 'compiler-rt' and mode not in (None, 'compiler-rt'):
            problems.append(f'{key}: compiler-rt label but the translation selects {mode}')
    return problems


# ---------------------------------------------------------------------------------------
# Report and receipt check.

def report_problems(report, registry=None, root=ROOT):
    """Problems in an assumption report or proof receipt: missing labels or claims."""
    problems = []

    def scan(value, where):
        if isinstance(value, dict):
            for key, item in value.items():
                here = where + '.' + key
                if key in BINARY_KEYS and item != NOT_CLAIMED:
                    problems.append(f'{here}: unsupported binary/native correspondence claim {item!r}')
                elif key in NOT_ATTESTED_KEYS and item != 'not_attested':
                    problems.append(f'{here}: unsupported correspondence claim {item!r}')
                elif key == 'correspondence' and item != CORRESPONDENCE:
                    problems.append(f'{here}: unsupported correspondence claim {item!r}')
                scan(item, here)
        elif isinstance(value, list):
            for position, item in enumerate(value):
                scan(item, f'{where}[{position}]')

    scan(report, '$')
    summary = report.get('float_semantics') if isinstance(report, dict) else None
    if not isinstance(summary, dict):
        problems.append('$.float_semantics: missing float-semantics summary')
    elif summary.get('binary_correspondence') != NOT_CLAIMED:
        problems.append('$.float_semantics: binary correspondence must be not_claimed')
    if isinstance(report, dict) and isinstance(report.get('theorems'), list):
        stated = 0
        for theorem in report['theorems']:
            record = theorem.get('float_semantics') if isinstance(theorem, dict) else None
            if record is None:
                continue
            if record.get('scope') == 'stated':
                stated += 1
                if not isinstance(summary, dict) or record.get('label') not in summary.get('labels', {}):
                    problems.append(f"{theorem.get('name')}: float-semantics label absent from summary")
            elif record.get('scope') != 'compiler-generated':
                problems.append(f"{theorem.get('name')}: invalid float-semantics record")
        if isinstance(summary, dict) and summary.get('numerical_theorems') != stated:
            problems.append('$.float_semantics: numerical theorem count differs from labeled theorems')
        if isinstance(report.get('nodes'), list) and isinstance(summary, dict):
            registry = load_registry(root=root) if registry is None else registry
            nodes = {node['name']: node for node in report['nodes']}
            records, issues, fresh = label_theorems(nodes, report['theorems'], set(report.get('modules', [])), registry)
            for theorem in report['theorems']:
                if theorem.get('float_semantics') != records.get(theorem['name']):
                    problems.append(f"{theorem['name']}: float-semantics record differs from the checked graph")
            for item in issues.values():
                problems.append(f"{item['name']}: {item['reason']}")
            if fresh != summary:
                problems.append('$.float_semantics: summary differs from the checked graph and registry')
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='action', required=True)
    check = sub.add_parser('check', help='light source-level label check (no build)')
    check.add_argument('--root', type=Path, default=ROOT)
    reports = sub.add_parser('check-report', help='reject unlabeled or binary-claiming reports/receipts')
    reports.add_argument('reports', nargs='+', type=Path)
    reports.add_argument('--root', type=Path, default=ROOT)
    reports.add_argument('--float-semantics', type=Path, dest='registry',
                         help='label registry the reports were audited with (default: assurance/float-semantics.json)')
    args = parser.parse_args(argv)
    try:
        if args.action == 'check':
            problems = check_sources(args.root)
        else:
            registry = load_registry(args.registry, root=args.root)
            problems = []
            for path in args.reports:
                report = json.loads(path.read_text(), object_pairs_hook=pairs)
                problems += [f'{path}: {p}' for p in report_problems(report, registry, args.root)]
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'float semantics error: {error}', file=sys.stderr)
        return 2
    for problem in problems:
        print('float semantics: ' + problem, file=sys.stderr)
    if problems:
        return 1
    print('float semantics labels: ok', file=sys.stderr)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
