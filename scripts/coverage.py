#!/usr/bin/env python3
"""Compiler-source inventory. Source evidence never implies verified support."""
import argparse
from collections import Counter
import hashlib
from functools import lru_cache
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FORMAT = 1


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tokens(text):
    """Zig lexical tokens, ignoring comments and preserving escaped identifiers."""
    pattern = r'//[^\n]*|/\*[\s\S]*?\*/|@"(?:\\.|[^"\\])*"|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_][A-Za-z_0-9]*|=>|[^\s]'
    return [m.group() for m in re.finditer(pattern, text)
            if not m.group().startswith(('//', '/*'))]


def identifier(token):
    if token.startswith('@"'):
        return json.loads(token[1:])
    if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', token):
        return token
    raise ValueError(f'expected identifier, got {token!r}')


def balanced(ts, start):
    pairs = {'{': '}', '(': ')', '[': ']'}
    stack = []
    for i in range(start, len(ts)):
        t = ts[i]
        if t in pairs:
            stack.append(pairs[t])
        elif t in pairs.values():
            if not stack or stack.pop() != t:
                raise ValueError('unbalanced Zig declaration')
            if not stack:
                return i
    raise ValueError('unterminated Zig declaration')


def declaration(text, name, kind):
    ts = tokens(text)
    matches = [i for i in range(len(ts) - 4)
               if ts[i:i+3] == ['const', name, '='] and ts[i+3] == kind]
    if len(matches) != 1:
        raise ValueError(f'expected exactly one const {name} = {kind}, got {len(matches)}')
    start = matches[0] + 4
    if ts[start] == '(':
        start = balanced(ts, start) + 1
    if ts[start] != '{':
        raise ValueError(f'{name}: expected declaration body')
    return ts[start+1:balanced(ts, start)]


def members(text, name, kind):
    """Read every top-level field; skip declarations, reject unfamiliar syntax."""
    body = declaration(text, name, kind)
    result = []
    i = 0
    while i < len(body):
        if body[i] in ('pub', 'const', 'fn', 'test', 'comptime', 'usingnamespace'):
            # Once enum methods/nested declarations begin, consume the declaration.
            while i < len(body) and body[i] not in (';', '{'):
                if body[i] in ('(', '['):
                    i = balanced(body, i)
                i += 1
            if i == len(body):
                raise ValueError(f'{name}: incomplete nested declaration')
            if body[i] == '{':
                i = balanced(body, i)
            i += 1
            if i < len(body) and body[i] == ';':
                i += 1
            continue
        field = identifier(body[i])
        i += 1
        if i < len(body) and body[i] not in (',', ':', '='):
            raise ValueError(f'{name}: unexpected syntax after {field}')
        while i < len(body) and body[i] != ',':
            if body[i] in ('{', '(', '['):
                i = balanced(body, i)
            i += 1
        if i == len(body):
            raise ValueError(f'{name}: field {field} missing comma')
        i += 1
        if field != '_':
            result.append(field)
    if not result or len(result) != len(set(result)):
        raise ValueError(f'{name}: empty or duplicate fields')
    return result


def function_body(text, name):
    ts = tokens(text)
    starts = [i for i in range(len(ts)-2) if ts[i:i+2] == ['fn', name]]
    if len(starts) != 1:
        raise ValueError(f'expected one function {name}')
    i = starts[0] + 2
    while i < len(ts):
        if ts[i] == '(':
            i = balanced(ts, i) + 1
        elif ts[i] == '{':
            return ts[i+1:balanced(ts, i)]
        else:
            i += 1
    raise ValueError(f'missing body {name}')


def switch_arms(ts, expression, occurrence=0):
    starts = [i for i in range(len(ts)) if ts[i:i+len(expression)+3] == ['switch', '('] + expression + [')']]
    if occurrence >= len(starts):
        raise ValueError(f'missing switch {expression}')
    start = starts[occurrence]+len(expression)+3
    if ts[start] != '{':
        raise ValueError('switch without body')
    body = ts[start+1:balanced(ts, start)]
    arms = {}
    i = 0
    while i < len(body):
        labels = []
        while body[i] != '=>':
            if body[i] == '.':
                labels.append(identifier(body[i+1])); i += 2
            elif body[i] == 'else':
                labels.append('*'); i += 1
            elif body[i] == ',':
                i += 1
            else:
                raise ValueError(f'unrecognized switch label {body[i]}')
        i += 1
        begin = i
        while i < len(body) and body[i] != ',':
            if body[i] in ('(', '{', '['):
                i = balanced(body, i)
            i += 1
        for label in labels:
            if label in arms:
                raise ValueError(f'duplicate switch label {label}')
            arms[label] = body[begin:i]
        i += 1
    return arms


def normalizer(text):
    section = text.split('  match raw.tag with', 1)[1].split('\n/--', 1)[0]
    matches = list(re.finditer(r'^  \| ((?:"[^"\n]+"\s*(?:\|\s*)?)+)=>', section, re.M))
    result = {}
    for n, match in enumerate(matches):
        next_arm = re.search(r'^  \| ', section[match.end():], re.M)
        end = match.end() + next_arm.start() if next_arm else len(section)
        branch = section[match.end():end]
        # Constructor references are an index for reviewer inspection, not a semantics proof.
        ops = sorted(set(a or b for a, b in re.findall(r'\breturn\s+\.(?:«([^»]+)»|([A-Za-z][A-Za-z0-9]*))', branch)))
        for tag in re.findall(r'"([^"\n]+)"', match.group(1)):
            result[tag] = ops
    return result


@lru_cache(maxsize=None)
def read_source(path):
    return path.read_text()


def source_hits(paths, symbol):
    pattern = re.compile(r'(?<![A-Za-z0-9_])' + re.escape(symbol) + r'(?![A-Za-z0-9_])')
    return [str(p.relative_to(ROOT)) for p in paths if pattern.search(read_source(p))]


def model_inventory(text):
    entries = []
    for fn in ('allocFn?', 'threadFn?', 'rejectedThreadFn?'):
        start = text.index('def '+fn)
        end = text.find('\n/--', start)
        section = text[start:end if end >= 0 else len(text)]
        for name in sorted(set(re.findall(r'"((?:mem\.Allocator|Thread|Io|time)\.[^"\n]+)"', section))):
            if ' ' not in name:
                entries.append({'name': name, 'recognizer': fn,
                                'disposition': 'translation-rejected' if fn == 'rejectedThreadFn?' else 'recognized-model-boundary',
                                'qualification': 'source-only; contracts and target/version restrictions require docs/std-models.md and Check.lean review'})
    return entries


def compiler_inventory(source):
    specs = [('air_tags', 'src/Air.zig', 'Tag', 'enum'),
             ('types', 'lib/std/builtin.zig', 'Type', 'union'),
             ('intern_keys', 'src/InternPool.zig', 'Key', 'union'),
             ('pointer_bases', 'src/InternPool.zig', 'BaseAddr', 'union')]
    out, hashes = {}, {}
    for category, relative, name, kind in specs:
        p = source / relative
        hashes[relative] = digest(p)
        out[category] = members(p.read_text(), name, kind)
    # Additional compiler surfaces for upgrade impact. Missing version-specific
    # files are recorded explicitly; these are not a full source closure.
    for relative in ('src/Type.zig', 'src/Value.zig', 'src/Sema.zig',
                     'src/codegen/llvm.zig', 'lib/std/mem/Allocator.zig',
                     'lib/std/Thread.zig', 'lib/std/Io.zig', 'lib/std/time.zig'):
        p = source / relative
        hashes[relative] = digest(p) if p.is_file() else None
    return out, hashes


def generate(version, source):
    universe, fingerprints = compiler_inventory(source)
    exporter = (ROOT/'zig-patch/air-json/json.zig').read_text()
    decode = switch_arms(function_body(exporter, 'writeInst'), ['tag'], 1)
    type_arms = switch_arms(function_body(exporter, 'writeTypeEntry'), ['ty', '.', 'zigTypeTag', '(', 'zcu', ')'])
    norms = normalizer((ROOT/'Air2Lean/Air/Normalize.lean').read_text())
    semantic_paths = sorted((ROOT/'ZigLean').rglob('*.lean'))
    emit_paths = [ROOT/'Air2Lean/Emit.lean']
    proof_paths = sorted((ROOT/'Proofs').rglob('*.lean'))
    # Parse actual golden JSON; malformed fixture is not silently evidence.
    test_tags = {}
    for p in sorted((ROOT/'tests/golden'/version).rglob('*.json')):
        data = json.loads(p.read_text())
        def visit(value):
            if isinstance(value, dict):
                tag = value.get('tag')
                if isinstance(tag, str) and type(value.get('id')) is int:
                    test_tags.setdefault(tag, set()).add(str(p.relative_to(ROOT)))
                for child in value.values(): visit(child)
            elif isinstance(value, list):
                for child in value: visit(child)
        visit(data)
    tags = []
    for tag in universe['air_tags']:
        arm = decode.get(tag)
        if arm is None:
            export_status = 'fallback-unclassified'
            export_reason = 'No explicit writeInst switch arm; inspect Compat and fallback. Do not infer rejection or decoding.'
        elif '"unsupported"' in arm:
            export_status = 'conditional-or-rejected'
            export_reason = 'Arm can write unsupported; review version and data conditions.'
        else:
            export_status = 'explicit-arm'
            export_reason = 'Explicit source arm found; operand correctness and nested helper conditions are unverified.'
        if tag.endswith('_optimized'):
            disposition = 'normalizer-rejected-fast-math'
        elif tag not in norms and not tag.startswith('call'):
            disposition = 'normalizer-unclassified-or-unknown'
        elif export_status != 'explicit-arm':
            disposition = 'conditional-pipeline-review-required'
        else:
            disposition = 'source-pipeline-candidate-unqualified'
        ops = norms.get(tag, ['call'] if tag.startswith('call') else [])
        tags.append({'tag': tag, 'disposition': disposition,
                     'exporter': {'status': export_status, 'reason': export_reason},
                     'normalization': {'status': 'explicit-source-branch' if tag in norms else 'call-prefix-branch' if tag.startswith('call') else 'no-explicit-source-branch', 'constructors': ops},
                     'parser': {'status': 'generic-schema-source-only', 'paths': ['Air2Lean/Air/Json.lean', 'Air2Lean/Air/Canon.lean']},
                     'checker': {'status': 'conditional-type-and-layout-review-required', 'paths': ['Air2Lean/Check.lean']},
                     'semantics': {'status': 'symbol-index-only', 'paths': sorted(set(p for op in ops for p in source_hits(semantic_paths, op)))},
                     'emission': {'status': 'symbol-index-only', 'paths': sorted(set(p for op in ops for p in source_hits(emit_paths, op)))},
                     'tests': {'status': 'golden-input-presence-only', 'paths': sorted(test_tags.get(tag, []))},
                     'proofs': {'status': 'symbol-index-only-not-proof-coverage', 'paths': sorted(set(p for op in ops for p in source_hits(proof_paths, op)))},
                     'guidance': 'Inspect exporter/Compat, normalizeOp, checker restrictions and emitted runtime calls; add compiler fixture, rejection and differential tests and checked contract before qualification.'})
    type_rows = [{'name': name, 'disposition': 'exporter-arm-conditional-checker-review' if name in type_arms else 'exporter-fallback-unclassified',
                  'qualification': 'Type/layout/value restrictions require Check.lean; an arm is not full type support.'}
                 for name in universe['types']]
    constants = [{'name': name, 'kind': 'type-key' if name.endswith('_type') else 'value-or-internal-key',
                  'disposition': 'unclassified-review-writeRef-and-Check',
                  'qualification': 'InternPool keys include internal/comptime entries; no claim all can reach executable AIR.'}
                 for name in universe['intern_keys']]
    bases = [{'name': name, 'disposition': 'conditional-global-resolution' if name in ('nav', 'uav', 'field') else 'exporter-unsupported-base',
              'qualification': 'writePtr and Check.lean restrict global provenance and packed field resolution.'}
             for name in universe['pointer_bases']]
    scopes = {'inventory-tool': ['scripts/coverage.py', 'zig-patch/versions.toml'], 'translation': ['Air2Lean', 'zig-patch/air-json'], 'runtime-models': ['ZigLean'],
              'proof-sources': ['Proofs'], 'qualification-probes': ['scripts/floatprobe.sh', 'tests/diff', 'tests/golden'],
              'model-boundaries': ['Air2Lean/Memory.lean', 'docs/std-models.md']}
    project_hashes = {}
    for scope, roots in scopes.items():
        entries = {}
        for relative in roots:
            p = ROOT/relative
            paths = sorted(p.rglob('*')) if p.is_dir() else [p]
            for item in paths:
                if item.is_file(): entries[str(item.relative_to(ROOT))] = digest(item)
        project_hashes[scope] = entries
    return {'format': FORMAT, 'zig_version': version,
            'evidence_level': 'source-inventory; no compiler execution, proof checking or support qualification',
            'compiler_source_sha256': fingerprints, 'universe': universe,
            'tags': tags, 'types': type_rows, 'constants': constants, 'pointer_bases': bases,
            'models': model_inventory((ROOT/'Air2Lean/Memory.lean').read_text()),
            'project_source_sha256': project_hashes,
            'summary': dict(Counter(row['disposition'] for row in tags))}


def changes(before, after):
    report = {'from': before['zig_version'], 'to': after['zig_version'], 'universes': {}, 'source_changes': {},
              'required_qualification': ['Review AIR/exporter operands and compiler lowering; new and renamed tags require explicit dispositions.',
                                         'Rerun target layout and float probes and differential fixtures for qualified profiles.',
                                         'Review std recognition and model contracts; rerun affected generated translations.',
                                         'Rebuild affected proofs and compare kernel dependency reports; this command does not discharge these obligations.']}
    for category in sorted(set(before['universe']) | set(after['universe'])):
        old, new = set(before['universe'].get(category, [])), set(after['universe'].get(category, []))
        report['universes'][category] = {'added': sorted(new-old), 'removed': sorted(old-new), 'rename_policy': 'renames appear as removal plus addition; never auto-matched'}
    for scope in sorted(set(before['project_source_sha256']) | set(after['project_source_sha256'])):
        old, new = before['project_source_sha256'].get(scope, {}), after['project_source_sha256'].get(scope, {})
        report['source_changes'][scope] = [p for p in sorted(set(old)|set(new)) if old.get(p) != new.get(p)]
    old_compiler, new_compiler = before['compiler_source_sha256'], after['compiler_source_sha256']
    report['compiler_source_changes'] = [p for p in sorted(set(old_compiler) | set(new_compiler)) if old_compiler.get(p) != new_compiler.get(p)]
    report['compiler_sources_changed'] = bool(report['compiler_source_changes'])
    report['model_recognition_changed'] = before['models'] != after['models']
    report['model_boundary_changed'] = report['model_recognition_changed'] or bool(report['source_changes'].get('model-boundaries')) or any(p.startswith('lib/std/') and p != 'lib/std/builtin.zig' for p in report['compiler_source_changes'])
    report['tag_dispositions_changed'] = [tag for tag in sorted(set(r['tag'] for r in before['tags']) | set(r['tag'] for r in after['tags']))
                                          if next((r for r in before['tags'] if r['tag'] == tag), None) != next((r for r in after['tags'] if r['tag'] == tag), None)]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('generate', 'check'):
        p = sub.add_parser(name)
        p.add_argument('--version', required=True)
        p.add_argument('--source', type=Path, required=True, help='compiler source root; no compiler is invoked')
        p.add_argument('--inventory', type=Path, required=True)
    p = sub.add_parser('diff')
    p.add_argument('before', type=Path); p.add_argument('after', type=Path)
    p.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.command == 'diff':
        result = changes(json.loads(args.before.read_text()), json.loads(args.after.read_text()))
        output = json.dumps(result, indent=2)+'\n'
        if args.output: args.output.write_text(output)
        else: print(output, end='')
        return 0
    result = generate(args.version, args.source)
    if args.command == 'generate':
        args.inventory.parent.mkdir(parents=True, exist_ok=True)
        args.inventory.write_text(json.dumps(result, indent=2)+'\n')
        print(f'{args.version}: {len(result["tags"])} AIR tags, {len(result["types"])} type tags, {len(result["constants"])} intern keys, {len(result["pointer_bases"])} pointer bases; source evidence only')
        return 0
    old = json.loads(args.inventory.read_text())
    if old != result:
        print(json.dumps(changes(old, result), indent=2))
        print('Inventory stale. Review changes and regenerate only after recording upgrade qualification obligations.', file=sys.stderr)
        return 1
    print(f'{args.version}: inventory current (source evidence only)')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError, IndexError) as error:
        print(f'coverage: {error}', file=sys.stderr)
        sys.exit(2)
