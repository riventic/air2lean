#!/usr/bin/env python3
"""Compiler-source inventory. Source evidence never implies verified support."""
import argparse
from collections import Counter
import hashlib
from functools import lru_cache
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FORMAT = 1


class SourceCache:
    """One generation's consistent file bytes, decoded text, tokens and hashes."""
    def __init__(self):
        self.bytes = {}
        self.texts = {}
        self.token_lists = {}
        self.hashes = {}

    def data(self, path):
        if path not in self.bytes:
            self.bytes[path] = path.read_bytes()
        return self.bytes[path]

    def text(self, path):
        if path not in self.texts:
            self.texts[path] = self.data(path).decode('utf-8')
        return self.texts[path]

    def tokens(self, path):
        if path not in self.token_lists:
            self.token_lists[path] = tokens(self.text(path))
        return self.token_lists[path]

    def digest(self, path):
        if path not in self.hashes:
            self.hashes[path] = hashlib.sha256(self.data(path)).hexdigest()
        return self.hashes[path]


def tokens(text):
    """Zig lexical tokens, ignoring comments and preserving escaped identifiers."""
    if isinstance(text, list):
        return text
    pattern = r'//[^\n]*|/\*[\s\S]*?\*/|@"(?:\\.|[^"\\])*"|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_][A-Za-z_0-9]*|=>|[^\s]'
    return [m.group() for m in re.finditer(pattern, text)
            if not m.group().startswith(('//', '/*'))]


def identifier(token):
    if token.startswith('@"'):
        # Zig string escapes are byte escapes, not JSON's escape language.
        body = token[2:-1]
        data = bytearray()
        i = 0
        escapes = {'n': b'\n', 'r': b'\r', 't': b'\t', '\\': b'\\', "'": b"'", '"': b'"'}
        while i < len(body):
            if body[i] != '\\':
                data.extend(body[i].encode('utf-8')); i += 1
                continue
            i += 1
            if i >= len(body):
                raise ValueError('unterminated Zig identifier escape')
            escape = body[i]; i += 1
            if escape in escapes:
                data.extend(escapes[escape])
            elif escape == 'x':
                digits = body[i:i+2]
                if not re.fullmatch(r'[0-9a-fA-F]{2}', digits):
                    raise ValueError('invalid Zig byte escape')
                data.append(int(digits, 16)); i += 2
            elif escape == 'u':
                match = re.match(r'\{([0-9a-fA-F]{1,6})\}', body[i:])
                if not match:
                    raise ValueError('invalid Zig Unicode escape')
                scalar = int(match.group(1), 16)
                if scalar > 0x10ffff or 0xd800 <= scalar <= 0xdfff:
                    raise ValueError('invalid Unicode scalar in Zig identifier')
                data.extend(chr(scalar).encode('utf-8')); i += match.end()
            else:
                raise ValueError(f'invalid Zig identifier escape {escape!r}')
        try:
            return data.decode('utf-8')
        except UnicodeDecodeError as error:
            raise ValueError('invalid UTF-8 in Zig identifier') from error
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
    for match in matches:
        next_arm = re.search(r'^  \| ', section[match.end():], re.M)
        end = match.end() + next_arm.start() if next_arm else len(section)
        branch = section[match.end():end]
        # Constructor references are an index for reviewer inspection, not a semantics proof.
        ops = sorted(set(a or b for a, b in re.findall(r'\breturn\s+\.(?:«([^»]+)»|([A-Za-z][A-Za-z0-9]*))', branch)))
        for tag in re.findall(r'"([^"\n]+)"', match.group(1)):
            result[tag] = ops
    return result


def runtime_tag_reasons(text):
    """Source-only rejection policy shared with the translator, not feature support.

    Actual per-version enum membership is supplied by compiler_inventory.
    """
    section = text.split('def runtimeTagReason?', 1)[1].split('\nprivate def', 1)[0]
    arms = re.finditer(r'^  \| ((?:"[^"\n]+"\s*(?:\|\s*)?)+)=> some ("[^"\n]+")$', section, re.M)
    return {tag: json.loads(match.group(2)) for match in arms
            for tag in re.findall(r'"([^"\n]+)"', match.group(1))}


def source_hits(paths, symbol, cache):
    pattern = re.compile(r'(?<![A-Za-z0-9_])' + re.escape(symbol) + r'(?![A-Za-z0-9_])')
    return [str(p.relative_to(ROOT)) for p in paths if pattern.search(cache.text(p))]


def golden_paths(version, os_name):
    """Mirror check.sh shared → version → OS overlays, including anon groups."""
    selected = []
    for example in sorted((ROOT/'examples').iterdir()):
        if not example.is_dir():
            continue
        versions = example/'zig-versions'
        if versions.is_file() and version not in versions.read_text().splitlines():
            continue
        groups = {}
        for directory in (ROOT/'tests/golden'/example.name/'air',
                          ROOT/'tests/golden'/version/example.name/'air',
                          ROOT/'tests/golden'/version/example.name/('air-'+os_name)):
            layer = {}
            for path in sorted(directory.glob('*.json')):
                name = re.sub(r'__anon_[0-9]+', '__anon_N', path.name)
                layer.setdefault(name, []).append(path)
            groups.update(layer)  # Later layer replaces every instance of a name.
        selected.extend(path for group in groups.values() for path in group)
    return sorted(selected)


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


def exact_file(path):
    # Case-insensitive host filesystems must not invent version-specific files
    # such as Io.zig from older releases' lowercase io.zig.
    return path.parent.is_dir() and any(child.name == path.name and child.is_file()
                                       for child in path.parent.iterdir())


def compiler_inventory(source, cache=None):
    cache = cache if cache is not None else SourceCache()
    specs = [('air_tags', 'src/Air.zig', 'Tag', 'enum'),
             ('types', 'lib/std/builtin.zig', 'Type', 'union'),
             ('intern_keys', 'src/InternPool.zig', 'Key', 'union'),
             ('pointer_bases', 'src/InternPool.zig', 'BaseAddr', 'union')]
    out, hashes = {}, {}
    for category, relative, name, kind in specs:
        p = source / relative
        hashes[relative] = cache.digest(p)
        out[category] = members(cache.tokens(p), name, kind)
    # Additional compiler surfaces for upgrade impact. Missing version-specific
    # files are recorded explicitly; these are not a full source closure.
    for relative in ('src/Type.zig', 'src/Value.zig', 'src/Sema.zig',
                     'src/codegen/llvm.zig', 'lib/std/mem/Allocator.zig',
                     'lib/std/Thread.zig', 'lib/std/Io.zig', 'lib/std/time.zig'):
        p = source / relative
        hashes[relative] = cache.digest(p) if exact_file(p) else None
    return out, hashes


def pointer_dispositions(names, arms):
    return [{'name': name,
             'disposition': 'exporter-explicit-arm-conditional-review' if name in arms else
             'exporter-fallback-unsupported-marker-review' if any(token in ('"unsupported"', 'unsupported') for token in arms.get('*', [])) else
             'exporter-fallback-unclassified',
             'qualification': 'Source arm/fallback only; writePtr helpers and Check.lean require provenance and layout review.'}
            for name in names]


def project_source_hashes(roots, cache):
    """Fingerprint source bytes independently of local build/test cache state."""
    def transient(path):
        parts = path.relative_to(ROOT).parts
        return '.lake' in parts or '__pycache__' in parts or parts[:3] == ('tests', 'diff', 'out')

    entries = {}
    for relative in roots:
        p = ROOT/relative
        if transient(p):
            continue
        paths = []
        if p.is_dir():
            for directory, dirs, files in os.walk(p, topdown=True, followlinks=False):
                parent = Path(directory)
                dirs[:] = [name for name in dirs if not transient(parent/name)]
                paths.extend(parent/name for name in files if not transient(parent/name))
        else:
            paths = [p]
        for item in sorted(paths):
            if item.is_file():
                entries[str(item.relative_to(ROOT))] = cache.digest(item)
    return entries


def generate(version, source, os_name='linux'):
    cache = SourceCache()
    universe, fingerprints = compiler_inventory(source, cache)
    exporter = cache.tokens(ROOT/'zig-patch/air-json/json.zig')
    decode = switch_arms(function_body(exporter, 'writeInst'), ['tag'], 1)
    type_arms = switch_arms(function_body(exporter, 'writeTypeEntry'), ['ty', '.', 'zigTypeTag', '(', 'zcu', ')'])
    ptr_arms = switch_arms(function_body(exporter, 'resolvePtr'), ['base'])
    normalizer_source = cache.text(ROOT/'Air2Lean/Air/Normalize.lean')
    norms = normalizer(normalizer_source)
    rejection_reasons = runtime_tag_reasons(normalizer_source)
    semantic_paths = sorted((ROOT/'ZigLean').rglob('*.lean'))
    emit_paths = [ROOT/'Air2Lean/Emit.lean']
    proof_paths = sorted((ROOT/'Proofs').rglob('*.lean'))
    path_groups = {'semantics': semantic_paths, 'emission': emit_paths, 'proofs': proof_paths}
    @lru_cache(maxsize=None)
    def hits(group, symbol):
        return source_hits(path_groups[group], symbol, cache)

    # Parse actual selected golden JSON; malformed fixture is not silently evidence.
    test_tags = {}
    for p in golden_paths(version, os_name):
        data = json.loads(cache.text(p))
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
        if tag in rejection_reasons:
            disposition = 'normalizer-rejected-compiler-state-or-effect'
        elif tag.endswith('_optimized'):
            disposition = 'normalizer-rejected-fast-math'
        elif tag not in norms and not tag.startswith('call'):
            disposition = 'normalizer-unclassified-or-unknown'
        elif export_status != 'explicit-arm':
            disposition = 'conditional-pipeline-review-required'
        else:
            disposition = 'source-pipeline-candidate-unqualified'
        ops = norms.get(tag, ['call'] if tag.startswith('call') else [])
        rejection_reason = rejection_reasons.get(tag)
        tags.append({'tag': tag, 'disposition': disposition,
                     'exporter': {'status': export_status, 'reason': export_reason},
                     'normalization': {'status': 'explicit-source-rejection' if rejection_reason else 'explicit-source-branch' if tag in norms else 'call-prefix-branch' if tag.startswith('call') else 'no-explicit-source-branch', 'constructors': ops},
                     'parser': {'status': 'generic-schema-source-only', 'paths': ['Air2Lean/Air/Json.lean', 'Air2Lean/Air/Canon.lean']},
                     'checker': {'status': 'conditional-type-and-layout-review-required', 'paths': ['Air2Lean/Check.lean']},
                     'semantics': {'status': 'symbol-index-only', 'paths': sorted(set(p for op in ops for p in hits('semantics', op)))},
                     'emission': {'status': 'symbol-index-only', 'paths': sorted(set(p for op in ops for p in hits('emission', op)))},
                     'tests': {'status': 'golden-input-presence-only', 'paths': sorted(test_tags.get(tag, []))},
                     'proofs': {'status': 'symbol-index-only-not-proof-coverage', 'paths': sorted(set(p for op in ops for p in hits('proofs', op)))},
                     'guidance': (rejection_reason + '; source-only rejection classification, no compiler fixture or support qualification') if rejection_reason else 'Inspect exporter/Compat, normalizeOp, checker restrictions and emitted runtime calls; add compiler fixture, rejection and differential tests and checked contract before qualification.'})
    type_rows = [{'name': name, 'disposition': 'exporter-arm-conditional-checker-review' if name in type_arms else 'exporter-fallback-unclassified',
                  'qualification': 'Type/layout/value restrictions require Check.lean; an arm is not full type support.'}
                 for name in universe['types']]
    constants = [{'name': name, 'kind': 'type-key' if name.endswith('_type') else 'value-or-internal-key',
                  'disposition': 'unclassified-review-writeRef-and-Check',
                  'qualification': 'InternPool keys include internal/comptime entries; no claim all can reach executable AIR.'}
                 for name in universe['intern_keys']]
    bases = pointer_dispositions(universe['pointer_bases'], ptr_arms)
    scopes = {'inventory-tool': ['scripts/coverage.py', 'zig-patch/versions.toml'], 'translation': ['Air2Lean', 'zig-patch/air-json'], 'runtime-models': ['ZigLean'],
              'proof-sources': ['Proofs'], 'qualification-probes': ['scripts/floatprobe.sh', 'tests/diff', 'tests/golden', 'tests/roadmap/diagnostics'],
              'model-boundaries': ['Air2Lean/Memory.lean', 'docs/std-models.md']}
    project_hashes = {}
    for scope, roots in scopes.items():
        project_hashes[scope] = project_source_hashes(roots, cache)
    return {'format': FORMAT, 'zig_version': version, 'golden_os': os_name,
            'evidence_level': 'source-inventory; no compiler execution, proof checking or support qualification',
            'compiler_source_sha256': fingerprints, 'universe': universe,
            'tags': tags, 'types': type_rows, 'constants': constants, 'pointer_bases': bases,
            'models': model_inventory(cache.text(ROOT/'Air2Lean/Memory.lean')),
            'project_source_sha256': project_hashes,
            'summary': dict(Counter(row['disposition'] for row in tags))}


def changes(before, after):
    report = {'from': before['zig_version'], 'to': after['zig_version'],
              'golden_selection': {'from_os': before.get('golden_os'), 'to_os': after.get('golden_os')},
              'universes': {}, 'source_changes': {},
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
    def first_rows(rows):
        result = {}
        for row in rows:
            result.setdefault(row['tag'], row)
        return result
    old_rows, new_rows = first_rows(before['tags']), first_rows(after['tags'])
    report['tag_dispositions_changed'] = [tag for tag in sorted(set(old_rows) | set(new_rows)) if old_rows.get(tag) != new_rows.get(tag)]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('generate', 'check'):
        p = sub.add_parser(name)
        p.add_argument('--version', required=True)
        p.add_argument('--os', default='linux', help='golden OS overlay (default: linux); no host test claim')
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
    result = generate(args.version, args.source, args.os)
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
