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


# A Lean constructor reference `.name` or `.«name»`; group 1 or 2 holds the name.
CTOR = r'\.(?:«([^»]+)»|([A-Za-z][A-Za-z0-9]*))'


def normalizer(text):
    section = text.split('  match raw.tag with', 1)[1].split('\n/--', 1)[0]
    matches = list(re.finditer(r'^  \| ((?:"[^"\n]+"\s*(?:\|\s*)?)+)=>', section, re.M))
    result = {}
    for match in matches:
        next_arm = re.search(r'^  \| ', section[match.end():], re.M)
        end = match.end() + next_arm.start() if next_arm else len(section)
        branch = section[match.end():end]
        # Constructors returned directly or by a `return if … then .a else .b` choice.
        ops = sorted(set(a or b for a, b in re.findall(r'(?:\breturn|\bthen|\belse)\s+' + CTOR, branch)))
        for tag in re.findall(r'"([^"\n]+)"', match.group(1)):
            result[tag] = ops
    return result


def canon_aliases(text):
    """Canon.lean's `tagAliases017`: Zig 0.17.0 tags read in their 0.16.0 spelling."""
    section = text.split('def tagAliases017', 1)[1].split('\n\n', 1)[0]
    pairs = re.findall(r'\("([^"]+)", "([^"]+)"\)', section)
    if not pairs:
        raise ValueError('Canon.lean: tagAliases017 not found')
    return dict(pairs)


def runtime_tag_reasons(text, name='runtimeTagReason?'):
    """Source-only rejection policy shared with the translator, not feature support.

    Actual per-version enum membership is supplied by compiler_inventory.
    """
    section = lean_section(text, name)
    arms = re.finditer(r'^  \| ((?:"[^"\n]+"\s*(?:\|\s*)?)+)=> some ("[^"\n]+")$', section, re.M)
    return {tag: json.loads(match.group(2)) for match in arms
            for tag in re.findall(r'"([^"\n]+)"', match.group(1))}


def lean_string_constant(text, name):
    match = re.search(r'^def ' + re.escape(name) + r' : String :=\s*\n\s*("[^"\n]+")$', text, re.M)
    if not match:
        raise ValueError(f'missing Lean string constant {name}')
    return json.loads(match.group(1))


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


# Reviewed roots of committed compiler-exported AIR outside tests/golden, keyed by the
# document that records the export command and checked source. `{version}` selects the
# per-version directory. Every other AIR JSON directory under tests/roadmap must be listed
# in NON_COMPILER_AIR with the reason it is not compiler evidence.
COMPILER_FIXTURE_ROOTS = {
    'tests/roadmap/thread-tuples/air/{version}': 'tests/roadmap/thread-tuples/provenance.json',
    'tests/roadmap/try-pointers/air/{version}': 'tests/roadmap/try-pointers/provenance.json',
    'tests/roadmap/bitops/qualified/{version}/air': 'tests/roadmap/bitops/qualified/0.16.0/manifest.json',
    'tests/roadmap/idle-loops/air': 'tests/roadmap/idle-loops/provenance.json',
    'tests/roadmap/spawn-failure/air/{version}': 'tests/roadmap/spawn-failure/air/provenance.json',
    'tests/roadmap/thread-locals/air/{version}': 'tests/roadmap/thread-locals/README.md',
    'tests/roadmap/futures/air/{version}': 'tests/roadmap/futures/check.sh',
    'tests/roadmap/pointer-width/air/{version}/x86_64-linux': 'tests/roadmap/pointer-width/README.md',
    'tests/roadmap/const-bases/air-fresh/{version}': 'tests/roadmap/const-bases/README.md',
    'tests/roadmap/loop-tactics/nested/air': 'tests/roadmap/loop-tactics/nested/provenance.json',
    'tests/roadmap/vector-layouts/air/{version}': 'tests/roadmap/vector-layouts/README.md',
    'tests/roadmap/vector-layouts/air-reads/{version}': 'tests/roadmap/vector-layouts/README.md',
    'tests/roadmap/const-locals/air/{version}': 'tests/roadmap/const-locals/provenance.json',
    'tests/roadmap/bitops-native/shift-panic/air/{version}': 'tests/roadmap/bitops-native/README.md',
    'tests/roadmap/const-locals/air-fuzz_s19/{version}': 'tests/roadmap/const-locals/provenance.json',
    'tests/roadmap/volatile-effects/air/{version}': 'tests/roadmap/volatile-effects/air/provenance.json',
    'tests/roadmap/volatile-effects/air-asm/{version}': 'tests/roadmap/volatile-effects/air-asm/provenance.json',
    # T03: patched-compiler exports of big_endian.zig/reject.zig (check.sh --export, README).
    'tests/roadmap/big-endian/air/{version}/s390x-linux': 'tests/roadmap/big-endian/README.md',
    'tests/roadmap/big-endian/air/{version}/x86_64-linux': 'tests/roadmap/big-endian/README.md',
    'tests/roadmap/big-endian/air/{version}/s390x-reject': 'tests/roadmap/big-endian/README.md',
    'tests/roadmap/env-boundaries/air/{version}': 'tests/roadmap/env-boundaries/air/provenance.json',
    'tests/roadmap/zig017/divceil/air/{version}': 'tests/roadmap/zig017/divceil/provenance.json',
    'tests/roadmap/bitcast-017/air/{version}': 'docs/bitcast-semantics.md',
    'tests/roadmap/zig017/casts/air/{version}': 'tests/roadmap/zig017/casts/provenance.json',
    'tests/roadmap/noreturn-variants/air/{version}': 'tests/roadmap/noreturn-variants/provenance.json',
    # L10: patched-compiler exports of error_width.zig at six `--error-limit` widths (export.sh).
    'tests/roadmap/error-width/air-fresh/{version}/bits2': 'tests/roadmap/error-width/provenance.json',
    'tests/roadmap/error-width/air-fresh/{version}/bits8': 'tests/roadmap/error-width/provenance.json',
    'tests/roadmap/error-width/air-fresh/{version}/bits10': 'tests/roadmap/error-width/provenance.json',
    'tests/roadmap/error-width/air-fresh/{version}/bits16': 'tests/roadmap/error-width/provenance.json',
    'tests/roadmap/error-width/air-fresh/{version}/bits17': 'tests/roadmap/error-width/provenance.json',
    'tests/roadmap/error-width/air-fresh/{version}/bits32': 'tests/roadmap/error-width/provenance.json',
}
NON_COMPILER_AIR = {
    'tests/roadmap/undef-operands/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/global-init/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/undef-locals/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/aggregate-casts/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/packed-fields/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/try-pointers/aliases/air': 'hand-written AIR (provenance.json air_origin; compiler export pending)',
    'tests/roadmap/error-width/air': 'hand-written AIR per error-code width (make-fixtures.py, README)',
    'tests/roadmap/asm-effects/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/const-bases/air': 'hand-written AIR in the exporter schema (README)',
    'tests/roadmap/pointer-width/air/0.16.0/wasm32-freestanding':
        'wasm32 compiler export: evidence for the T02 32-bit profile only (README), not this inventory',
    'tests/roadmap/pointer-width/air/0.16.0/wasm32-wasi':
        'wasm32 compiler export: evidence for the T02 32-bit profile only (README), not this inventory',
    'tests/roadmap/pointer-width/air/0.16.0/wasm32-reject':
        'wasm32 compiler export of rejected forms (reject.zig, README), not this inventory',
    'tests/roadmap/noreturn-variants/air-reject': 'compiler AIR for layout rejections (test_cli.py, provenance.json); not tag evidence',
    'tests/roadmap/fuzz': 'fuzzer-mutated AIR regressions',
    'tests/roadmap/models': 'synthetic model-boundary inputs',
    'tests/roadmap/profiles': 'synthetic profile inputs',
    'tests/roadmap/air-semantics/fixtures': 'hand-written caller of the golden basic.scale (docs/air-semantics.md)',
    'tests/roadmap/zig017/air': 'synthetic 0.17.0 AIR in the exporter schema (tests/roadmap/zig017/test_cli.py)',
    'tests/roadmap/zig017/reject': 'synthetic 0.17.0 rejection inputs (tests/roadmap/zig017/test_cli.py)',
}


def is_air_json(data):
    return isinstance(data, dict) and 'zig_version' in data and isinstance(data.get('body'), list)


def roadmap_fixture_paths(version):
    """Committed compiler-exported roadmap AIR recorded for exactly this compiler version."""
    selected = []
    for template in COMPILER_FIXTURE_ROOTS:
        directory = ROOT/template.format(version=version)
        selected.extend(path for path in sorted(directory.glob('*.json'))
                        if json.loads(path.read_text()).get('zig_version') == version)
    return selected


def compiler_fixture_root(directory):
    """Whether a repository-relative directory is a reviewed COMPILER_FIXTURE_ROOTS entry."""
    return any(re.fullmatch(re.escape(t).replace(re.escape('{version}'), r'[^/]+'), directory)
               for t in COMPILER_FIXTURE_ROOTS)


def unreviewed_air_roots():
    """AIR JSON directories under tests/roadmap in neither reviewed table."""
    found = set()
    for path in (ROOT/'tests/roadmap').rglob('*.json'):
        relative = str(path.parent.relative_to(ROOT))
        if compiler_fixture_root(relative) or \
                any(relative == r or relative.startswith(r + '/') for r in NON_COMPILER_AIR):
            continue
        try:
            data = json.loads(path.read_text())
        except (ValueError, UnicodeDecodeError):
            continue
        if is_air_json(data):
            found.add(relative)
    return sorted(found)


# Table row pattern -> legacy recognizer label kept in coverage JSON.
MODEL_ROWS = (('allocFn?', r'^  allocModel "([^"\n]+)"'),
              ('threadFn?', r'^  threadModel "([^"\n]+)"'),
              ('rejectedThreadFn?', r'symbol := "([^"\n]+)",\s*kind := \.rejected'))


def model_inventory(text):
    """Rows of the single built-in std model table (Air2Lean/StdModels.lean `stdModels`)."""
    start = text.index('def stdModels')
    end = text.find('\n\n', start)
    table = text[start:] if end < 0 else text[start:end]
    entries = []
    for fn, pattern in MODEL_ROWS:
        for name in sorted(set(re.findall(pattern, table, re.M))):
            if re.match(r'(?:mem\.Allocator|Thread|Io|time)\.', name) and ' ' not in name:
                entries.append({'name': name, 'recognizer': fn,
                                'disposition': 'translation-rejected' if fn == 'rejectedThreadFn?' else 'recognized-model-boundary',
                                'qualification': 'source-only; contracts and target/version restrictions require docs/std-models.md and Check.lean review'})
    return entries


def exact_file(path):
    # Case-insensitive host filesystems must not invent version-specific files
    # such as Io.zig from older releases' lowercase io.zig.
    return path.parent.is_dir() and any(child.name == path.name and child.is_file()
                                       for child in path.parent.iterdir())


TYPE_FILES = ('lib/std/builtin.zig', 'lib/std/lang.zig')


def compiler_inventory(source, cache=None):
    cache = cache if cache is not None else SourceCache()
    # Zig 0.17 moved std.builtin's language types (including Type) to std.lang.
    type_file = next((relative for relative in TYPE_FILES if exact_file(source / relative)), TYPE_FILES[0])
    specs = [('air_tags', 'src/Air.zig', 'Tag', 'enum'),
             ('types', type_file, 'Type', 'union'),
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


# Every inventory row receives one of these names. Only `unclassified-forbidden`
# is a placeholder: `generate` and `check` fail while any row carries it.
FORBIDDEN = 'unclassified-forbidden'
DISPOSITIONS = {
    'tags': {
        'emitted-unqualified': 'Exporter decodes the tag for this version, normalizeOp builds an Op, an Emit.lean dispatch arm emits it and a selected compiler-generated fixture contains it; no semantics, proof or contract qualification.',
        'emitted-unfixtured': 'Passes the same source stages as emitted-unqualified, but no selected golden or reviewed roadmap compiler export for this version contains the tag; FIXTURE_REQUESTS names unexported candidate source. Not a supported source feature.',
        'erased-at-emission': 'Exported and normalized to line/debug metadata that the emitter drops.',
        'rejected-fast-math': 'normalizeOp rejects the fast-math suffix with optimizedFloatGuidance before decoding.',
        'rejected-compiler-state-or-effect': 'runtimeTagReason? rejects the tag with a specific diagnostic.',
        'rejected-exporter-unsupported': 'The exporter writes "unsupported": true for this version; normalizeOp rejects the marker with the exporterTagReason? reason and guidance.',
        'rejected-unknown-tag': 'Exported, but normalizeOp has no branch; its fallback rejects the unknown AIR tag with a diagnostic.',
        'unreachable-at-export': 'Reviewed override: the compiler cannot place this tag in exported analyzed AIR.',
        FORBIDDEN: 'No mechanical derivation or reviewed override; generate/check fail.',
    },
    'types': {
        'exported-checker-restricted': 'Explicit writeTypeEntry arm; Check.lean applies type/layout restrictions.',
        'exported-as-other-rejected': 'Fallback writes kind "other"; Check.checkTy rejects it with a diagnostic (pointer-to-fn/anyopaque children are checked separately).',
        'unreachable-at-export': 'Reviewed override: comptime-only type that cannot be a runtime AIR value type.',
        FORBIDDEN: 'No mechanical derivation or reviewed override; generate/check fail.',
    },
    'constants': {
        'type-key-via-type-table': 'InternPool type key (`*_type`): exported through the type table and classified by the `types` rows.',
        'value-exported': 'Explicit writeRef arm or fallback helper that names the key; Json.parseVal checks the form against the type.',
        'value-fallback-text-restricted': 'Fallback writes the formatted value; Json.parseLeafVal accepts only int/bool/void/packed leaf types and rejects others with a diagnostic.',
        'unreachable-at-export': 'Reviewed override: internal/comptime key that is not an exported runtime operand.',
        FORBIDDEN: 'No mechanical derivation or reviewed override; generate/check fail.',
    },
    'pointer_bases': {
        'resolved-conditional': 'Explicit resolvePtr arm can resolve to a global; nested restrictions may still yield an unsupported pointer that Check.lean rejects.',
        'rejected-unsupported-pointer-base': 'resolvePtr returns unsupported for the base; Check.lean rejects the pointer constant with a diagnostic.',
        FORBIDDEN: 'No mechanical derivation or reviewed override; generate/check fail.',
    },
}

# L14: for each tag that passes every source stage but has no compiler-generated fixture for
# some version, the candidate function in FIXTURE_SOURCE that should produce it once exported
# with the command in docs/coverage.md §L14, or None with the reason no candidate exists.
# Unexported and unverified; an emitted tag without a fixture and without a row here is forbidden.
FIXTURE_SOURCE = 'tests/roadmap/runtime-tags/runtime_tags.zig'
NO_SEMA_PRODUCER = ('no Sema producer found in the 0.14.1/0.15.2/0.16.0 sources (only legalization/backend '
                    'switches name it); needs an unreachable-at-export review or a compiler-generated counterexample')
FIXTURE_REQUESTS = {
    'add_with_overflow': 'addOverflow', 'sub_with_overflow': 'subOverflow',
    'mul_with_overflow': 'mulOverflow', 'shl_with_overflow': 'shlOverflow',
    'sub_wrap': 'subWrap', 'sub_sat': 'subSat', 'mul_sat': 'mulSat', 'shl_sat': 'shlSat',
    'shl': 'shlPlain', 'shl_exact': 'shlExact', 'shr_exact': 'shrExact', 'div_exact': 'divExact',
    'xor': 'xorBits', 'clz': 'leading', 'ctz': 'trailing', 'popcount': 'population',
    'byte_swap': 'swapBytes', 'bit_reverse': 'reverseBits',
    'ptr_add': 'advance', 'ptr_sub': 'retreat', 'ptr_elem_val': 'manyElem',
    'trap': 'trapZero', 'ret': 'unsafeReturn', 'loop_switch_br': 'dispatch', 'switch_dispatch': 'dispatch',
    'call_always_tail': 'alwaysTail', 'call_never_tail': 'neverTail', 'call_never_inline': 'neverInline',
    'try_cold': 'coldTry', 'try_ptr': 'tryPtr', 'try_ptr_cold': 'tryPtrCold', 'is_null': 'isNull',
    'is_non_err_ptr': 'nonErrPtr', 'errunion_payload_ptr_set': 'setPayload', 'error_name': 'errorName',
    'is_null_ptr': None, 'is_err': None, 'is_err_ptr': None,
    'bool_and': 'threeWay', 'bool_or': 'alignSlice',
    'fptrunc': 'narrow', 'fpext': 'widen', 'int_from_float': 'truncUnsafe', 'float_from_int': 'toFloat',
    'struct_field_ptr': 'fieldPtr', 'slice': 'subSlice', 'ptr_slice_len_ptr': 'setLen',
    'ptr_slice_ptr_ptr': 'setPtr', 'slice_elem_ptr': 'elemPtr', 'array_to_slice': 'arraySlice',
    'aggregate_init': 'makePair', 'tag_name': 'colorName', 'splat': 'splatLanes', 'shuffle': 'reverseLanes',
    'memset': 'clearUnsafe', 'memset_safe': 'clearSafe', 'memcpy': 'copyBytes',
    'cmpxchg_weak': 'casWeak', 'cmpxchg_strong': 'casStrong', 'atomic_load': 'loadAcquire',
    'atomic_store_unordered': 'storeUnordered', 'atomic_store_monotonic': 'storeMonotonic',
    'atomic_store_release': 'storeRelease', 'atomic_store_seq_cst': 'storeSeqCst', 'atomic_rmw': 'fetchAdd',
}


def fixture_request(tag, source_text):
    """The reviewed fixture request for an unfixtured tag, or None when absent or dangling."""
    if tag not in FIXTURE_REQUESTS:
        return None
    function = FIXTURE_REQUESTS[tag]
    if function is None:
        return {'source': None, 'function': None, 'reason': NO_SEMA_PRODUCER}
    if not re.search(r'^(?:export|pub) fn ' + re.escape(function) + r'\(', source_text, re.M):
        return None
    return {'source': FIXTURE_SOURCE, 'function': function,
            'reason': 'candidate source not yet exported by a patched compiler; see docs/coverage.md §L14'}


# Normalize.lean definition holding the reason and guidance for each rejected disposition.
# `rejected-unknown-tag` has none, so the L14 gate fails any such row.
REJECTION_DEFINITIONS = {'rejected-fast-math': 'optimizedFloatGuidance',
                         'rejected-compiler-state-or-effect': 'runtimeTagReason?',
                         'rejected-exporter-unsupported': 'exporterTagReason?'}


# Reviewed exceptions. `replaces` pins the mechanical result an override was reviewed
# against: when the derivation changes, the override is stale and the row is forbidden.
OVERRIDES = {
    'tags': {},
    'types': {name: {'disposition': 'unreachable-at-export', 'replaces': 'exported-as-other-rejected',
                     'reason': 'comptime-only type: Sema never gives a runtime AIR instruction or operand this type'}
              for name in ('type', 'comptime_int', 'comptime_float', 'undefined', 'null', 'enum_literal')},
    'constants': {
        'undef': {'disposition': 'value-exported', 'replaces': 'value-fallback-text-restricted',
                  'reason': 'writeRef fallback tests val.isUndef before formatting and writes the "undef" marker that Json.parseVal accepts'},
        'enum_literal': {'disposition': 'unreachable-at-export', 'replaces': 'value-fallback-text-restricted',
                         'reason': 'value of the comptime-only enum_literal type'},
        'memoized_call': {'disposition': 'unreachable-at-export', 'replaces': 'value-fallback-text-restricted',
                          'reason': 'Sema comptime call memoization entry, not a value'},
        'variable': {'disposition': 'unreachable-at-export', 'replaces': 'value-fallback-text-restricted',
                     'reason': '0.14/0.15 global variable owner; analyzed AIR addresses globals through ptr nav bases'},
    },
    'pointer_bases': {},
}


def version_minor(version):
    match = re.fullmatch(r'0\.(\d+)\.\d+', version)
    return int(match.group(1)) if match else None


def version_branches(ts, minor):
    """Token branches selected by comptime `Compat.vNN` tests; unknown versions keep all."""
    if ts[:2] != ['if', '(']:
        return [ts]
    close = balanced(ts, 1)
    cond = ts[2:close]
    negated = cond[:1] == ['!']
    cond = cond[1:] if negated else cond
    if len(cond) != 3 or cond[:2] != ['Compat', '.'] or not re.fullmatch(r'v\d+', cond[2]):
        return [ts]
    if ts[close+1:close+2] != ['{']:
        raise ValueError('Compat version branch without a block')
    then_end = balanced(ts, close+1)
    then, rest = ts[close+2:then_end], ts[then_end+1:]
    other = rest[1:] if rest[:1] == ['else'] else []
    if other[:1] == ['{'] and balanced(other, 0) == len(other) - 1:
        other = other[1:-1]
    flag = None if minor is None else (minor == int(cond[2][1:])) != negated
    branches = []
    if flag is not False: branches += version_branches(then, minor)
    if flag is not True: branches += version_branches(other, minor)
    return branches


def named_members(ts, exporter):
    """Enum members a branch compares against directly or through a `Compat.is*` helper."""
    def compared(ts):  # The tokenizer splits `==` into two `=` tokens.
        return {ts[i+3] for i in range(len(ts)-3) if ts[i:i+3] == ['=', '=', '.']}
    names = compared(ts)
    for i in range(len(ts)-3):
        if ts[i:i+2] == ['Compat', '.'] and ts[i+2].startswith('is') and ts[i+3] == '(':
            names |= compared(function_body(exporter, ts[i+2]))
    return {identifier(name) for name in names}


def exporter_status(tag, decode, minor, exporter):
    arm, fallback = decode.get(tag), tag not in decode
    if fallback:
        arm = decode.get('*')
        if arm is None:
            return 'fallback-unclassified'
    statuses = set()
    for branch in version_branches(arm, minor):
        if fallback:
            statuses.add('fallback-named-decoder' if tag in named_members(branch, exporter) else
                          'fallback-unsupported-marker' if '"unsupported"' in branch else
                          'fallback-unclassified')
        elif '"unsupported"' not in branch:
            statuses.add('explicit-arm')
        elif any(t in ('if', 'switch', 'orelse', 'catch', 'while', 'for') for t in branch):
            statuses.add('explicit-arm-conditional-unsupported')
        else:
            statuses.add('explicit-arm-unsupported-marker')
    return statuses.pop() if len(statuses) == 1 else 'version-conditional-unresolved'


def lean_section(text, name):
    """One top-level Lean definition, ending at the next top-level command."""
    match = re.search(r'^(?:(?:private|partial|noncomputable) )*def ' + re.escape(name) + r'(?![^\s])', text, re.M)
    if not match:
        raise ValueError(f'missing Lean definition {name}')
    end = re.compile(r'^(?:/--|@\[|end\b|mutual\b|theorem |(?:(?:private|partial|noncomputable) )*def )', re.M).search(text, match.end())
    return text[match.start():end.start() if end else len(text)]


def normalizer_rules(text):
    """Diagnostic gates around normalizeOp's tag table: fast-math suffix and call prefix."""
    body = lean_section(text, 'normalizeOp')
    fast = re.findall(r'if raw\.tag\.endsWith "([^"]+)" then\s*\n\s*throw', body)
    call = re.findall(r'if tag\.startsWith "([^"]+)" then', body)
    if len(fast) != 1 or len(call) != 1 or not re.search(r'if raw\.unsupported then\s*\n\s*throw', body) \
            or 'unknown AIR tag' not in body:
        raise ValueError('normalizeOp: fast-math, exporter-marker, call-prefix or unknown-tag gate not found')
    return fast[0], call[0]


def emission_arms(text):
    """Op constructors with an explicit emitter dispatch arm, and those emitScalar drops."""
    scalar = lean_section(text, 'emitScalar')
    dispatch = scalar + lean_section(text, 'emitStmts') + lean_section(text, 'emitTerminator')
    def ctors(text):
        return {a or b for a, b in re.findall(r'\|\s*' + CTOR + r'(?![A-Za-z0-9_])', text)}
    erased = set()
    for pattern in re.findall(r'^(\s*\|[^\n]*?)=>\s*\(env, none\)\s*$', scalar, re.M):
        erased |= ctors(pattern)
    return ctors(dispatch), erased


def apply_override(category, row):
    name = row.get('tag', row.get('name'))
    override = OVERRIDES[category].get(name)
    if override is None:
        row['derivation'] = {'method': 'mechanical'}
    elif override['replaces'] == row['disposition']:
        row['derivation'] = {'method': 'reviewed-override', 'replaces': override['replaces'], 'reason': override['reason']}
        row['disposition'] = override['disposition']
    else:
        row['derivation'] = {'method': 'stale-override', 'derived': row['disposition'],
                             'replaces': override['replaces'], 'reason': override['reason']}
        row['disposition'] = FORBIDDEN
    return row


UNIVERSES = {'tags': 'air_tags', 'types': 'types', 'constants': 'intern_keys', 'pointer_bases': 'pointer_bases'}


def disposition_problems(inventory):
    """Rows without a named disposition, and compiler universe members without a row."""
    problems = []
    for category, universe in UNIVERSES.items():
        rows = inventory[category]
        names = [row.get('tag', row.get('name')) for row in rows]
        if names != inventory['universe'][universe]:
            problems.append(f'{category}: rows do not match the compiler {universe} universe')
        for name, row in zip(names, rows):
            if row.get('disposition') not in DISPOSITIONS[category] or row['disposition'] == FORBIDDEN:
                problems.append(f'{category}: {name}: {row.get("disposition")} {json.dumps(row.get("derivation"))}')
    return problems


def compiler_fixture_path(relative):
    """A committed golden or a file directly inside a reviewed compiler-export root."""
    if relative.startswith('tests/golden/'):
        return True
    return compiler_fixture_root(relative.rsplit('/', 1)[0])


def air_tags(data):
    """Instruction tags (objects with a string tag and an integer id) anywhere in AIR JSON."""
    found = set()
    def visit(value):
        if isinstance(value, dict):
            if isinstance(value.get('tag'), str) and type(value.get('id')) is int:
                found.add(value['tag'])
            for child in value.values(): visit(child)
        elif isinstance(value, list):
            for child in value: visit(child)
    visit(data)
    return found


def l14_problems(inventory):
    """L14 gate on an inventory: emitted tags need a compiler fixture (or a reviewed request);
    rejected tags need the translator's current reason and guidance."""
    problems = [f'tests/roadmap AIR directory {d} is in neither COMPILER_FIXTURE_ROOTS nor NON_COMPILER_AIR'
                for d in unreviewed_air_roots()]
    source = (ROOT/'Air2Lean/Air/Normalize.lean').read_text()
    reasons = {'runtimeTagReason?': runtime_tag_reasons(source),
               'exporterTagReason?': runtime_tag_reasons(source, 'exporterTagReason?'),
               'optimizedFloatGuidance': lean_string_constant(source, 'optimizedFloatGuidance')}
    fixture_text = (ROOT/FIXTURE_SOURCE).read_text()
    tags_cache = {}
    for row in inventory['tags']:
        tag, disposition = row['tag'], row['disposition']
        label = f'{inventory.get("zig_version")}: {tag}'
        paths = row.get('tests', {}).get('paths', [])
        if disposition == 'emitted-unqualified':
            witnesses = []
            for relative in paths:
                path = ROOT/relative
                if compiler_fixture_path(relative) and path.is_file():
                    if relative not in tags_cache:
                        tags_cache[relative] = air_tags(json.loads(path.read_text()))
                    if tag in tags_cache[relative]:
                        witnesses.append(relative)
            if not witnesses:
                problems.append(f'{label}: emitted-unqualified without a committed compiler-generated fixture containing it')
        elif disposition == 'emitted-unfixtured':
            request = fixture_request(tag, fixture_text)
            if paths:
                problems.append(f'{label}: emitted-unfixtured but fixture paths are recorded')
            if request is None or row.get('fixture_request') != request:
                problems.append(f'{label}: emitted-unfixtured without a current FIXTURE_REQUESTS entry')
        elif disposition.startswith('rejected-'):
            rejection = row.get('rejection') or {}
            definition = REJECTION_DEFINITIONS.get(disposition)
            current = reasons.get(definition) if rejection.get('definition') == definition else None
            current = current.get(tag) if isinstance(current, dict) else current
            if not rejection.get('reason') or rejection['reason'] != current:
                problems.append(f'{label}: {disposition} without a current translator reason and guidance')
    return problems


def pointer_dispositions(names, arms, checker_rejects=True):
    def derive(name):
        arm = arms.get(name, arms.get('*', []))
        if arm[:5] == ['return', '.', '{', '.', 'unsupported']:
            return 'rejected-unsupported-pointer-base' if checker_rejects else FORBIDDEN
        return 'resolved-conditional' if name in arms else FORBIDDEN
    return [apply_override('pointer_bases', {'name': name, 'disposition': derive(name),
             'qualification': 'Source arm/fallback only; writePtr helpers and Check.lean require provenance and layout review.'})
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
    # Canon.versionTags renames 0.17.0's split and renamed tags to the 0.16.0 spelling before
    # normalizeOp reads them: such a tag has its canonical tag's constructors.
    for alias, canonical in canon_aliases(cache.text(ROOT/'Air2Lean/Air/Canon.lean')).items():
        if canonical in norms:
            norms.setdefault(alias, norms[canonical])
    rejection_reasons = runtime_tag_reasons(normalizer_source)
    exporter_reasons = runtime_tag_reasons(normalizer_source, 'exporterTagReason?')
    fast_guidance = lean_string_constant(normalizer_source, 'optimizedFloatGuidance')
    fixture_text = cache.text(ROOT/FIXTURE_SOURCE)
    semantic_paths = sorted((ROOT/'ZigLean').rglob('*.lean'))
    proof_paths = sorted((ROOT/'Proofs').rglob('*.lean'))
    path_groups = {'semantics': semantic_paths, 'proofs': proof_paths}
    @lru_cache(maxsize=None)
    def hits(group, symbol):
        return source_hits(path_groups[group], symbol, cache)

    # Parse actual selected golden and reviewed roadmap compiler-exported JSON; a malformed
    # fixture is not silently evidence.
    test_tags = {}
    for p in golden_paths(version, os_name) + roadmap_fixture_paths(version):
        for tag in air_tags(json.loads(cache.text(p))):
            test_tags.setdefault(tag, set()).add(str(p.relative_to(ROOT)))
    minor = version_minor(version)
    fast_suffix, call_prefix = normalizer_rules(normalizer_source)
    emitted, erased = emission_arms(cache.text(ROOT/'Air2Lean/Emit.lean'))
    export_reasons = {
        'explicit-arm': 'Explicit writeInst arm for this version; operand correctness and nested helper conditions are unverified.',
        'fallback-named-decoder': 'Version-selected fallback branch names the tag (directly or via a Compat.is* helper) and decodes it.',
        'explicit-arm-unsupported-marker': 'Version-selected explicit arm writes only the unsupported marker.',
        'fallback-unsupported-marker': 'Version-selected fallback writes the unsupported marker for every tag it does not name.',
        'explicit-arm-conditional-unsupported': 'Arm writes the unsupported marker under a data-dependent condition; review required.',
        'version-conditional-unresolved': 'Compat version branches disagree and the version label selects none.',
        'fallback-unclassified': 'Fallback neither names the tag nor writes the unsupported marker.'}
    tags = []
    for tag in universe['air_tags']:
        export_status = exporter_status(tag, decode, minor, exporter)
        rejection_reason = rejection_reasons.get(tag)
        is_call = tag not in norms and tag.startswith(call_prefix)
        ops = norms.get(tag, ['call'] if is_call else [])
        unemitted = [op for op in ops if op not in emitted]
        request = None
        if tag.endswith(fast_suffix):
            disposition = 'rejected-fast-math'
        elif rejection_reason:
            disposition = 'rejected-compiler-state-or-effect'
        elif export_status in ('explicit-arm-unsupported-marker', 'fallback-unsupported-marker'):
            # L14: an exporter rejection needs a reviewed reason and guidance in the translator.
            disposition = 'rejected-exporter-unsupported' if tag in exporter_reasons else FORBIDDEN
        elif export_status not in ('explicit-arm', 'fallback-named-decoder'):
            disposition = FORBIDDEN
        elif tag not in norms and not is_call:
            disposition = 'rejected-unknown-tag'
        elif not ops or unemitted:
            disposition = FORBIDDEN
        elif all(op in erased for op in ops):
            disposition = 'erased-at-emission'
        elif test_tags.get(tag):
            disposition = 'emitted-unqualified'
        else:
            # L14: no compiler-generated fixture; honest only with a reviewed fixture request.
            request = fixture_request(tag, fixture_text)
            disposition = 'emitted-unfixtured' if request else FORBIDDEN
        reached = disposition in ('emitted-unqualified', 'emitted-unfixtured', 'erased-at-emission')
        reason = (fast_guidance if disposition == 'rejected-fast-math' else rejection_reason
                  if disposition == 'rejected-compiler-state-or-effect' else exporter_reasons.get(tag)
                  if disposition == 'rejected-exporter-unsupported' else None)
        emission = ('erased-dispatch-arm' if disposition == 'erased-at-emission' else 'dispatch-arm') if reached else \
            'missing-dispatch-arm: ' + ', '.join(unemitted) if disposition == FORBIDDEN and unemitted else 'not-reached'
        tags.append(apply_override('tags', {'tag': tag, 'disposition': disposition,
                     'exporter': {'status': export_status, 'reason': export_reasons[export_status]},
                     'normalization': {'status': 'explicit-source-rejection' if rejection_reason else 'fast-math-rejection' if tag.endswith(fast_suffix) else 'explicit-source-branch' if tag in norms else 'call-prefix-branch' if is_call else 'unknown-tag-rejection', 'constructors': ops},
                     'parser': {'status': 'generic-schema-source-only', 'paths': ['Air2Lean/Air/Json.lean', 'Air2Lean/Air/Canon.lean']},
                     'checker': {'status': 'conditional-type-and-layout-review-required', 'paths': ['Air2Lean/Check.lean']},
                     'semantics': {'status': 'symbol-index-only', 'paths': sorted(set(p for op in ops for p in hits('semantics', op)))},
                     'emission': {'status': emission, 'paths': ['Air2Lean/Emit.lean'] if reached else []},
                     'tests': {'status': 'compiler-fixture-presence-only', 'paths': sorted(test_tags.get(tag, []))},
                     'proofs': {'status': 'symbol-index-only-not-proof-coverage', 'paths': sorted(set(p for op in ops for p in hits('proofs', op)))},
                     'rejection': {'reason': reason, 'source': 'Air2Lean/Air/Normalize.lean', 'definition': REJECTION_DEFINITIONS[disposition]} if reason else None,
                     'fixture_request': request if disposition == 'emitted-unfixtured' else None,
                     'guidance': (reason + '; source-only rejection classification, no compiler fixture or support qualification') if reason else DISPOSITIONS['tags'][disposition] + ' Qualification needs a compiler fixture, rejection/differential tests and a checked contract.'}))
    other_written = '"other"' in type_arms.get('*', [])
    other_rejected = re.search(r'\|\s*\.other name =>\s*\n\s*throw', cache.text(ROOT/'Air2Lean/Check.lean')) is not None
    type_rows = [apply_override('types', {'name': name,
                  'disposition': 'exported-checker-restricted' if name in type_arms else 'exported-as-other-rejected' if other_written and other_rejected else FORBIDDEN,
                  'qualification': 'Type/layout/value restrictions require Check.lean; an arm is not full type support.'})
                 for name in universe['types']]
    ref_arms = switch_arms(function_body(exporter, 'writeRef'), ['ip', '.', 'indexToKey', '(', 'ip_index', ')'])
    ref_fallback = ref_arms.get('*', [])
    fallback_named = named_members(ref_fallback, exporter)
    fallback_text = 'writeFmt' in ref_fallback and re.search(r'\| other => throw s!"\{fnName\}: constant of unsupported type',
                                                              lean_section(cache.text(ROOT/'Air2Lean/Air/Json.lean'), 'parseLeafVal')) is not None
    def constant_disposition(name):
        if name in ref_arms or name in fallback_named:
            return 'value-exported'
        if name.endswith('_type'):
            return 'type-key-via-type-table'
        return 'value-fallback-text-restricted' if fallback_text else FORBIDDEN
    constants = [apply_override('constants', {'name': name, 'kind': 'type-key' if name.endswith('_type') else 'value-or-internal-key',
                  'disposition': constant_disposition(name),
                  'qualification': 'writeRef source arm/fallback only; Json.parseVal and Check.lean restrict forms and types.'})
                 for name in universe['intern_keys']]
    ptr_rejected = re.search(r'ptrOther\? then throw', cache.text(ROOT/'Air2Lean/Check.lean')) is not None
    bases = pointer_dispositions(universe['pointer_bases'], ptr_arms, ptr_rejected)
    scopes = {'inventory-tool': ['scripts/coverage.py', 'zig-patch/versions.toml'], 'translation': ['Air2Lean', 'zig-patch/air-json'], 'runtime-models': ['ZigLean'],
              'proof-sources': ['Proofs'], 'qualification-probes': ['scripts/floatprobe.sh', 'tests/diff', 'tests/golden', 'tests/roadmap/diagnostics',
                                       'tests/roadmap/runtime-tags',
                                       # Every compiler-fixture root is tag evidence, so its sources are hashed.
                                       *(root.split('/{version}')[0] for root in COMPILER_FIXTURE_ROOTS)],
              'model-boundaries': ['Air2Lean/StdModels.lean', 'Air2Lean/Memory.lean', 'docs/std-models.md']}
    project_hashes = {}
    for scope, roots in scopes.items():
        project_hashes[scope] = project_source_hashes(roots, cache)
    return {'format': FORMAT, 'zig_version': version, 'golden_os': os_name,
            'evidence_level': 'source-inventory; no compiler execution, proof checking or support qualification',
            'compiler_source_sha256': fingerprints, 'universe': universe,
            'tags': tags, 'types': type_rows, 'constants': constants, 'pointer_bases': bases,
            'models': model_inventory(cache.text(ROOT/'Air2Lean/StdModels.lean')),
            'project_source_sha256': project_hashes,
            'summary': dict(Counter(row['disposition'] for row in tags)),
            'category_summary': {category: dict(Counter(row['disposition'] for row in rows))
                                 for category, rows in (('types', type_rows), ('constants', constants), ('pointer_bases', bases))},
            'dispositions': DISPOSITIONS}


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
    report['model_boundary_changed'] = report['model_recognition_changed'] or bool(report['source_changes'].get('model-boundaries')) or any(p.startswith('lib/std/') and p not in TYPE_FILES for p in report['compiler_source_changes'])
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
    p = sub.add_parser('l14', help='offline L14 fixture/guidance gate over committed inventories')
    p.add_argument('inventories', type=Path, nargs='+')
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
    if args.command == 'l14':
        problems = []
        for path in args.inventories:
            inventory = json.loads(path.read_text())
            problems += disposition_problems(inventory) + l14_problems(inventory)
            rows = Counter(row['disposition'] for row in inventory['tags'])
            print(f"{inventory['zig_version']}: {rows['emitted-unqualified']} emitted tags with a compiler fixture, "
                  f"{rows['emitted-unfixtured']} without (fixture requested), "
                  f"{sum(n for d, n in rows.items() if d.startswith('rejected-'))} rejected with reason and guidance")
        if problems:
            print('\n'.join(problems), file=sys.stderr)
            print(f'{len(problems)} L14 problems: add a compiler fixture, a FIXTURE_REQUESTS row or a translator reason.', file=sys.stderr)
            return 1
        return 0
    result = generate(args.version, args.source, args.os)
    problems = disposition_problems(result) + l14_problems(result)
    if args.command == 'generate':
        # Written even when incomplete so the forbidden rows can be reviewed in place.
        args.inventory.parent.mkdir(parents=True, exist_ok=True)
        args.inventory.write_text(json.dumps(result, indent=2)+'\n')
        print(f'{args.version}: {len(result["tags"])} AIR tags, {len(result["types"])} type tags, {len(result["constants"])} intern keys, {len(result["pointer_bases"])} pointer bases; source evidence only')
    else:
        old = json.loads(args.inventory.read_text())
        if old != result:
            print(json.dumps(changes(old, result), indent=2))
            print('Inventory stale. Review changes and regenerate only after recording upgrade qualification obligations.', file=sys.stderr)
            return 1
    if problems:
        print('\n'.join(problems), file=sys.stderr)
        print(f'{len(problems)} rows lack a named disposition: extend the derivation or add a reviewed override in scripts/coverage.py.', file=sys.stderr)
        return 1
    if args.command == 'check':
        print(f'{args.version}: inventory current (source evidence only)')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError, IndexError) as error:
        print(f'coverage: {error}', file=sys.stderr)
        sys.exit(2)
