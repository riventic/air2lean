#!/usr/bin/env python3
"""V03 independent export validation: re-check exported AIR JSON structure without Air2Lean.

This shares no code with the Lean decoder (`Air2Lean/Air/Json.lean`, `Canon.lean`). It reads
the exporter's JSON directly and checks structural invariants of docs/air-json.md:
instruction id uniqueness, operand references that resolve to an earlier instruction of an
enclosing body, block/loop/dispatch targets, nonempty bodies ending in a noreturn terminator,
type-table and global references, acyclic value types and the per-version AIR tag set and
exporter-unsupported markers of coverage/<zig_version>.json. It checks structure, not
semantics: a file that passes is still only trusted (docs/premises.md TRU-02).

With no paths it validates every committed golden AIR file (`git ls-files` under
tests/golden and tests/roadmap whose directory is named `air*`). Exit 0: all valid;
1: a finding (one line per violation); 2: usage or I/O error.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MAX_SCHEMA = 12
KINDS = {'int', 'float', 'bool', 'void', 'noreturn', 'ptr', 'array', 'vector', 'optional',
         'error_union', 'error_set', 'struct', 'tuple', 'enum', 'union', 'other'}
CHILD_FIELDS = ('child', 'error', 'payload', 'tag', 'safety_tag')
BODY_FIELDS = ('body', 'then', 'else')
# Tags that must carry these bodies (docs/air-json.md, Inst table).
REQUIRED_BODIES = {
    'block': ('body',), 'dbg_inline_block': ('body',), 'loop': ('body',),
    'try': ('body',), 'try_cold': ('body',), 'try_ptr': ('body',), 'try_ptr_cold': ('body',),
    'cond_br': ('then', 'else'),
}
TARGET_KINDS = {'br': {'block', 'dbg_inline_block'}, 'repeat': {'loop'},
                'switch_dispatch': {'loop_switch_br'}}
CONSTANT_CHILDREN = ('payload', 'some', 'utag', 'uval', 'slice_ptr', 'slice_len')
GIT_SCOPES = ('tests/golden', 'tests/roadmap')


class Finding(Exception):
    pass


def strict_json(text):
    """JSON with duplicate keys and NaN/Infinity rejected (the exporter writes neither)."""
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise Finding(f'duplicate JSON key {key!r}')
            result[key] = value
        return result

    def constant(name):
        raise Finding(f'non-JSON constant {name}')
    return json.loads(text, object_pairs_hook=pairs, parse_constant=constant)


def is_nat(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def load_inventory(coverage_dir, version, cache):
    if version not in cache:
        path = Path(coverage_dir) / f'{version}.json'
        if not path.is_file():
            cache[version] = None
        else:
            data = json.loads(path.read_text(encoding='utf-8'))
            universe = set(data['universe']['air_tags'])
            exporter = {entry['tag']: entry['exporter']['status'] for entry in data['tags']}
            cache[version] = (universe, exporter)
    return cache[version]


class Validator:
    def __init__(self, doc, inventory):
        self.doc = doc
        self.universe, self.exporter = inventory
        self.errors = []
        self.types = doc.get('types')
        self.globals = doc.get('globals', [])

    def error(self, where, message):
        self.errors.append(f'{where}: {message}')

    def type_id(self, where, value):
        if not is_nat(value) or not isinstance(self.types, list) or value >= len(self.types):
            self.error(where, f'type reference {value!r} is not in the type table')
            return False
        return True

    def kind(self, ty):
        if is_nat(ty) and isinstance(self.types, list) and ty < len(self.types) \
                and isinstance(self.types[ty], dict):
            return self.types[ty].get('k')
        return None

    # Types -----------------------------------------------------------------
    def check_types(self):
        if not isinstance(self.types, list):
            self.error('types', 'missing or not a list')
            self.types = []
            return
        edges = {}
        for index, ty in enumerate(self.types):
            where = f'types[{index}]'
            if not isinstance(ty, dict) or ty.get('k') not in KINDS:
                self.error(where, f'unknown type kind {ty.get("k") if isinstance(ty, dict) else ty!r}')
                continue
            k = ty['k']
            children = []
            for field in CHILD_FIELDS:
                if field in ty and self.type_id(f'{where}.{field}', ty[field]):
                    children.append(ty[field])
            for n, field in enumerate(ty.get('fields', []) if k in ('struct', 'tuple', 'union') else []):
                if not isinstance(field, dict) or 'ty' not in field:
                    self.error(f'{where}.fields[{n}]', 'field without a type')
                elif self.type_id(f'{where}.fields[{n}].ty', field['ty']):
                    children.append(field['ty'])
            if k == 'int' and not (isinstance(ty.get('signed'), bool) and is_nat(ty.get('bits'))):
                self.error(where, 'int needs boolean signed and natural bits')
            if k == 'float' and ty.get('bits') not in (16, 32, 64, 80, 128):
                self.error(where, f'float bits {ty.get("bits")!r} not in 16/32/64/80/128')
            if k == 'ptr' and ty.get('size') not in ('one', 'many', 'slice', 'c'):
                self.error(where, f'pointer size {ty.get("size")!r}')
            if k in ('ptr', 'array', 'vector', 'optional') and 'child' not in ty:
                self.error(where, f'{k} without child')
            if k == 'error_union' and not ('error' in ty and 'payload' in ty):
                self.error(where, 'error_union needs error and payload')
            if k in ('array', 'vector') and not is_nat(ty.get('len')):
                self.error(where, f'{k} needs a natural len')
            # Pointers break value cycles; every other child edge is by value.
            edges[index] = [] if k == 'ptr' else children
        state = {}
        for start in edges:
            if start in state:
                continue
            stack = [(start, iter(edges[start]))]
            state[start] = 'open'
            while stack:
                node, it = stack[-1]
                child = next(it, None)
                if child is None:
                    state[node] = 'done'
                    stack.pop()
                elif state.get(child) == 'open':
                    self.error(f'types[{child}]', 'cyclic value type (only pointer recursion is allowed)')
                elif child not in state and child in edges:
                    state[child] = 'open'
                    stack.append((child, iter(edges[child])))

    # References ------------------------------------------------------------
    def constant(self, where, ref):
        """A constant Ref: a type plus constant-only nested values."""
        if not isinstance(ref, dict):
            self.error(where, f'operand is not an object: {ref!r}')
            return
        if 'inst' in ref:
            self.error(where, f'instruction ref {ref["inst"]!r} inside a constant')
            return
        if 'ty' not in ref:
            self.error(where, 'constant without a type')
        else:
            self.type_id(f'{where}.ty', ref['ty'])
        for key in CONSTANT_CHILDREN:
            if key in ref:
                self.constant(f'{where}.{key}', ref[key])
        for n, item in enumerate(ref.get('elems', [])):
            self.constant(f'{where}.elems[{n}]', item)
        ptr = ref.get('ptr')
        if isinstance(ptr, dict) and 'global' in ptr:
            if not is_nat(ptr['global']) or ptr['global'] >= len(self.globals):
                self.error(where, f'pointer constant global {ptr["global"]!r} is not in globals')

    def operand(self, where, ref, available):
        if isinstance(ref, dict) and 'inst' in ref:
            if set(ref) != {'inst'}:
                self.error(where, f'instruction ref with extra fields {sorted(ref)}')
            if ref['inst'] not in available:
                self.error(where, f'instruction ref {ref["inst"]!r} does not resolve to an earlier '
                                  'instruction of an enclosing body')
        else:
            self.constant(where, ref)

    def operands(self, inst):
        yield from enumerate(inst.get('args', []))
        if 'callee' in inst:
            yield 'callee', inst['callee']
        for n, case in enumerate(inst.get('cases', [])):
            for m, item in enumerate(case.get('items', [])):
                yield f'cases[{n}].items[{m}]', item
            for m, pair in enumerate(case.get('ranges', [])):
                for side, item in zip('ab', pair):
                    yield f'cases[{n}].ranges[{m}].{side}', item
        for group in ('outputs', 'inputs'):
            for n, entry in enumerate(inst.get(group, [])):
                if isinstance(entry, dict) and 'ref' in entry:
                    yield f'{group}[{n}]', entry['ref']

    # Instructions ----------------------------------------------------------
    def body(self, where, body, scopes, available, seen):
        if not isinstance(body, list) or not body:
            self.error(where, 'body is empty or not a list')
            return
        available = set(available)
        for n, inst in enumerate(body):
            here = f'{where}[{n}]'
            if not isinstance(inst, dict):
                self.error(here, 'instruction is not an object')
                continue
            ident, tag = inst.get('id'), inst.get('tag')
            if not is_nat(ident):
                self.error(here, f'instruction id {ident!r} is not a natural number')
                ident = None  # an unusable id is neither defined nor a valid target
            elif ident in seen:
                self.error(here, f'duplicate instruction id {ident}')
            if ident is not None:
                seen.add(ident)
            here = f'{where}[{n}] (id {ident}, {tag})'
            self.tag(here, inst)
            if not isinstance(tag, str):
                tag = ''
            if 'ty' in inst:
                self.type_id(f'{here}.ty', inst['ty'])
            elif not tag.startswith('inferred_alloc'):
                self.error(here, 'instruction without a result type')
            for label, ref in self.operands(inst):
                self.operand(f'{here}.{label}', ref, available)
            for m, lane in enumerate(inst.get('mask', [])):
                if isinstance(lane, dict) and 'v' in lane:
                    self.constant(f'{here}.mask[{m}]', lane['v'])
            if tag in TARGET_KINDS:
                target = inst.get('target')
                if not any(t == target and k in TARGET_KINDS[tag] for t, k in scopes):
                    self.error(here, f'target {target!r} is not an enclosing '
                                     f'{"/".join(sorted(TARGET_KINDS[tag]))}')
            for field in REQUIRED_BODIES.get(tag, ()):
                if field not in inst:
                    self.error(here, f'missing {field} body')
            if tag in ('switch_br', 'loop_switch_br') and not ('cases' in inst and 'else' in inst):
                self.error(here, 'switch needs cases and else')
            nested = scopes + [(ident, tag)] if tag in ('block', 'dbg_inline_block', 'loop',
                                                       'loop_switch_br') else scopes
            for field in BODY_FIELDS:
                if field in inst:
                    self.body(f'{here}.{field}', inst[field], nested, available, seen)
            for m, case in enumerate(inst.get('cases', [])):
                self.body(f'{here}.cases[{m}].body', case.get('body') if isinstance(case, dict) else None,
                          nested, available, seen)
            noreturn = self.kind(inst.get('ty')) == 'noreturn'
            last = n == len(body) - 1
            if last and not noreturn:
                self.error(here, 'body does not end in a noreturn terminator')
            if noreturn and not last and not tag.startswith('call'):
                self.error(here, 'noreturn instruction before the end of its body')
            if ident is not None:
                available.add(ident)

    def tag(self, where, inst):
        tag = inst.get('tag')
        if not isinstance(tag, str) or tag not in self.universe:
            self.error(where, f'tag {tag!r} is not an AIR tag of this Zig version')
            return
        status = self.exporter.get(tag, '')
        marked = inst.get('unsupported')
        if marked is not None and marked is not True:
            self.error(where, '"unsupported" must be literal true')
        if marked and 'unsupported-marker' not in status:
            self.error(where, f'"unsupported" marker on a tag the exporter decodes ({status})')
        if not marked and 'unsupported-marker' in status:
            self.error(where, f'decoded operands for a tag the exporter marks unsupported ({status})')

    # Function --------------------------------------------------------------
    def run(self):
        doc = self.doc
        schema = doc.get('schema')
        if not is_nat(schema) or not 1 <= schema <= MAX_SCHEMA:
            self.error('schema', f'unsupported schema {schema!r}')
        if not isinstance(doc.get('name'), str) or not doc.get('name'):
            self.error('name', 'missing function name')
        if schema == MAX_SCHEMA:
            profile = doc.get('profile')
            if not isinstance(profile, dict):
                self.error('profile', 'schema 12 requires a profile')
            elif profile.get('zig_version') != doc.get('zig_version'):
                self.error('profile.zig_version', 'differs from zig_version')
        if doc.get('target_endian', 'little') not in ('little', 'big'):
            self.error('target_endian', f'{doc.get("target_endian")!r}')
        if not isinstance(self.globals, list):
            self.error('globals', 'not a list')
            self.globals = []
        self.check_types()
        params = doc.get('params')
        if not isinstance(params, list):
            self.error('params', 'missing or not a list')
        else:
            for n, ty in enumerate(params):
                self.type_id(f'params[{n}]', ty)
        if schema == MAX_SCHEMA and 'noalias' not in doc:
            self.error('noalias', 'schema 12 requires the noalias parameter list')
        noalias = doc.get('noalias', [])
        count = len(params) if isinstance(params, list) else 0
        if not (isinstance(noalias, list) and all(is_nat(i) and i < count for i in noalias)
                and noalias == sorted(set(noalias))):
            self.error('noalias', 'not increasing parameter indices')
        self.type_id('ret', doc.get('ret'))
        for n, glob in enumerate(self.globals):
            if not isinstance(glob, dict) or 'ty' not in glob:
                self.error(f'globals[{n}]', 'global without a type')
                continue
            self.type_id(f'globals[{n}].ty', glob['ty'])
            if 'init' in glob:
                self.constant(f'globals[{n}].init', glob['init'])
        self.body('body', doc.get('body'), [], set(), set())
        return self.errors


def validate_text(text, coverage_dir=ROOT / 'coverage', cache=None):
    """Return the findings for one AIR JSON document (empty: structurally valid)."""
    cache = {} if cache is None else cache
    try:
        doc = strict_json(text)
    except (Finding, ValueError) as error:
        return [f'json: {error}']
    if not isinstance(doc, dict):
        return ['json: top level is not an object']
    version = doc.get('zig_version')
    inventory = load_inventory(coverage_dir, version, cache) if isinstance(version, str) else None
    if inventory is None:
        return [f'zig_version: no coverage inventory for {version!r}']
    try:
        return Validator(doc, inventory).run()
    except (TypeError, AttributeError, KeyError) as error:
        # Wrong JSON shapes (an object where a list belongs, a list as an id) are findings.
        return [f'malformed AIR shape: {type(error).__name__}: {error}']


def committed_air(root=ROOT):
    listed = subprocess.run(['git', '-C', str(root), 'ls-files', '-z', '--', *GIT_SCOPES],
                            check=True, capture_output=True).stdout.decode('utf-8').split('\0')
    # A fixture's provenance record may sit beside its AIR (`air/provenance.json`); it is not AIR.
    return sorted(root / rel for rel in listed if rel.endswith('.json')
                  and Path(rel).name != 'provenance.json'
                  and any(part.startswith('air') for part in Path(rel).parts[:-1]))


def expand(paths):
    for path in map(Path, paths):
        if path.is_dir():
            yield from sorted(path.rglob('*.json'))
        else:
            yield path


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('paths', nargs='*', help='AIR JSON files or directories (default: committed golden AIR)')
    parser.add_argument('--coverage-dir', default=str(ROOT / 'coverage'))
    args = parser.parse_args(argv)
    try:
        files = list(expand(args.paths)) if args.paths else committed_air()
    except (OSError, subprocess.CalledProcessError) as error:
        print(f'validate-air: {error}', file=sys.stderr)
        return 2
    if not files:
        print('validate-air: no AIR files', file=sys.stderr)
        return 2
    cache, bad = {}, 0
    for path in files:
        try:
            text = path.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError) as error:
            print(f'validate-air: {path}: {error}', file=sys.stderr)
            return 2
        findings = validate_text(text, args.coverage_dir, cache)
        if findings:
            bad += 1
            for finding in findings:
                print(f'{path}: {finding}')
    print(f'validate-air: {len(files)} files, {bad} with findings')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
