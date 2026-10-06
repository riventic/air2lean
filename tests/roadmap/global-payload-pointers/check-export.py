#!/usr/bin/env python3
"""Check only freshly compiler-produced public fixtures, with source reachability markers."""
import argparse
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(HERE.parents[2]/'scripts/normalize-generated.py'))
BASELINE_FEATURES = runpy.run_path(str(HERE.parent/'try-pointers/check-artifacts.py'))['BASELINE_FEATURES']

def profile(document, version, backend):
    result = HELPERS['profile_for_air'](document)
    if document.get('schema') != 12 or document.get('zig_version') != version:
        raise ValueError('fresh AIR schema/version mismatch')
    arch, os_version, _ = result['target_triple'].split('-')
    if (document.get('target_endian') != 'little' or arch != 'x86_64' or
        os_version.split('.')[0] != 'linux' or result['abi'] not in {'gnu', 'musl'} or
        result['backend'] != backend or result['cpu'] != 'x86_64' or
        set(result['features']) != BASELINE_FEATURES or result['build_mode'] != 'ReleaseSafe' or
        result['error_tracing'] is not False):
        raise ValueError('fresh AIR differs from the requested Linux/baseline ReleaseSafe profile')
    return result

def type_at(document, ty):
    table = document['types']
    if type(ty) is not int or not 0 <= ty < len(table):
        raise ValueError('invalid type reference')
    return table[ty]

def field(document, ty, name):
    entry = type_at(document, ty)
    matches = [f for f in entry['fields'] if f.get('name') == name]
    if len(matches) != 1 or type(matches[0].get('offset')) is not int or matches[0]['offset'] < 0:
        raise ValueError(f'missing unique compiler field layout: {name}')
    return matches[0]

def pointers(value):
    if isinstance(value, dict):
        if 'ptr' in value: yield value['ptr']
        for key, child in value.items():
            if key != 'globals': yield from pointers(child)
    elif isinstance(value, list):
        for child in value: yield from pointers(child)

def check(directory, version, backend, reject=False):
    profiles = []
    if reject:
        expected = {'equalAlignment': 'error_payload_model_layout', 'volatilePayload': 'payload_volatile'}
        for name, reason in expected.items():
            doc = HELPERS['parse_json']((directory/f'reject.{name}.json').read_text())
            if doc['name'] != f'reject.{name}': raise ValueError('wrong rejection fixture')
            profiles.append(profile(doc, version, backend))
            found = list(pointers(doc['body']))
            if not found or any(p.get('unsupported') != reason or 'global' in p for p in found):
                raise ValueError(f'{name}: expected only explicit {reason} pointer rejection')
        if any(p != profiles[0] for p in profiles): raise ValueError('mixed rejection profiles')
        print('fresh source payload layout/volatile rejection checks passed')
        return
    names = ['optionalPtr', 'sameOptionalPtr', 'smallPtr', 'widePtr', 'optionalSlice']
    roots = []
    for name in names:
        path = directory/f'global_payloads.{name}.json'
        doc = HELPERS['parse_json'](path.read_text())
        profiles.append(profile(doc, version, backend))
        if doc['name'] != f'global_payloads.{name}': raise ValueError('wrong public source function')
        candidates = list(pointers(doc['body']))
        candidates = [p for p in candidates if p.get('payload_base') is True]
        if not candidates: raise ValueError(f'{name}: eu_payload/opt_payload did not reach the exporter')
        for p in candidates:
            if 'unsupported' in p or type(p.get('global')) is not int or type(p.get('off')) is not int:
                raise ValueError('payload resolution did not retain a global address')
            if not 0 <= p['global'] < len(doc['globals']): raise ValueError('invalid global index')
            named = [g['name'] for g in doc['globals'] if g.get('name')]
            if len(named) != len(set(named)): raise ValueError('duplicated named global identity')
            g = doc['globals'][p['global']]
            if not g.get('const') or 'init' not in g: raise ValueError('frozen source global lost its initializer')
            inner = field(doc, g['ty'], 'inner')
            small = field(doc, inner['ty'], 'small')
            wide = field(doc, inner['ty'], 'wide')
            opt = field(doc, inner['ty'], 'optional')
            opt_type = type_at(doc, opt['ty'])
            value = field(doc, opt_type['child'], 'value')
            expected = inner['offset'] + (
                small['offset'] + 2 if name == 'smallPtr' else
                wide['offset'] if name == 'widePtr' else opt['offset'] + value['offset'])
            if p['off'] != expected: raise ValueError(f'{name}: wrong payload offset {p["off"]}, expected {expected}')
            roots.append(g.get('name'))
    if any(p != profiles[0] for p in profiles): raise ValueError('mixed fresh AIR profiles')
    if len(set(roots)) != 1 or not roots[0]: raise ValueError('cross-file constants lost shared named global identity')
    print('fresh public constant pointers retain one global identity and exact nested payload offsets')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--version', required=True, choices=('0.14.1', '0.15.2', '0.16.0'))
    parser.add_argument('--backend', required=True, choices=('stage2_llvm', 'stage2_x86_64'))
    parser.add_argument('--reject', action='store_true')
    args = parser.parse_args()
    check(args.directory, args.version, args.backend, args.reject)
