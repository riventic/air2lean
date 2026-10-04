#!/usr/bin/env python3
"""Hash/inventory gate for checked L04 artifacts; hashes do not attest compilation."""
import hashlib
import json
from pathlib import Path
import re
import sys

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect(repo=REPO, case=CASE, record=False):
    manifest_path = case / 'provenance.json'
    manifest = json.loads(manifest_path.read_text())
    for role in ('source', 'exporter'):
        expected = manifest[role + '_sha256']
        if not isinstance(expected, str) or not re.fullmatch(r'[0-9a-f]{64}', expected):
            raise ValueError('invalid ' + role + ' SHA-256')
        if digest(repo / manifest[role]) != expected:
            raise ValueError('stale ' + role)
    files = sorted((case / 'air/0.16.0').glob('*.json'))
    data = [json.loads(path.read_text()) for path in files]
    expected = {'try_pointers.' + name for name in manifest['functions']}
    names = [item['name'] for item in data]
    if len(names) != len(expected) or set(names) != expected:
        raise ValueError('AIR function inventory differs')
    tags = []
    def walk(value):
        if isinstance(value, dict):
            if value.get('unsupported') is True:
                raise ValueError('unsupported AIR instruction')
            if 'tag' in value: tags.append(value['tag'])
            for child in value.values(): walk(child)
        elif isinstance(value, list):
            for child in value: walk(child)
    for item in data:
        if item.get('schema') != 11 or item.get('zig_version') != '0.16.0' or item.get('target_endian') != 'little':
            raise ValueError('AIR profile differs')
        walk(item.get('body', []))
    if 'try_ptr' not in tags or 'try_ptr_cold' not in tags:
        raise ValueError('both pointer-try tags must occur in actual AIR')
    gen = case / 'TryPointers/Gen.lean'
    inventory = {str(path.relative_to(case)): digest(path) for path in [*files, gen]}
    if record:
        manifest['artifacts'] = inventory
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    elif inventory != manifest['artifacts']:
        raise ValueError('stale or incomplete artifact inventory')
    return inventory

if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--record']):
        raise SystemExit('usage: check-artifacts.py [--record]')
    try:
        inspect(record=sys.argv[1:] == ['--record'])
    except (KeyError, OSError, ValueError, TypeError) as error:
        raise SystemExit(str(error))
    print('pointer-try source/exporter/artifact hashes and AIR inventory passed')
