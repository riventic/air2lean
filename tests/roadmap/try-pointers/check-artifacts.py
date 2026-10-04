#!/usr/bin/env python3
"""Hash/inventory gate for checked L04 artifacts; hashes do not attest compilation."""
import argparse
import hashlib
import json
from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect(repo=REPO, case=CASE, record=False, fresh_air=None):
    if record and fresh_air is not None:
        raise ValueError('fresh AIR validation cannot record checked artifact hashes')
    manifest_path = case / 'provenance.json'
    manifest = json.loads(manifest_path.read_text())
    for role in ('source', 'exporter'):
        expected = manifest[role + '_sha256']
        if not isinstance(expected, str) or not re.fullmatch(r'[0-9a-f]{64}', expected):
            raise ValueError('invalid ' + role + ' SHA-256')
        if digest(repo / manifest[role]) != expected:
            raise ValueError('stale ' + role)
    air_dir = Path(fresh_air) if fresh_air is not None else case / 'air/0.16.0'
    files = sorted(air_dir.glob('*.json'))
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
    # Fresh compiler output has host-dependent AIR details. Validate the same source,
    # exporter, exact function inventory, profile and tags; the caller separately
    # translates it and compares generated Lean byte-for-byte with checked Gen.
    if fresh_air is not None:
        return {path.name: digest(path) for path in files}
    gen = case / 'TryPointers/Gen.lean'
    inventory = {str(path.relative_to(case)): digest(path) for path in [*files, gen]}
    if record:
        manifest['artifacts'] = inventory
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    elif inventory != manifest['artifacts']:
        raise ValueError('stale or incomplete artifact inventory')
    return inventory

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--record', action='store_true')
    mode.add_argument('--fresh-air', type=Path, metavar='DIR',
                      help='validate fresh AIR inventory/profile without writing checked hashes')
    args = parser.parse_args()
    try:
        inspect(record=args.record, fresh_air=args.fresh_air)
    except (KeyError, OSError, ValueError, TypeError) as error:
        raise SystemExit(str(error))
    if args.fresh_air is not None:
        print('pointer-try source/exporter hashes and fresh AIR profile/inventory passed')
    else:
        print('pointer-try source/exporter/artifact hashes and AIR inventory passed')
