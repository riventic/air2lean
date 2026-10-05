#!/usr/bin/env python3
"""Hash/inventory gate for checked L04 artifacts; hashes do not attest compilation."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(REPO / 'scripts/normalize-generated.py'))
# Zig 0.16.0 Target.x86.cpu.x86_64, with the sse2 -> sse dependency.
BASELINE_FEATURES = {'64bit', 'cmov', 'cx8', 'fxsr', 'idivq_to_divl', 'macrofusion',
                     'mmx', 'nopl', 'slow_3ops_lea', 'slow_incdec', 'sse', 'sse2',
                     'vzeroupper', 'x87'}


def exporter_digest(case, manifest, record):
    origin = manifest['exporter_sha256']
    variant_path = case / 'integration-qualification.json'
    if not variant_path.exists():
        return origin
    if record:
        raise ValueError('integration qualification cannot rewrite historical provenance')
    variant = HELPERS['parse_json'](variant_path.read_text())
    fields = {'format', 'status', 'origin_provenance_sha256', 'origin_exporter_sha256',
              'current_exporter_sha256'}
    if (not isinstance(variant, dict) or set(variant) != fields or
            variant['format'] != 'l04-integration-inputs-v1' or
            variant['status'] != 'inputs-only-not-compilation-attestation'):
        raise ValueError('invalid integration qualification manifest')
    if variant['origin_exporter_sha256'] != origin:
        raise ValueError('integration origin exporter SHA-256 differs')
    if variant['origin_provenance_sha256'] != digest(case / 'provenance.json'):
        raise ValueError('integration historical provenance SHA-256 differs')
    expected = variant['current_exporter_sha256']
    if not isinstance(expected, str) or re.fullmatch(r'[0-9a-f]{64}', expected) is None:
        raise ValueError('invalid integration current exporter SHA-256')
    return expected


def fresh_profile(item):
    if item.get('schema') != 12 or item.get('zig_version') != '0.16.0':
        raise ValueError('fresh AIR profile differs: schema 12 / Zig 0.16.0 required')
    profile = HELPERS['profile_for_air'](item)
    arch, os_version, _ = profile['target_triple'].split('-')
    if (item.get('target_endian') != 'little' or arch != 'x86_64' or
            os_version.split('.')[0] != 'linux' or profile['abi'] not in {'gnu', 'musl'} or
            profile['backend'] != 'stage2_llvm' or profile['cpu'] != 'x86_64' or
            set(profile['features']) != BASELINE_FEATURES or
            profile['build_mode'] != 'ReleaseSafe' or profile['error_tracing'] is not False):
        raise ValueError('fresh AIR profile differs from Linux/baseline ReleaseSafe flags')
    return profile

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect(repo=REPO, case=CASE, record=False, fresh_air=None):
    if record and fresh_air is not None:
        raise ValueError('fresh AIR validation cannot record checked artifact hashes')
    manifest_path = case / 'provenance.json'
    manifest = HELPERS['parse_json'](manifest_path.read_text())
    for role in ('source', 'exporter'):
        expected = manifest[role + '_sha256']
        if not isinstance(expected, str) or not re.fullmatch(r'[0-9a-f]{64}', expected):
            raise ValueError('invalid ' + role + ' SHA-256')
        if role == 'exporter':
            expected = exporter_digest(case, manifest, record)
        if digest(repo / manifest[role]) != expected:
            raise ValueError('stale ' + role)
    air_dir = Path(fresh_air) if fresh_air is not None else case / 'air/0.16.0'
    files = sorted(air_dir.glob('*.json'))
    data = [HELPERS['parse_json'](path.read_text()) for path in files]
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
    profiles = []
    for item in data:
        if fresh_air is not None:
            profiles.append(fresh_profile(item))
        elif item.get('schema') != 11 or item.get('zig_version') != '0.16.0' or item.get('target_endian') != 'little':
            raise ValueError('AIR profile differs')
        walk(item.get('body', []))
    if profiles and any(profile != profiles[0] for profile in profiles):
        raise ValueError('fresh AIR has mixed profiles')
    if 'try_ptr' not in tags or 'try_ptr_cold' not in tags:
        raise ValueError('both pointer-try tags must occur in actual AIR')
    # Fresh compiler output has host-dependent AIR details. Validate the same source,
    # exporter, exact function inventory, profile and tags; the caller separately
    # translates it, binds the full output/input hashes, then compares the complete
    # generated body with checked Gen through normalize-generated.py.
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
