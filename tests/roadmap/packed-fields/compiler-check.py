#!/usr/bin/env python3
"""Hash/inventory/profile gate for the L08 compiler export (compiler-provenance.json).

`air-fresh/0.16.0/llvm` and `air-fresh/0.16.0/x86_64` are unmodified patched-compiler exports of
`packed_fields.zig`; hashes bind the retained files but do not attest that a compiler ran.
Modes: default (retained files), `--record` (rewrite the hashes after a deliberate re-export),
`--fresh DIR` (a fresh `compiler.sh --export DIR`: same inventory and profile; the caller
translates it and compares it with the retained `PackedFieldsFresh` modules).
"""
import argparse
import hashlib
import json
from pathlib import Path
import runpy

REPO = Path(__file__).resolve().parents[3]
CASE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(REPO / 'scripts/normalize-generated.py'))
BACKENDS = {'llvm': 'stage2_llvm', 'x86_64': 'stage2_x86_64'}
GENERATED = ('PackedFieldsFresh/Gen.lean', 'PackedFieldsX86/Gen.lean')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profile(doc, kind):
    """Schema-12 Linux x86_64 baseline ReleaseSafe profile of backend `kind`."""
    if doc.get('schema') != 12 or doc.get('zig_version') != '0.16.0':
        raise ValueError('AIR must be schema 12 from Zig 0.16.0')
    p = HELPERS['profile_for_air'](doc)
    if (doc.get('target_endian') != 'little' or p['target_triple'].split('-')[0] != 'x86_64' or
            p['target_triple'].split('-')[1].split('.')[0] != 'linux' or p['cpu'] != 'x86_64' or
            set(p['features']) != HELPERS['BASELINE_FEATURES'] or p['build_mode'] != 'ReleaseSafe' or
            p['error_tracing'] is not False or p['backend'] != BACKENDS[kind]):
        raise ValueError(f'AIR profile differs from the {kind} Linux/baseline ReleaseSafe export')
    return p


def load(directory, kind, expected):
    files = sorted(directory.glob('*.json'))
    docs = [HELPERS['parse_json'](path.read_text()) for path in files]
    if sorted(d['name'] for d in docs) != sorted('packed_fields.' + n for n in expected):
        raise ValueError(f'{kind} AIR function inventory differs')
    profiles = [profile(d, kind) for d in docs]
    if any(p != profiles[0] for p in profiles):
        raise ValueError(f'{kind} AIR has mixed profiles')
    for doc in docs:
        if 'unsupported' in json.dumps(doc):
            raise ValueError('unsupported AIR instruction')
    return files


def inspect(case=CASE, record=False, fresh=None):
    manifest_path = case / 'compiler-provenance.json'
    manifest = HELPERS['parse_json'](manifest_path.read_text())
    source = case / manifest['source']
    if record:
        manifest['source_sha256'] = digest(source)
    elif digest(source) != manifest['source_sha256']:
        raise ValueError('stale source')
    inventory = {}
    for kind, expected in manifest['functions'].items():
        directory = Path(fresh) / kind if fresh else case / 'air-fresh/0.16.0' / kind
        files = load(directory, kind, expected)
        root = Path(fresh) if fresh else case
        inventory.update({str(p.relative_to(root)): digest(p) for p in files})
    if fresh:
        return inventory
    inventory.update({g: digest(case / g) for g in GENERATED})
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
    mode.add_argument('--fresh', type=Path, metavar='DIR')
    args = parser.parse_args()
    try:
        inspect(record=args.record, fresh=args.fresh)
    except (KeyError, OSError, ValueError, TypeError) as error:
        raise SystemExit(str(error))
    print('packed-field compiler export: ' + ('fresh inventory/profile' if args.fresh else 'hashes, inventory and profile') + ' passed')
