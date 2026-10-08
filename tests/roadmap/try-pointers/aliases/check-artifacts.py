#!/usr/bin/env python3
"""Hash/inventory gate for the L04 alias/cleanup fixture; hashes do not attest compilation.

The retained `try_aliases.*` AIR is hand-written in the 0.16.0 schema-11 exporter shape. Its
compiler export is pending, so `provenance.json` records `air_origin: hand-written` and every
qualification entry as `pending`. `--fresh-air DIR` validates the inventory/profile/tags of an
actual patched-compiler export without rewriting the retained hashes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import runpy

REPO = Path(__file__).resolve().parents[4]
CASE = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(REPO / 'scripts/normalize-generated.py'))
PENDING = {'compiler_export': 'pending', 'native': 'pending', 'lean': 'pending'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk_tags(value, tags):
    if isinstance(value, dict):
        if value.get('unsupported') is True:
            raise ValueError('unsupported AIR instruction')
        if 'tag' in value:
            tags.append(value['tag'])
        for child in value.values():
            walk_tags(child, tags)
    elif isinstance(value, list):
        for child in value:
            walk_tags(child, tags)


def inspect(repo=REPO, case=CASE, record=False, fresh_air=None):
    if record and fresh_air is not None:
        raise ValueError('fresh AIR validation cannot record checked artifact hashes')
    manifest_path = case / 'provenance.json'
    manifest = HELPERS['parse_json'](manifest_path.read_text())
    if manifest.get('air_origin') != 'hand-written' or manifest.get('qualification') != PENDING:
        raise ValueError('alias fixture must stay hand-written with pending qualification')
    if not record and digest(repo / manifest['source']) != manifest['source_sha256']:
        raise ValueError('stale source')
    air_dir = Path(fresh_air) if fresh_air is not None else case / 'air/0.16.0'
    files = sorted(air_dir.glob('*.json'))
    data = [HELPERS['parse_json'](path.read_text()) for path in files]
    expected = {'try_aliases.' + name for name in manifest['functions']}
    names = [item['name'] for item in data]
    if len(names) != len(expected) or set(names) != expected:
        raise ValueError('AIR function inventory differs')
    tags = []
    profiles = []
    for item in data:
        if fresh_air is not None:
            profiles.append(HELPERS['fresh_linux_profile'](item, '0.16.0'))
        elif (item.get('schema') != 11 or item.get('zig_version') != '0.16.0' or
              item.get('target_endian') != 'little'):
            raise ValueError('AIR profile differs')
        walk_tags(item.get('body', []), tags)
    if any(profile != profiles[0] for profile in profiles):
        raise ValueError('fresh AIR has mixed profiles')
    if 'try_ptr' not in tags:
        raise ValueError('pointer-try tag must occur in AIR')
    if fresh_air is not None:
        return {path.name: digest(path) for path in files}
    gen = case / 'TryAliases/Gen.lean'
    inventory = {str(path.relative_to(case)): digest(path) for path in [*files, gen]}
    if record:
        manifest['source_sha256'] = digest(repo / manifest['source'])
        manifest['artifacts'] = inventory
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    elif inventory != manifest['artifacts']:
        raise ValueError('stale or incomplete artifact inventory')
    return inventory


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--record', action='store_true')
    mode.add_argument('--fresh-air', type=Path, metavar='DIR')
    args = parser.parse_args()
    try:
        inspect(record=args.record, fresh_air=args.fresh_air)
    except (KeyError, OSError, ValueError, TypeError) as error:
        raise SystemExit(str(error))
    print('pointer-try alias fixture hashes and AIR inventory passed')
