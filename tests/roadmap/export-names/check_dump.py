#!/usr/bin/env python3
"""Inspect public fixture dumps; never invokes a compiler or translator."""
import argparse
import hashlib
import json
from pathlib import Path
import re

PREFIX = '~air2lean-sha256-'


def filename(name):
    stem = name.split('.', 1)[0].upper()
    reserved = stem in {'CON', 'PRN', 'AUX', 'NUL'} or re.fullmatch(r'(COM|LPT)[1-9]', stem)
    if (re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_.-]*', name) and
            len(name.encode('utf-8')) + 5 <= 255 and not reserved):
        return name + '.json'
    return PREFIX + hashlib.sha256(name.encode('utf-8')).hexdigest() + '.json'


def documents(directory, skip=None):
    result = {}
    for path in sorted(directory.glob('*.json')):
        if path.name == skip:
            continue
        if path.stat().st_size > 32 * 1024 * 1024:
            raise ValueError(f'{path}: fixture exceeds 32MiB inspection cap')
        doc = json.loads(path.read_text())
        name = doc['name']
        if name in result:
            raise ValueError(f'duplicate full identity {name!r}')
        if path.name != filename(name):
            raise ValueError(f'{path}: incorrect filename for full JSON name')
        if doc['schema'] != 12 or doc['profile']['zig_version'] != doc['zig_version']:
            raise ValueError(f'{path}: missing current exporter profile')
        result[name] = path
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--mode', choices=['check', 'seed-collision', 'check-collision', 'seed-reexport', 'check-reexport'], default='check')
    args = parser.parse_args()
    expected = json.loads(Path(__file__).with_name('expected-names.json').read_text())
    marker = args.directory / '.export-names-expectation'
    if args.mode in ('check-collision', 'check-reexport'):
        record = json.loads(marker.read_text())
        target = args.directory / record['file']
        if args.mode == 'check-collision':
            if hashlib.sha256(target.read_bytes()).hexdigest() != record['sha256']:
                parser.error('distinct-identity collision was overwritten')
            found = documents(args.directory, skip=target.name)
            if set(found) != set(expected) - {record['name']}:
                parser.error('collision suppressed an independent sibling')
            print('collision preserved; all independent siblings retained')
            return
        if 'reexport_sentinel' in json.loads(target.read_text()):
            parser.error('same-identity re-export did not replace the prior document')
    found = documents(args.directory)
    if set(found) != set(expected):
        parser.error(f'missing={sorted(set(expected)-set(found))}; unexpected={sorted(set(found)-set(expected))}')
    if args.mode in ('seed-collision', 'seed-reexport'):
        name = next(name for name in expected if len(name.encode('utf-8')) == 408)
        target = found[name]
        doc = json.loads(target.read_text())
        if args.mode == 'seed-collision':
            doc['name'] = 'public_fixture.distinct_identity'
        else:
            doc['reexport_sentinel'] = 'MUST_BE_REPLACED'
        target.write_text(json.dumps(doc, ensure_ascii=False))
        marker.write_text(json.dumps(dict(file=target.name, name=name, sha256=hashlib.sha256(target.read_bytes()).hexdigest())))
        print(f'{args.mode}: {target.name}')
        return
    print(f'checked {len(found)} full identities, {sum(p.name.startswith(PREFIX) for p in found.values())} hash filenames')


if __name__ == '__main__':
    main()
