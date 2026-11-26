#!/usr/bin/env python3
"""Opaque-type entries the translator must reject through the CLI, each with its diagnostic.

Every case is the committed export of `copy` (`fn (*Handle) *Handle`) of each Zig version with
its type table changed: what an exporter that does not mark opaque types writes, an entry that
claims the primitive's name, an entry outside the schema, and pointer kinds that need the size
of the opaque type. Zig rejects the last ones at compile time; the translator must not rely on
that.

usage: negatives.py TRANSLATOR
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERSIONS = ('0.17.1', '0.16.0', '0.15.2', '0.14.1')
NO_SIZE = "opaque type 'opaque_ptrs.Handle' has no size, alignment or values"


def opaque(types):
    found = [t for t in types if t['k'] == 'opaque']
    if len(found) != 1:
        raise SystemExit(f'expected one opaque type in the export of copy, found {len(found)}')
    return found[0]


def pointers(types):
    return [t for t in types if t['k'] == 'ptr' and types[t['child']]['k'] == 'opaque']


def unmarked(types):
    entry = opaque(types)
    del entry['module']
    entry['k'] = 'other'


def primitive_name(types):
    opaque(types)['name'] = 'anyopaque'


def no_module(types):
    del opaque(types)['module']


def with_fields(types):
    opaque(types)['fields'] = []


def with_size(types):
    opaque(types).update(abi_size=0, abi_align=1)


def pointer_size(size):
    def change(types):
        for t in pointers(types):
            t['size'] = size
            if size == 'slice':
                t['abi_size'] = 16
    return change


def by_value(types):
    # Every `*Handle` becomes `Handle` itself: a parameter and a result of the opaque type.
    index = types.index(opaque(types))
    for i, t in enumerate(types):
        if t['k'] == 'ptr' and t['child'] == index:
            types[i] = dict(types[index])


CASES = {
    'an export that does not mark the opaque type (kind other)':
        (unmarked, "type 'opaque_ptrs.Handle' is outside the subset (otherwise unsupported)"),
    'an opaque entry named anyopaque':
        (primitive_name, "a declared opaque type cannot have the primitive's name 'anyopaque'"),
    'an opaque entry without its module': (no_module, "missing 'module'"),
    'an opaque entry with fields': (with_fields, "unknown key 'fields'"),
    'an opaque entry with a size': (with_size, 'its entry cannot state a layout'),
    'a many-item pointer to the opaque type': (pointer_size('many'), NO_SIZE),
    'a slice of the opaque type': (pointer_size('slice'), NO_SIZE),
    'a C pointer to the opaque type': (pointer_size('c'), NO_SIZE),
    'the opaque type by value': (by_value, NO_SIZE),
}


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    for version in VERSIONS:
        source = (HERE / 'air' / version / 'opaque_ptrs.copy.json').read_text()
        for name, (change, message) in CASES.items():
            doc = json.loads(source)
            change(doc['types'])
            with tempfile.TemporaryDirectory(prefix='air2lean-opaque-pointers-') as temp:
                air = Path(temp) / 'air'
                air.mkdir()
                (air / 'opaque_ptrs.copy.json').write_text(json.dumps(doc))
                out = Path(temp) / 'Gen.lean'
                result = subprocess.run(
                    [sys.argv[1], str(air), '-o', str(out), '--namespace', 'Rejected',
                     '--profile', 'abi64-le-v1'], capture_output=True, text=True, check=False)
                log = result.stdout + result.stderr
                if result.returncode == 0 or out.exists():
                    raise SystemExit(f'{version}: {name}: accepted')
                if message not in log:
                    raise SystemExit(f'{version}: {name}: wrong rejection: {log.strip()}')
    print(f'opaque pointer negatives: {len(CASES)} cases x {len(VERSIONS)} versions rejected')


if __name__ == '__main__':
    main()
