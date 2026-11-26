#!/usr/bin/env python3
"""Opaque-type entries the translator must reject through the CLI, each with its diagnostic.

Every case is the committed export of `copy` (`fn (*Handle) *Handle`) of each Zig version with
its type table changed: what an exporter that does not mark opaque types writes, an entry that
claims the primitive's name, an entry outside the schema, and pointer kinds that need the size
of the opaque type. Zig rejects the last ones at compile time; the translator must not rely on
that.

The cast cases change one side of a committed pointer cast into a slice (`erase`:
`*u32 → *Handle`; `recover`: `*Handle → *u32`, admitted under `--allocator-model translated`).
Zig has no cast between a slice and a pointer that is not a slice (`@ptrCast` of a slice casts
its `.ptr`); the model's slice is a pointer and a length, so the translation of such a cast
would not type in Lean.

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
    entry = dict(opaque(types))
    for t in pointers(types):
        t.clear()
        t.update(entry)


def typed_pointer_to_slice(types):
    # The `*u32` of the cast becomes `[]u32`: the other side stays `*Handle`.
    found = [t for t in types if t['k'] == 'ptr' and types[t['child']]['k'] == 'int']
    if len(found) != 1:
        raise SystemExit(f'expected one pointer to an integer in the export, found {len(found)}')
    found[0].update(size='slice', abi_size=16)


ONE_SLICE = 'a cast between a slice (a pointer and a length) and a type that is not a slice'
COPY = ('air', 'opaque_ptrs.copy.json', ())
# name: (the committed export: directory, file, translator arguments; the change; the diagnostic)
CASES = {
    'an export that does not mark the opaque type (kind other)':
        (COPY, unmarked, "type 'opaque_ptrs.Handle' is outside the subset (otherwise unsupported)"),
    'an opaque entry named anyopaque':
        (COPY, primitive_name, "a declared opaque type cannot have the primitive's name 'anyopaque'"),
    'an opaque entry without its module': (COPY, no_module, "missing 'module'"),
    'an opaque entry with fields': (COPY, with_fields, "unknown key 'fields'"),
    'an opaque entry with a size': (COPY, with_size, 'its entry cannot state a layout'),
    'a many-item pointer to the opaque type': (COPY, pointer_size('many'), NO_SIZE),
    'a slice of the opaque type': (COPY, pointer_size('slice'), NO_SIZE),
    'a C pointer to the opaque type': (COPY, pointer_size('c'), NO_SIZE),
    'the opaque type by value': (COPY, by_value, NO_SIZE),
    'a cast of a slice to an opaque pointer':
        (('air', 'opaque_ptrs.erase.json', ()), typed_pointer_to_slice, ONE_SLICE),
    'a cast of a slice to an opaque pointer (translated allocator model)':
        (('air', 'opaque_ptrs.erase.json', ('--allocator-model', 'translated')),
         typed_pointer_to_slice, ONE_SLICE),
    'a cast of an opaque pointer to a slice':
        (('air-recover', 'opaque_ptrs.recover.json', ('--allocator-model', 'translated')),
         typed_pointer_to_slice, ONE_SLICE),
    'a cast of an opaque pointer to a slice (default allocator model)':
        (('air-recover', 'opaque_ptrs.recover.json', ()), typed_pointer_to_slice, ONE_SLICE),
}


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    for version in VERSIONS:
        for name, ((directory, file, args), change, message) in CASES.items():
            doc = json.loads((HERE / directory / version / file).read_text())
            change(doc['types'])
            with tempfile.TemporaryDirectory(prefix='air2lean-opaque-pointers-') as temp:
                air = Path(temp) / 'air'
                air.mkdir()
                (air / file).write_text(json.dumps(doc))
                out = Path(temp) / 'Gen.lean'
                result = subprocess.run(
                    [sys.argv[1], str(air), '-o', str(out), '--namespace', 'Rejected',
                     '--profile', 'abi64-le-v1', *args], capture_output=True, text=True, check=False)
                log = result.stdout + result.stderr
                if result.returncode == 0 or out.exists():
                    raise SystemExit(f'{version}: {name}: accepted')
                if message not in log:
                    raise SystemExit(f'{version}: {name}: wrong rejection: {log.strip()}')
    print(f'opaque pointer negatives: {len(CASES)} cases x {len(VERSIONS)} versions rejected')


if __name__ == '__main__':
    main()
