#!/usr/bin/env python3
"""Check the fresh compiler inventory and exact unary ty_op payloads."""
import argparse
import json
from pathlib import Path

NAMES = {'reverse8', 'reverseSigned8', 'reverse1', 'reverse3', 'reverseSigned3',
         'reverse9', 'reverseSigned9', 'swap8', 'swapSigned8', 'swap16', 'swapSigned16',
         'swap24', 'swapSigned24', 'reverse64', 'reverseSigned64', 'swap64', 'swapSigned64',
         'reverse128', 'reverseSigned128', 'swap128', 'swapSigned128', 'reverseLanes',
         'reverseSignedLanes', 'swapLanes', 'swapSignedLanes', 'reverseNarrowLanes',
         'reverseZero', 'reverseSignedZero', 'swapZero', 'swapSignedZero'}

def walk(body):
    for inst in body:
        yield inst
        for name in ('body', 'then', 'else'):
            yield from walk(inst.get(name, []))
        for case in inst.get('cases', []):
            yield from walk(case.get('body', []))

def check(directory):
    files = list(directory.glob('*.json'))
    functions = [json.loads(path.read_text()) for path in files]
    names = [f['name'].removeprefix('byte_permutation.') for f in functions]
    if set(names) != NAMES or len(names) != len(NAMES):
        raise ValueError(f'export inventory mismatch: {names}')
    tags = set()
    for f in functions:
        instructions = list(walk(f['body']))
        ids = {i['id']: i for i in instructions}
        for inst in instructions:
            if inst['tag'] not in ('byte_swap', 'bit_reverse'):
                continue
            tags.add(inst['tag'])
            args = inst.get('args', [])
            if len(args) != 1 or 'inst' not in args[0]:
                raise ValueError(f'non-runtime/unary permutation in {f["name"]}')
            if ids[args[0]['inst']]['ty'] != inst['ty']:
                raise ValueError(f'permutation changes its operand type in {f["name"]}')
    if tags != {'byte_swap', 'bit_reverse'}:
        raise ValueError(f'missing fresh permutation tags: {tags}')
    print(f'{len(functions)} fresh compiler functions; both unary type-preserving permutation tags')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    check(parser.parse_args().directory)
