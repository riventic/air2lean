#!/usr/bin/env python3
"""Stub patched compiler for project.py export tests.

`version` prints STUB_ZIG_VERSION. `build-obj` appends its argv and filter to STUB_LOG and
writes AIR for every function of the STUB_PROGRAM call graph ({name: [callees]}) whose name
matches a ZIG_AIR_JSON_FILTER prefix. STUB_EXIT forces an exit status; STUB_PROFILE (JSON)
is written into every AIR file as its build profile.
"""
import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
if args == ['version']:
    print(os.environ.get('STUB_ZIG_VERSION', '0.16.0'))
    sys.exit(0)
if not args or args[0] != 'build-obj':
    sys.exit(2)
prefixes = [p for p in os.environ.get('ZIG_AIR_JSON_FILTER', '').split(',') if p]
with open(os.environ['STUB_LOG'], 'a', encoding='utf-8') as log:
    log.write(json.dumps({'argv': args, 'filter': prefixes,
                          'cwd': os.getcwd(), 'env_dir': os.environ.get('ZIG_AIR_JSON_DIR')}) + '\n')
    for arg in args:
        if arg.startswith('-M') and '=' in arg:
            path = Path(arg.split('=', 1)[1])
            log.write(json.dumps({'module': arg.split('=', 1)[0][2:], 'text': path.read_text()}) + '\n')
if os.environ.get('STUB_EXIT'):
    print('stub compiler failure', file=sys.stderr)
    sys.exit(int(os.environ['STUB_EXIT']))
program = json.loads(Path(os.environ['STUB_PROGRAM']).read_text())
types = [{'k': 'ptr', 'size': 'one', 'const': True, 'child': 2}, {'k': 'int', 'signed': False, 'bits': 32},
         {'k': 'other', 'name': 'fn (u32) u32'}]
out = Path(os.environ['ZIG_AIR_JSON_DIR'])
for name, callees in program.items():
    if not any(name.startswith(p) for p in prefixes):
        continue
    body = [{'id': i, 'tag': 'call', 'ty': 1, 'callee': {'ty': 0, 'func': c, 'noreturn': False}, 'args': []}
            for i, c in enumerate(callees)]
    air = {'schema': 11, 'zig_version': os.environ.get('STUB_AIR_VERSION', '0.16.0'), 'name': name,
           'params': [], 'ret': 1, 'body': body, 'types': types}
    if os.environ.get('STUB_PROFILE'):
        air['schema'] = 12
        air['profile'] = json.loads(os.environ['STUB_PROFILE'])
    (out / f'{name}.json').write_text(json.dumps(air))
if os.environ.get('STUB_WARN'):
    print('air2lean: no JSON for x', file=sys.stderr)
