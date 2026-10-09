#!/usr/bin/env python3
"""Stub translator: writes the AIR function names it received to -o (STUB_TRANSLATE=fail|empty)."""
import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
out = Path(args[args.index('-o') + 1])
mode = os.environ.get('STUB_TRANSLATE')
if mode == 'fail':
    print('stub translator: unsupported')
    sys.exit(1)
names = sorted(json.loads(p.read_text())['name'] for p in Path(args[0]).glob('*.json'))
out.write_text('' if mode == 'empty' else '-- ' + json.dumps({'args': args[1:], 'functions': names}) + '\n')
