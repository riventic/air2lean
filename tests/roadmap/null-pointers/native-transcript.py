#!/usr/bin/env python3
"""L05: the native transcript of nullpointers.zig in the model's terms (check.sh --native).

usage: native-transcript.py VERSION EXIT_CODE STDERR > transcript

The model is `.illegal` where Zig 0.14.1/0.15.2 type a field pointer of address zero as a
nonnullable `*F` (`allowzeroNextPtr`, `nullNextPtr`): a non-`allowzero` pointer must not be zero, so
forming it is illegal behaviour that no check catches, and the native run prints address 0
(docs/null-pointers.md §Address-zero projection policy). Zig 0.17.0 checks `&n.*.next` of a null
`[*c]Node` and panics, which ends the run: the last line becomes `nullNextPtr panic`.
"""
import sys

version, code, path = sys.argv[1], int(sys.argv[2]), sys.argv[3]
lines = open(path, encoding='utf-8').read().splitlines()
out = []
for line in lines:
    if line.startswith('thread ') and 'panic: ' in line:
        if code == 0 or 'attempt to use null value' not in line:
            sys.exit(f'unexpected native panic: {line}')
        out.append('nullNextPtr panic')
        break
    if version.startswith(('0.14.', '0.15.')) and line in ('allowzeroNextPtr 0', 'nullNextPtr 0'):
        line = line.rsplit(' ', 1)[0] + ' illegal'
    out.append(line)
else:
    if code != 0:
        sys.exit(f'native run failed with exit code {code} without a panic')
print('\n'.join(out))
