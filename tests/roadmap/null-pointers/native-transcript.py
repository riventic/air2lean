#!/usr/bin/env python3
"""L05: the native transcript of nullpointers.zig in the model's terms (check.sh --native).

usage: native-transcript.py VERSION EXIT_CODE STDERR [CASE EXIT_CODE STDERR]... > transcript

The first run is `main`. The model is `.illegal` where Zig 0.14.1/0.15.2 type a field pointer of
address zero as a nonnullable `*F` (`allowzeroNextPtr`, `nullNextPtr`): a non-`allowzero` pointer
must not be zero, so forming it is illegal behaviour that no check catches, and the native run
prints address 0 (docs/null-pointers.md §Address-zero projection policy). Zig 0.17.0 checks
`&n.*.next` of a null `[*c]Node` and panics, which ends the run: the last line becomes
`nullNextPtr panic`.

Each further run is one `case` variant, which ends the process: a null-unwrap safety panic is
`case NAME panic`; a segmentation fault (an access through address zero, which no check
catches) is `case NAME illegal`.
"""
import sys

PANIC = 'attempt to use null value'


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read().splitlines()


def main_run(version, code, lines):
    out = []
    for line in lines:
        if line.startswith('thread ') and 'panic: ' in line:
            if code == 0 or PANIC not in line:
                sys.exit(f'unexpected native panic: {line}')
            out.append('nullNextPtr panic')
            break
        if version.startswith(('0.14.', '0.15.')) and line in ('allowzeroNextPtr 0', 'nullNextPtr 0'):
            line = line.rsplit(' ', 1)[0] + ' illegal'
        out.append(line)
    else:
        if code != 0:
            sys.exit(f'native run failed with exit code {code} without a panic')
    return out


def case_run(name, code, lines):
    if code == 0:
        sys.exit(f'case {name} exited normally')
    if any(line.startswith('thread ') and f'panic: {PANIC}' in line for line in lines):
        return f'case {name} panic'
    if any(line.startswith('Segmentation fault at address 0x0') for line in lines):
        return f'case {name} illegal'
    sys.exit(f'case {name}: unexpected native failure (exit code {code}): {lines[:2]}')


def main(argv):
    if len(argv) < 4 or (len(argv) - 4) % 3:
        sys.exit(__doc__.split('\n\n')[1])
    out = main_run(argv[1], int(argv[2]), read(argv[3]))
    for i in range(4, len(argv), 3):
        out.append(case_run(argv[i], int(argv[i + 1]), read(argv[i + 2])))
    print('\n'.join(out))


if __name__ == '__main__':
    main(sys.argv)
