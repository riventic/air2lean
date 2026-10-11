#!/usr/bin/env python3
"""x86_64-windows-gnu: what the translator admits and what it rejects (docs/windows-target.md).

Each case translates tests/roadmap/windows-target/air/<case>/ (recorded Zig 0.17.0 exports for
x86_64-windows-gnu) with the translator given as the first argument.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PREFIX = '-- air2lean-profile: '


def translate(binary, case, *extra):
    with tempfile.TemporaryDirectory(prefix='air2lean-windows-') as tmp:
        out = Path(tmp) / 'Gen.lean'
        done = subprocess.run([str(binary), str(HERE / 'air' / case), '-o', str(out),
                               '--namespace', 'WindowsTarget', '--prefix', f'{case}.', *extra],
                              text=True, capture_output=True, check=False)
        return done, (out.read_text() if done.returncode == 0 else '')


def rejects(binary, case, needle, *extra):
    done, _ = translate(binary, case, *extra)
    assert done.returncode != 0, f'{case}: accepted, expected a rejection with {needle!r}'
    assert needle in done.stderr, f'{case}: {done.stderr}'


def header(text):
    first = text.splitlines()[0]
    assert first.startswith(PREFIX), first
    return json.loads(first[len(PREFIX):])


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    # Pure code translates; `c_long` is the 32-bit integer the exporter writes; `neg` of an f80
    # does not use the x87 precision control.
    done, text = translate(binary, 'pure')
    assert done.returncode == 0, done.stderr
    meta = header(text)
    assert meta['profile']['target_triple'].startswith('x86_64-windows'), meta
    assert 'admission' not in meta, meta
    # An f80 division depends on the thread's x87 precision control: rejected without the
    # admission, admitted (and recorded) with it.
    rejects(binary, 'x87', 'x87 result depends on the thread\'s precision control')
    done, text = translate(binary, 'x87', '--assume-x87-extended')
    assert done.returncode == 0, done.stderr
    assert header(text)['admission'] == 'x87-extended', header(text)
    # Thread-local storage and the std thread model rest on the OS layer, which Windows lacks.
    rejects(binary, 'tls', 'thread-local storage rests on the OS')
    rejects(binary, 'spawn', "the std model of 'Thread.spawn' is outside the x86_64-windows model")
    # A Windows OS call is an unbound extern, with the reason.
    rejects(binary, 'oscall', 'the OS primitives of x86_64-windows have no model yet')
    print('windows-target: 6 cases as expected')


if __name__ == '__main__':
    main()
