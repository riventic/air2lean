#!/usr/bin/env python3
"""Rewrite provenance.json after a re-export: source, compiler and per-file AIR hashes.

usage: provenance.py <patched zig (zig-unlocked)> <stock zig 0.16.0>
"""
import hashlib
import json
import pathlib
import sys

here = pathlib.Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


record = {
    'source_sha256': {n: sha(here / n) for n in ('arena.zig', 'native.zig', 'upstream/oob_gep.zig')},
    'air': {
        'zig_version': '0.16.0', 'schema': 12,
        'targets': {'linux': 'x86_64-linux', 'macos': 'aarch64-macos'},
        'cpu': 'baseline', 'optimization': 'ReleaseSafe', 'error_tracing': False,
        'command': 'ZIG_AIR_JSON_DIR=<dir> ZIG_AIR_JSON_FILTER=arena.,heap.,mem.,math.,debug.assert,posix. '
                   'zig build-obj -fno-emit-bin -OReleaseSafe '
                   '-fno-error-tracing -target <triple> -mcpu=baseline arena.zig',
        'selection': 'call/function-value closure of the exported arena.* functions, stopping '
                     'at debug.FullPanic and posix.mmap/munmap/mremap (the trusted OS boundary)',
    },
    'patched_compiler': 'zig-patch/air-json/json.zig of codex/alloc-milestone1 (the P0 exporter: '
                        'global initializers and container layouts resolved before writing; schema 12 '
                        'module identity and instance keys)',
    'patched_compiler_sha256': sha(sys.argv[1]),
    'stock_compiler_sha256': sha(sys.argv[2]),
    'air_sha256': {str(p.relative_to(here / 'air')): sha(p)
                   for p in sorted((here / 'air').rglob('*.json'))},
}
(here / 'provenance.json').write_text(json.dumps(record, indent=2) + '\n')
