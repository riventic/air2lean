#!/usr/bin/env python3
"""T04: qualify one aarch64 profile from native probe output and its versioned expected file.

  aarch64-abi.py observe --zig ZIG --target TRIPLE [--mode MODE] --output FILE
  aarch64-abi.py compare --target TRIPLE [--mode MODE] OBSERVED
  aarch64-abi.py check   --zig ZIG --target TRIPLE [--mode MODE] [--output FILE]

TRIPLE is aarch64-linux-gnu or aarch64-macos-none; MODE is ReleaseSafe (default). `observe`
builds and runs, with the stock compiler ZIG, tests/roadmap/aarch64-abi/probe.zig, L09's
tests/roadmap/vector-layouts/probe.zig, and the atomic-width limit probe that must fail to
compile; it runs only on the profile's own host (no emulator, no cross execution). `compare`
compares an observation file line by line with
tests/roadmap/aarch64-abi/expected/<zig>/<triple>-<mode>.txt. `check` is observe + compare.

Every command prints one JSON status line. Exit 0: `match`; 1: `mismatch` (or an error);
3: `excluded` (wrong host, no expected file for this Zig version). An exclusion is never a
match: it exits non-zero, and nothing records it as qualification evidence.
"""
import argparse
import difflib
import hashlib
import json
import platform
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
DIR = 'tests/roadmap/aarch64-abi'
PROBE = f'{DIR}/probe.zig'
LIMIT = f'{DIR}/atomic-limit.zig'
VECTORS = 'tests/roadmap/vector-layouts/probe.zig'
COMPAT = 'tests/diff/compat.zig'
# triple -> (platform.system(), platform.machine() values, Zig -mcpu)
PROFILES = {'aarch64-linux-gnu': ('Linux', ('aarch64', 'arm64'), 'baseline'),
            'aarch64-macos-none': ('Darwin', ('arm64',), 'baseline')}
MODES = ('ReleaseSafe',)
LIMIT_ERROR = re.compile(r'error: (expected \d+-bit integer type or smaller; found \d+-bit integer type)')
EXCLUDED, MISMATCH = 3, 1


class Excluded(Exception):
    pass


def expected_path(version, triple, mode):
    return ROOT / DIR / 'expected' / version / f'{triple}-{mode}.txt'


def build(zig, target, mode, root, out, compat=True):
    command = [zig, 'build-exe', '-fllvm', '-O' + mode, '-target', target, '-mcpu=baseline',
               '-femit-bin=' + str(out)]
    command += ['--dep', 'compat', '-Mroot=' + str(ROOT / root), '-Mcompat=' + str(ROOT / COMPAT)] \
        if compat else [str(ROOT / root)]
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)


def run(binary, stream):
    done = subprocess.run([str(binary)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
                          check=True)
    return getattr(done, stream).decode('utf-8')


def observe(zig, target, mode):
    system, machines, _ = PROFILES[target]
    if platform.system() != system or platform.machine() not in machines:
        raise Excluded(f'{target} runs only natively on {system}/{"|".join(machines)}, '
                       f'not {platform.system()}/{platform.machine()}')
    zig = str(Path(zig).resolve(strict=True))
    version = subprocess.run([zig, 'version'], stdout=subprocess.PIPE, check=True,
                             timeout=60).stdout.decode().strip()
    lines = []
    with tempfile.TemporaryDirectory(prefix='air2lean-t04-') as tmp:
        tmp = Path(tmp)
        for root, binary, stream, compat in ((PROBE, tmp / 'probe', 'stdout', True),
                                             (VECTORS, tmp / 'vectors', 'stderr', False)):
            built = build(zig, target, mode, root, binary, compat)
            if built.returncode:
                raise ValueError(f'{root} failed to compile:\n' + built.stderr.decode()[:4096])
            lines += run(binary, stream).splitlines()
        # Synchronization boundary: the widest atomic integer the compiler accepts.
        limit = build(zig, target, mode, LIMIT, tmp / 'limit', compat=False)
        found = LIMIT_ERROR.search(limit.stderr.decode())
        if limit.returncode == 0 or not found:
            raise ValueError(f'{LIMIT} must fail with the atomic width error; got exit '
                             f'{limit.returncode}:\n' + limit.stderr.decode()[:4096])
        lines.append('limit atomic_u256 ' + found.group(1).replace(' ', '_'))
    return version, '\n'.join(lines) + '\n'


def compare(text, target, mode, version):
    path = expected_path(version, target, mode)
    if not path.is_file():
        raise Excluded(f'no expected results for Zig {version} {target} {mode} '
                       f'({path.relative_to(ROOT)})')
    expected = path.read_text(encoding='utf-8')
    status = {'target': target, 'mode': mode, 'zig': version,
              'expected': str(path.relative_to(ROOT)),
              'expected_sha256': hashlib.sha256(expected.encode()).hexdigest(),
              'observed_sha256': hashlib.sha256(text.encode()).hexdigest(),
              'lines': len(expected.splitlines())}
    if text == expected:
        return {**status, 'status': 'match'}
    diff = list(difflib.unified_diff(expected.splitlines(), text.splitlines(), 'expected',
                                     'observed', lineterm='', n=0))
    return {**status, 'status': 'mismatch', 'diff': diff[:200]}


def version_of(text):
    found = re.search(r'^meta zig (\S+)$', text, re.M)
    if not found:
        raise ValueError('observation has no `meta zig` line')
    return found.group(1)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('observe', 'compare', 'check'):
        cmd = sub.add_parser(name)
        cmd.add_argument('--target', required=True, choices=sorted(PROFILES))
        cmd.add_argument('--mode', default='ReleaseSafe', choices=MODES)
        if name != 'compare':
            cmd.add_argument('--zig', required=True)
        if name == 'compare':
            cmd.add_argument('observed', type=Path)
        else:
            cmd.add_argument('--output', type=Path, required=name == 'observe')
    args = parser.parse_args(argv)
    try:
        if args.action == 'compare':
            text = args.observed.read_text(encoding='utf-8')
            version = version_of(text)
        else:
            version, text = observe(args.zig, args.target, args.mode)
            if version_of(text) != version:
                raise ValueError(f'probe reports Zig {version_of(text)}, `zig version` {version}')
            if args.output:
                args.output.write_text(text, encoding='utf-8')
            if args.action == 'observe':
                print(json.dumps({'target': args.target, 'mode': args.mode, 'zig': version,
                                  'status': 'observed', 'output': str(args.output)}))
                return 0
        status = compare(text, args.target, args.mode, version)
    except Excluded as why:
        print(json.dumps({'target': args.target, 'mode': args.mode, 'status': 'excluded',
                          'reason': str(why)}))
        return EXCLUDED
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f'aarch64-abi: {error}', file=sys.stderr)
        return MISMATCH
    print(json.dumps(status, indent=2))
    return 0 if status['status'] == 'match' else MISMATCH


if __name__ == '__main__':
    sys.exit(main())
