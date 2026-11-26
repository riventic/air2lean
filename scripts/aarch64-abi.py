#!/usr/bin/env python3
"""T04: qualify one aarch64 profile from native probe output and its versioned expected file.

  aarch64-abi.py observe --zig ZIG --target TRIPLE [--mode MODE] --output FILE
  aarch64-abi.py compare --target TRIPLE [--mode MODE] OBSERVED
  aarch64-abi.py check   --zig ZIG --target TRIPLE [--mode MODE] [--output FILE]

TRIPLE is aarch64-linux-gnu or aarch64-macos-none; MODE is ReleaseSafe (default). `observe`
builds and runs, with the stock compiler ZIG, tests/roadmap/aarch64-abi/probe.zig, L09's
tests/roadmap/vector-layouts/probe.zig, and the limit probes (tests/roadmap/aarch64-abi/limits/)
that must fail to compile, one result line each, and then probe.zig again at each other CPU of
the profile (`CPUS`), as `cpu` rows; it runs only on the profile's own host (no emulator, no
cross execution). `compare` compares an observation file line by line with
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
LIMITS = f'{DIR}/limits'
VECTORS = 'tests/roadmap/vector-layouts/probe.zig'
COMPAT = 'tests/diff/compat.zig'
# triple -> (platform.system(), platform.machine() values, Zig -mcpu)
PROFILES = {'aarch64-linux-gnu': ('Linux', ('aarch64', 'arm64'), 'baseline'),
            'aarch64-macos-none': ('Darwin', ('arm64',), 'baseline')}
# triple -> the other `-mcpu` values at which `probe.zig` is observed (`cpu` rows): the profile's
# baseline with the features that decide how floats and atomics lower switched (`fullfp16`: an
# `f16` multiply-add; `lse`, `lse2`, `rcpc`, `outline_atomics`: atomic instructions or helper
# calls). Each needs only features of ARMv8.2 hosts.
CPUS = {'aarch64-linux-gnu': ('generic+fullfp16', 'generic+lse+rcpc', 'generic+outline_atomics'),
        'aarch64-macos-none': ('generic', 'generic+lse', 'apple_m1-fullfp16',
                               'apple_m1+outline_atomics')}
MODES = ('ReleaseSafe',)
# The first compile error of a probe that must be rejected: `<file>.zig:<line>:<col>: error: <message>`.
LIMIT_ERROR = re.compile(r'\.zig:\d+:\d+: error: (.+)$', re.M)
# An LLVM backend failure without a source location (`LLVM ERROR: Broken module found, ...` after
# an abort, or `error: Invalid cast (Producer: 'zig <v>' Reader: 'LLVM <v>')`), without the
# parenthesized versions, so that the line is the same for every Zig version with the same failure.
# LLVM prints its error right after the last line of the verifier's IR dump, without a newline.
LLVM_ERROR = re.compile(r'(?:LLVM ERROR|^error): (.+?)(?: \(.*\))?$', re.M)
F80_PROBE = f'{DIR}/atomic_f80.zig'
# Every atomic op that Sema might accept on a float cell, each built on its own (`atomic_f80.zig`).
F80_OPS = ('load_monotonic', 'load_acquire', 'load_seq_cst', 'store_monotonic', 'store_release',
           'store_seq_cst', 'rmw_Xchg', 'rmw_Add', 'rmw_Sub', 'rmw_Max', 'rmw_Min', 'cmpxchg_strong',
           'cmpxchg_weak')
EXCLUDED, MISMATCH = 3, 1


class Excluded(Exception):
    pass


def expected_path(version, triple, mode):
    return ROOT / DIR / 'expected' / version / f'{triple}-{mode}.txt'


def build(zig, target, mode, root, out, deps=(), cpu='baseline'):
    """`zig build-exe` of `root` with the modules `deps` (name, path) imported by name."""
    command = [zig, 'build-exe', '-fllvm', '-O' + mode, '-target', target, '-mcpu=' + cpu,
               '-femit-bin=' + str(out)]
    for name, _ in deps:
        command += ['--dep', name]
    command.append('-Mroot=' + str(ROOT / root))
    command += [f'-M{name}={path}' for name, path in deps]
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600)


def f80_atomic(zig, target, mode, tmp, op):
    """The `f80atomic` row of `op` (`F80_OPS`): `zig <error>` if Sema rejects it, `llvm <error>` if
    the LLVM backend fails on it, else `runs cell=<model|other> result=<model|other>` (the exit
    code of `atomic_f80.zig`)."""
    module = tmp / 'op.zig'
    module.write_text(f'pub const name: []const u8 = "{op}";\n', encoding='utf-8')
    built = build(zig, target, mode, F80_PROBE, tmp / 'f80', deps=(('op', module),))
    if built.returncode:
        stderr = built.stderr.decode(errors='replace')
        found = LIMIT_ERROR.search(stderr)
        if found:
            return f'f80atomic {op} zig ' + found.group(1).replace(' ', '_')
        found = LLVM_ERROR.search(stderr)
        if not found:
            raise ValueError(f'{F80_PROBE} ({op}) failed without a compile error:\n' + stderr[:4096])
        return f'f80atomic {op} llvm ' + found.group(1).replace(' ', '_')
    code = subprocess.run([str(tmp / 'f80')], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          timeout=60).returncode
    if code not in range(4):
        raise ValueError(f'{F80_PROBE} ({op}) exited with {code}')
    cell = 'model' if code & 1 else 'other'
    result = 'model' if code & 2 else 'other'
    return f'f80atomic {op} runs cell={cell} result={result}'


def cpu_rows(cpu, baseline, observed):
    """The `cpu` rows of `probe.zig` at `-mcpu=<cpu>`: each line that differs from the baseline's
    line at its place, and how many lines are the same."""
    if len(observed) != len(baseline):
        raise ValueError(f'{PROBE} prints {len(observed)} lines at -mcpu={cpu}, {len(baseline)} at '
                         'the baseline')
    changed = [new for old, new in zip(baseline, observed) if old != new]
    return [f'cpu {cpu} {line}' for line in changed] + \
        [f'cpu {cpu} same {len(baseline) - len(changed)} of {len(baseline)}']


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

        def output(root, stream, deps=(), cpu='baseline'):
            built = build(zig, target, mode, root, tmp / 'probe', deps, cpu)
            if built.returncode:
                raise ValueError(f'{root} failed to compile at -mcpu={cpu}:\n' +
                                 built.stderr.decode()[:4096])
            return run(tmp / 'probe', stream).splitlines()

        compat = (('compat', ROOT / COMPAT),)
        baseline = output(PROBE, 'stdout', compat)
        lines += baseline + output(VECTORS, 'stderr')
        # Synchronization boundaries the compiler must reject (widest atomic integer, orderings,
        # operand types): one line each with the first compile error.
        for source in sorted((ROOT / LIMITS).glob('*.zig')):
            limit = build(zig, target, mode, f'{LIMITS}/{source.name}', tmp / 'limit')
            found = LIMIT_ERROR.search(limit.stderr.decode())
            if limit.returncode == 0 or not found:
                raise ValueError(f'{source.name} must fail to compile with an error; got exit '
                                 f'{limit.returncode}:\n' + limit.stderr.decode()[:4096])
            lines.append(f'limit {source.stem} ' + found.group(1).replace(' ', '_'))
        # Atomic `f80`: whether each op compiles, and if it runs, whether it does the op.
        lines += [f80_atomic(zig, target, mode, tmp, op) for op in F80_OPS]
        # The other CPUs: the whole probe again, as its differences from the baseline.
        for cpu in CPUS[target]:
            lines += cpu_rows(cpu, baseline, output(PROBE, 'stdout', compat, cpu))
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
