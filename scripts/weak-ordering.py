#!/usr/bin/env python3
"""T04 weak ordering: run the litmus tests natively and check the outcomes against the model.

  weak-ordering.py observe --zig ZIG --target TRIPLE --output FILE
  weak-ordering.py check FILE...

`observe` builds tests/roadmap/weak-ordering/litmus.zig with the stock compiler ZIG for TRIPLE
(aarch64-linux-gnu or aarch64-macos-none, ReleaseSafe, LLVM, baseline CPU) and runs it; it runs
only on the profile's own host (scripts/aarch64-abi.py's PROFILES), so a host exclusion is never
an observation. FILE gets a `meta` line and one `litmus` line per test.

`check` runs tests/roadmap/weak-ordering/Litmus.lean on the files (`lake env lean --run`): every
observed outcome must be an outcome of the model's atomics (docs/weak-ordering.md). Exit 0: every
outcome allowed; 1: an outcome the model does not allow (a soundness finding), or an error; 3:
excluded (wrong host).
"""
import argparse
import importlib.util
import platform
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
LITMUS = ROOT / 'tests/roadmap/weak-ordering/litmus.zig'
MODEL = 'tests/roadmap/weak-ordering/Litmus.lean'
EXCLUDED = 3


def profiles():
    spec = importlib.util.spec_from_file_location('aarch64_abi', ROOT / 'scripts/aarch64-abi.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.PROFILES


def observe(zig, target, output):
    system, machines, cpu = profiles()[target]
    if platform.system() != system or platform.machine() not in machines:
        print(f'excluded: {target} runs only natively on {system}/{"|".join(machines)}, '
              f'not {platform.system()}/{platform.machine()}', file=sys.stderr)
        return EXCLUDED
    zig = str(Path(zig).resolve(strict=True))
    version = subprocess.run([zig, 'version'], stdout=subprocess.PIPE, check=True,
                             timeout=60).stdout.decode().strip()
    with tempfile.TemporaryDirectory(prefix='air2lean-weak-') as tmp:
        binary = Path(tmp) / 'litmus'
        subprocess.run([zig, 'build-exe', '-fllvm', '-OReleaseSafe', '-target', target,
                        f'-mcpu={cpu}', f'-femit-bin={binary}', str(LITMUS)],
                       check=True, timeout=600)
        done = subprocess.run([str(binary)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              check=True, timeout=600)
    lines = [line for line in done.stderr.decode().splitlines() if line.startswith('litmus ')]
    output.write_text(f'meta zig {version} target {target} mode ReleaseSafe backend llvm\n'
                      + ''.join(line + '\n' for line in lines), encoding='utf-8')
    print(f'observed {len(lines)} litmus tests on {target} with Zig {version}: {output}')
    return 0


def check(files):
    return subprocess.run(['lake', 'env', 'lean', '--run', MODEL, *map(str, files)],
                          cwd=ROOT).returncode


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    sub = parser.add_subparsers(dest='action', required=True)
    obs = sub.add_parser('observe')
    obs.add_argument('--zig', required=True)
    obs.add_argument('--target', required=True, choices=('aarch64-linux-gnu', 'aarch64-macos-none'))
    obs.add_argument('--output', type=Path, required=True)
    chk = sub.add_parser('check')
    chk.add_argument('files', type=Path, nargs='+')
    args = parser.parse_args(argv)
    if args.action == 'observe':
        return observe(args.zig, args.target, args.output)
    return 1 if check(args.files) else 0


if __name__ == '__main__':
    sys.exit(main())
