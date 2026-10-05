#!/usr/bin/env python3
"""Run semantic mutants sequentially in temporary copies; coordinator must guard compilers."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
MUTANTS = {
    'ignore-failure-trace': (' or std.mem.indexOfScalar(usize, self.failures, k) != null', ''),
    'ignore-request-cap': (' or len > self.request_cap', ''),
    'omit-live-removal': ('                _ = self.live.swapRemove(i);', '                _ = i;'),
}

def mutated(source, name):
    before, after = MUTANTS[name]
    if source.count(before) != 1:
        raise ValueError(f'{name}: mutation anchor must occur exactly once')
    return source.replace(before, after)


def main():
    source = (ROOT / 'tests/diff/common.zig').read_text()
    zig = os.environ.get('AIR2LEAN_ZIG', 'zig')
    # A compiler/build failure is not mutation detection. Only the fixture's explicit
    # outcome/ownership assertion errors qualify. Time/resource kills also fail the test.
    for name in MUTANTS:
        with tempfile.TemporaryDirectory(prefix='allocation-policy-mutant-') as temp:
            work = Path(temp)
            (work / 'common.zig').write_text(mutated(source, name))
            shutil.copyfile(ROOT / 'tests/diff/compat.zig', work / 'compat.zig')
            binary = work / 'fixture'
            subprocess.run([zig, 'build-exe', '-OReleaseSafe', '-mcpu=baseline',
                f'-femit-bin={binary}', '--dep', 'common',
                '-Mroot=tests/roadmap/allocation-policy/fixture.zig',
                f'-Mcommon={work / "common.zig"}'], cwd=ROOT, check=True)
            result = subprocess.run([str(binary)], capture_output=True, text=True)
            if result.returncode != 1 or 'error: PolicyOrCleanupMismatch' not in result.stderr:
                raise RuntimeError(f'{name}: expected an explicit semantic assertion failure, got {result.returncode}')
            print(f'{name}: detected by fixture outcome/ownership assertion')

if __name__ == '__main__':
    main()
