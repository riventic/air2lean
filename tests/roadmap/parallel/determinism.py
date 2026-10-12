#!/usr/bin/env python3
"""Run a command with AIR2LEAN_JOBS=1 and then with N workers; require identical results.

    determinism.py [--jobs N] [--output PATH]... [--keep DIR] -- COMMAND...

Each run starts after every --output path (a file or directory, relative to the current
directory) is removed. The runs must agree on the exit status, stdout, stderr and the bytes of
every file under each --output path. Dropped from both
streams first: Lake's build progress lines (`✔ [3/9] Built X (1.2s)`, `Build completed
successfully (9 jobs).`), which record which modules this run had to build and how long they took
(the cache state the first run leaves, not the worker count), and `real/user/sys` timing lines.
Made constant: mktemp directory names (`air2lean-NAME.XXXXXX`) and unittest's `Ran N tests in Ts`.
Nothing else is normalized. --keep DIR keeps both runs' captures (DIR/sequential, DIR/parallel).

Exit status: 0 when the runs agree, 1 with a unified diff of the first differences otherwise.
"""
import argparse
import difflib
import filecmp
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

PROGRESS = re.compile(rb'^(?:(?:\xe2\x9c\x94|\xe2\x9a\xa0|\xe2\x9c\x96) )?\[\d+/\d+\] (?:Built|Replayed|Ran|Fetched) .*\n|'
                      rb'^Build completed successfully(?: \(\d+ jobs\))?\.\n|^(?:real|user|sys)\s+\S+\n', re.M)

# Names that differ per run by construction: mktemp directories and unittest's elapsed time.
RUN_NAMES = re.compile(rb'(air2lean-[A-Za-z-]+)\.[A-Za-z0-9]{6}\b|^(Ran \d+ tests?) in [\d.]+s$', re.M)


def normalize(data: bytes) -> bytes:
    return RUN_NAMES.sub(lambda m: (m.group(1) + b'.X') if m.group(1) else m.group(2), PROGRESS.sub(b'', data))


def capture(command, jobs, outputs, into: Path) -> None:
    for path in outputs:
        if path.is_dir():
            shutil.rmtree(path)
        elif path.exists():
            path.unlink()
    result = subprocess.run(command, env=dict(os.environ, AIR2LEAN_JOBS=str(jobs)),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    into.mkdir(parents=True)
    (into / 'status').write_text(f'{result.returncode}\n')
    (into / 'stdout').write_bytes(normalize(result.stdout))
    (into / 'stderr').write_bytes(normalize(result.stderr))
    for index, path in enumerate(outputs):
        target = into / 'outputs' / f'{index}-{path.name}'
        target.parent.mkdir(exist_ok=True)
        if path.is_dir():
            shutil.copytree(path, target, symlinks=True)
        elif path.exists():
            shutil.copy2(path, target)


def differences(left: Path, right: Path, rel=Path('.')):
    """Relative paths whose presence or bytes differ."""
    found = []
    comparison = filecmp.dircmp(left / rel, right / rel)
    found += [rel / name for name in comparison.left_only + comparison.right_only + comparison.funny_files]
    for name in comparison.common_files:
        if (left / rel / name).read_bytes() != (right / rel / name).read_bytes():
            found.append(rel / name)
    for name in comparison.common_dirs:
        found += differences(left, right, rel / name)
    return sorted(found)


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if '--' not in argv:
        print(__doc__, file=sys.stderr)
        return 2
    split = argv.index('--')
    parser = argparse.ArgumentParser(usage='%(prog)s [--jobs N] [--output PATH]... [--keep DIR] -- COMMAND...')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--output', type=Path, action='append', default=[])
    parser.add_argument('--keep', type=Path)
    args = parser.parse_args(argv[:split])
    command = argv[split + 1:]
    if not command or args.jobs < 2:
        parser.error('a COMMAND and --jobs of at least 2 are required')
    work = Path(tempfile.mkdtemp(prefix='air2lean-determinism.'))
    try:
        capture(command, 1, args.output, work / 'sequential')
        capture(command, args.jobs, args.output, work / 'parallel')
        found = differences(work / 'sequential', work / 'parallel')
        for rel in found[:10]:
            left, right = work / 'sequential' / rel, work / 'parallel' / rel
            if left.is_file() and right.is_file():
                sys.stderr.writelines(difflib.unified_diff(
                    left.read_text(errors='replace').splitlines(True)[:5000],
                    right.read_text(errors='replace').splitlines(True)[:5000],
                    f'sequential/{rel}', f'parallel/{rel}', n=2))
            else:
                print(f'only in one run: {rel}', file=sys.stderr)
        status = (work / 'sequential/status').read_text().strip()
        print(f'determinism: {" ".join(command)}: AIR2LEAN_JOBS=1 and {args.jobs}: exit {status}, '
              + (f'{len(found)} differing files' if found else 'identical stdout, stderr and outputs'))
        return 1 if found else 0
    finally:
        if args.keep:
            shutil.copytree(work, args.keep, dirs_exist_ok=True)
        shutil.rmtree(work)


if __name__ == '__main__':
    sys.exit(main())
