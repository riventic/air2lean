#!/usr/bin/env python3
"""The examples that a change can affect, for quick local runs (never CI's selection).

    python3 scripts/changed-examples.py [--base REF] [EXAMPLE...]

scripts/example-selection.sh applies it to the default selection of check.sh, diff.sh and
build-mode-docker.sh when AIR2LEAN_CHANGED_FROM=REF is set (an explicit AIR2LEAN_EXAMPLES wins).

Changed paths: the commits since the merge base with REF (default origin/main), staged and
unstaged changes and untracked files. A path inside one example's own files (examples/<ex>/,
tests/diff/<ex>/, tests/golden/<ex>/, tests/golden/<version>/<ex>/, Proofs/<Ex>/) selects that
example. Documentation (docs/, top-level *.md) selects none. Any other path (the translator, the
runtime library, scripts, the harness runner, toolchain pins, ...) can change every example, so
it selects all of them. Prints the selected EXAMPLEs (default: every examples/ directory)
space-separated in their order, or nothing when none is affected. CI and the merge queue
always run every example.
"""
import argparse
from pathlib import Path, PurePosixPath
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.run(['git', '-C', str(ROOT), *args], check=True, capture_output=True,
                          text=True).stdout.split('\0')


def changed_paths(base):
    merge_base = subprocess.run(['git', '-C', str(ROOT), 'merge-base', base, 'HEAD'], check=True,
                                capture_output=True, text=True).stdout.strip()
    paths = git('diff', '-z', '--name-only', '--no-renames', merge_base) + git('ls-files', '-z', '--others', '--exclude-standard')
    return sorted({p for p in paths if p})


def affected(paths, examples):
    """The examples `paths` can affect: a subset of `examples`, or all of them."""
    selected = set()
    by_namespace = {ex[:1].upper() + ex[1:]: ex for ex in examples}
    for path in map(PurePosixPath, paths):
        parts = path.parts
        if parts[0] == 'docs' or (len(parts) == 1 and path.suffix == '.md'):
            continue
        owner = None
        if parts[0] == 'examples' and len(parts) > 2:
            owner = parts[1]
        elif parts[:2] == ('tests', 'diff') and len(parts) > 3:
            owner = parts[2]
        elif parts[:2] == ('tests', 'golden') and len(parts) > 3:
            owner = parts[2] if parts[2] in examples else parts[3] if len(parts) > 4 else None
        elif parts[0] == 'Proofs' and len(parts) > 2:
            owner = by_namespace.get(parts[1])
        if owner not in examples:
            return list(examples)
        selected.add(owner)
    return [ex for ex in examples if ex in selected]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--base', default='origin/main')
    parser.add_argument('examples', nargs='*')
    args = parser.parse_args(argv)
    known = sorted(p.name for p in (ROOT / 'examples').iterdir() if p.is_dir())
    selected = affected(changed_paths(args.base), known)
    print(' '.join(ex for ex in (args.examples or known) if ex in selected))
    return 0


if __name__ == '__main__':
    sys.exit(main())
