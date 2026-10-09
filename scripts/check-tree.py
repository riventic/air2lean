#!/usr/bin/env python3
"""Derived workspace that builds alternative translations without touching the checkout.

  check-tree.py create DEST [--replace PATH=SOURCE ...]

Verification never writes a tracked file (docs/generated-code.md#check-trees). To build or
differentially test a module other than the committed one (one Zig version's or host OS's
`Proofs/<Ex>/Gen.lean`), this makes DEST a copy of the checkout's working tree (tracked and
unignored untracked files), replaces each PATH with SOURCE (paths relative to the current
directory), and clones the checkout's Lake build caches (`.lake/build`, `tests/diff/.lake`) into
it: Lake traces are content-based, so only the replaced modules and their dependents rebuild
there. DEST is not a git checkout: run Lake, scripts/diff.sh and the Lean checks inside it,
never git-based tools.

Each run recreates DEST from scratch. DEST must be new or an earlier check tree (it holds a
`.air2lean-check-tree.json` marker, written first), outside every tracked directory and cache.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
MARKER = '.air2lean-check-tree.json'
CACHES = ('.lake/build', 'tests/diff/.lake')


def clone_tree(source, destination):
    """Copy a build cache, as a copy-on-write clone where the file system supports one."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    flag = '-c' if platform.system() == 'Darwin' else '--reflink=auto'
    if subprocess.run(['cp', '-R', flag, str(source), str(destination)], capture_output=True).returncode:
        shutil.rmtree(destination, ignore_errors=True)
        shutil.copytree(source, destination, symlinks=True)


def create(dest, replacements, root=ROOT):
    """Make DEST the checkout `root` with each 'PATH=SOURCE' of `replacements` applied."""
    root, dest = Path(root).resolve(), Path(os.path.realpath(dest))
    listed = subprocess.run(['git', '-C', str(root), 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
                            check=True, capture_output=True).stdout
    # Lake's own directories (build caches, check reports, check trees) are never sources.
    files = sorted({p for p in os.fsdecode(listed).split('\0') if p and '.lake' not in Path(p).parts})
    if dest == root or root.is_relative_to(dest):
        raise ValueError(f'{dest}: a check tree cannot contain the checkout')
    if dest.is_relative_to(root):
        top = dest.relative_to(root).parts[0]
        if any(Path(p).parts[0] == top for p in files) or any(dest.is_relative_to(root / c) for c in CACHES):
            raise ValueError(f'{dest}: a check tree cannot be inside a source directory or build cache')
    if dest.exists() and not (dest / MARKER).is_file():
        raise ValueError(f'{dest}: exists and is not a check tree ({MARKER} missing)')
    replaced = {}
    for spec in replacements:
        path, sep, source = spec.partition('=')
        if not sep or Path(path).is_absolute() or '..' in Path(path).parts or not Path(source).is_file():
            raise ValueError(f'bad --replace {spec!r}: want RELATIVE_PATH=EXISTING_FILE')
        replaced[path] = (source, Path(source).read_bytes())
    shutil.rmtree(dest, ignore_errors=True)
    dest.mkdir(parents=True)
    # First: an interrupted run leaves a tree the next run may replace.
    marker = dict(format='air2lean-check-tree-v1', checkout=str(root),
                  replaced={path: dict(source=source, sha256=hashlib.sha256(data).hexdigest())
                            for path, (source, data) in replaced.items()})
    (dest / MARKER).write_text(json.dumps(marker, indent=2, sort_keys=True) + '\n')
    for path in files:
        if os.path.lexists(root / path):  # Else deleted in the working tree.
            (dest / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / path, dest / path, follow_symlinks=False)
    for path, (_, data) in replaced.items():  # A new example's module need not exist yet.
        (dest / path).parent.mkdir(parents=True, exist_ok=True)
        (dest / path).unlink(missing_ok=True)  # Never write through a copied symlink.
        (dest / path).write_bytes(data)
    for cache in CACHES:
        if (root / cache).is_dir():
            clone_tree(root / cache, dest / cache)
    return dest


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    make = sub.add_parser('create')
    make.add_argument('dest')
    make.add_argument('--replace', action='append', default=[], metavar='PATH=SOURCE')
    args = parser.parse_args(argv)
    try:
        create(args.dest, args.replace)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
