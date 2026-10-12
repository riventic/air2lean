#!/usr/bin/env python3
"""Derived workspace that builds alternative translations without touching the checkout.

  check-tree.py create DEST [--replace PATH=SOURCE ...] [--host-goldens VERSION]

Verification never writes a tracked file (docs/generated-code.md#check-trees). To build or
differentially test a module other than the committed one (one Zig version's or host OS's
`Proofs/<Ex>/Gen.lean`), this makes DEST a copy of the checkout's working tree (tracked and
unignored untracked files, and the materialized whole-tree generated files), replaces each PATH with SOURCE (paths relative to the current
directory), and clones the checkout's Lake build caches (`.lake/build`, `tests/diff/.lake`) into
it: Lake traces are content-based, so only the replaced modules and their dependents rebuild
there. DEST is not a git checkout: run Lake, scripts/diff.sh and the Lean checks inside it,
never git-based tools.

`--host-goldens VERSION` replaces each example's `Proofs/<Ex>/Gen.lean` with the committed
translation that scripts/check.sh compares on this host for Zig VERSION, when that is another
file: `tests/golden/VERSION/<ex>/Gen-<os>-<arch>.lean`, else `Gen-<os>.lean`, else
`tests/golden/VERSION/<ex>/Gen.lean` (os: `uname -s` in lower case, arch: `uname -m`). A run that
tests committed translations without exporting AIR (the build-mode runs) thereby tests this
host's translations, as check.sh does.

Each run recreates DEST from scratch. DEST must be new or an earlier check tree (it holds a
`.air2lean-check-tree.json` marker, written first), outside every tracked directory and cache.
"""
import argparse
import hashlib
import importlib.util
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


def generated_paths(root):
    """The whole-tree generated files of `root` (scripts/generated.py paths; none without a registry)."""
    if not (Path(root) / 'assurance/generated.json').is_file():
        return set()
    spec = importlib.util.spec_from_file_location('air2lean_generated', Path(__file__).with_name('generated.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.paths(root)


def clone_tree(source, destination):
    """Copy a build cache, as a copy-on-write clone where the file system supports one."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    flag = '-c' if platform.system() == 'Darwin' else '--reflink=auto'
    if subprocess.run(['cp', '-R', flag, str(source), str(destination)], capture_output=True).returncode:
        shutil.rmtree(destination, ignore_errors=True)
        shutil.copytree(source, destination, symlinks=True)


def host_goldens(version, root=ROOT, system=None, machine=None):
    """`--replace` specs for this host's committed translations of Zig `version` (check.sh's
    lookup order), for every example whose translation is not `Proofs/<Ex>/Gen.lean`."""
    host_os = (system or platform.system()).lower()
    arch = machine or platform.machine()
    specs = []
    for ex_dir in sorted((Path(root) / 'examples').iterdir()):
        ex = ex_dir.name
        golden = Path(root) / 'tests/golden' / version / ex
        for name in (f'Gen-{host_os}-{arch}.lean', f'Gen-{host_os}.lean', 'Gen.lean'):
            if (golden / name).is_file():
                module = f'Proofs/{ex[0].upper()}{ex[1:]}/Gen.lean'
                specs.append(f'{module}={golden / name}')
                break
    return specs


def create(dest, replacements, root=ROOT):
    """Make DEST the checkout `root` with each 'PATH=SOURCE' of `replacements` applied."""
    root, dest = Path(root).resolve(), Path(os.path.realpath(dest))
    listed = subprocess.run(['git', '-C', str(root), 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
                            check=True, capture_output=True).stdout
    # Lake's own directories (build caches, check reports, check trees) are never sources.
    files = {p for p in os.fsdecode(listed).split('\0') if p and '.lake' not in Path(p).parts}
    # The whole-tree generated files materialized in the checkout (ignored, never committed:
    # assurance/generated.json, docs/ci.md#whole-tree-generated-files) belong to this tree too.
    files = sorted(files | {p for p in generated_paths(root) if (root / p).is_file()})
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
    make.add_argument('--host-goldens', metavar='VERSION',
                      help="replace each example's module with this host's committed translation")
    args = parser.parse_args(argv)
    try:
        create(args.dest, args.replace + (host_goldens(args.host_goldens) if args.host_goldens else []))
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
