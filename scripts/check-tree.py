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
never git-based tools. In a restricted CI checkout (docs/ci.md#restricted-checkout) the withheld
files stay withheld in DEST: the placeholder, unreadable, never the checkout's file.

`--host-goldens VERSION` replaces each example's `Proofs/<Ex>/Gen.lean` with the committed
translation that scripts/check.sh compares on this host for Zig VERSION, when that is another
file: `tests/golden/VERSION/<ex>/Gen-<os>-<arch>.lean`, else `Gen-<os>.lean`, else
`tests/golden/VERSION/<ex>/Gen.lean` (os: `uname -s` in lower case, arch: `uname -m`). A run that
tests committed translations without exporting AIR (the build-mode runs) thereby tests this
host's translations, as check.sh does.

Each run recreates DEST from scratch. DEST must be new or an earlier check tree (it holds a
`.air2lean-check-tree.json` marker, written first), outside every tracked directory and cache.

  check-tree.py check-models VERSION EXAMPLE...

Fails unless each example's `Proofs/<Ex>/Gen.lean` in this tree (the checkout or a check tree)
is this host's translation for Zig VERSION, the stock Zig that scripts/diff.sh runs natively
against it: a fresh translation's first-line profile record names VERSION, and a committed body
equals the translation check.sh compares for VERSION on this host (the `--host-goldens` file,
else the checkout's `Proofs/<Ex>/Gen.lean`). A model of another Zig version is never compared
with this Zig's native code (docs/architecture-audit/soft-float-darwin.md).
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


def withheld_files(root):
    """{path: placeholder bytes} of the files a restricted CI checkout withholds (scripts/ci-reuse.py,
    docs/ci.md#restricted-checkout): the check tree withholds them too, without reading them."""
    git_dir = subprocess.run(['git', '-C', str(root), 'rev-parse', '--absolute-git-dir'], check=True,
                             capture_output=True, text=True).stdout.strip()
    state = Path(git_dir, 'air2lean-restricted.json')
    if not state.is_file():
        return {}
    data = json.loads(state.read_text())
    if data.get('discover'):  # scripts/ci-reuse.py restrict --discover keeps the checkout whole
        return {}
    placeholder = subprocess.run(['git', '-C', str(root), 'cat-file', 'blob', data['placeholder']], check=True,
                                 capture_output=True).stdout
    return dict.fromkeys(data['withheld'], placeholder)


def clone_tree(source, destination):
    """Copy a build cache, as a copy-on-write clone where the file system supports one."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    flag = '-c' if platform.system() == 'Darwin' else '--reflink=auto'
    if subprocess.run(['cp', '-R', flag, str(source), str(destination)], capture_output=True).returncode:
        shutil.rmtree(destination, ignore_errors=True)
        shutil.copytree(source, destination, symlinks=True)


def module_of(ex):
    """`Proofs/<Ex>/Gen.lean` of example `ex` (layout convention: first letter uppercased)."""
    return f'Proofs/{ex[0].upper()}{ex[1:]}/Gen.lean'


def host_golden(version, ex, root=ROOT, system=None, machine=None):
    """This host's committed translation of example `ex` for Zig `version` when it is not
    `Proofs/<Ex>/Gen.lean` (check.sh's lookup order), else None."""
    host_os = (system or platform.system()).lower()
    arch = machine or platform.machine()
    golden = Path(root) / 'tests/golden' / version / ex
    for name in (f'Gen-{host_os}-{arch}.lean', f'Gen-{host_os}.lean', 'Gen.lean'):
        if (golden / name).is_file():
            return golden / name
    return None


def host_goldens(version, root=ROOT, system=None, machine=None):
    """`--replace` specs for this host's committed translations of Zig `version` (check.sh's
    lookup order), for every example whose translation is not `Proofs/<Ex>/Gen.lean`."""
    specs = []
    for ex_dir in sorted((Path(root) / 'examples').iterdir()):
        golden = host_golden(version, ex_dir.name, root, system, machine)
        if golden:
            specs.append(f'{module_of(ex_dir.name)}={golden}')
    return specs


def split_generated(data):
    """(profile record or None, body) of a generated module (scripts/normalize-generated.py)."""
    spec = importlib.util.spec_from_file_location('air2lean_normalize',
                                                  Path(__file__).with_name('normalize-generated.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.split_generated(data)


def check_models(version, examples, root=ROOT, system=None, machine=None):
    """Raise ValueError unless each example's module in tree `root` is this host's translation
    for Zig `version` (see the module docstring)."""
    root = Path(root)
    marker = root / MARKER
    checkout = Path(json.loads(marker.read_text())['checkout']) if marker.is_file() else root
    for ex in examples:
        module = module_of(ex)
        metadata, body = split_generated((root / module).read_bytes())
        if metadata is not None:
            found = metadata['profile']['zig_version']
            if found != version:
                raise ValueError(f'{module} is the translation of Zig {found}, the native harness is '
                                 f'built with Zig {version}: set AIR2LEAN_ZIG to a Zig {found}')
            continue
        expected = host_golden(version, ex, root, system, machine)
        if expected is None:
            if checkout == root:
                continue  # The checkout's own module is the committed translation for `version`.
            expected = checkout / module
        if split_generated(expected.read_bytes())[1] != body:
            raise ValueError(f'{module} is not the translation of Zig {version} on this host '
                             f'({expected}): set AIR2LEAN_ZIG to the Zig whose translation this tree '
                             f'holds, or test Zig {version} with scripts/check.sh '
                             f'(AIR2LEAN_ZIG_VERSION={version}) or check-tree.py --host-goldens {version}')


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
    withheld = withheld_files(root)
    for path in files:
        if path in withheld:
            (dest / path).parent.mkdir(parents=True, exist_ok=True)
            (dest / path).write_bytes(withheld[path])
            os.chmod(dest / path, 0)
        elif os.path.lexists(root / path):  # Else deleted in the working tree.
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
    models = sub.add_parser('check-models')
    models.add_argument('version')
    models.add_argument('examples', nargs='+')
    args = parser.parse_args(argv)
    try:
        if args.command == 'check-models':
            check_models(args.version, args.examples)
        else:
            create(args.dest, args.replace + (host_goldens(args.host_goldens) if args.host_goldens else []))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
