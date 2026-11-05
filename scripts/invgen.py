#!/usr/bin/env python3
"""The generated loop invariants (P09, docs/invariant-synthesis.md): every committed `Inv.lean`.

    python3 -B scripts/invgen.py check|write [INV_LEAN...]

`TARGETS` lists each `Inv.lean` with the fixture root it is elaborated under (`lean -R`), the
translated module it is generated from and that module's namespace. For each target (all, or the
given paths), the translated module is compiled into a scratch directory and `air2lean-invgen`
(`lake exe`, which builds it) writes the file there. `check` fails when a committed file differs
from it; `write` replaces the stale ones. The translated modules must be current first
(`scripts/gen-integrity.py`): scripts/regen.py runs this as its `invgen` step, right after `gen`,
and a fixture check repeats the comparison for the file it proves against. Lean runs unguarded here: callers
run it under scripts/build-guard.py. `scripts/gen-integrity.py invgen` checks the files' records
(generator revision, source hashes) without running Lean.
"""
import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The library module that air2lean-invgen imports besides the translated module: `fsym` for the
# Houdini pruning walks.
LIBRARY = 'ZigLean.Sep.Full.AutoAll'

# (Inv.lean, fixture root, translated module, its namespace)
TARGETS = [
    ('tests/roadmap/loop-tactics/nested/Nested/Inv.lean', 'tests/roadmap/loop-tactics/nested',
     'Nested.Gen', 'Nested'),
    ('tests/roadmap/loop-tactics/counted/Counted/Inv.lean', 'tests/roadmap/loop-tactics/counted',
     'Counted.Gen', 'Counted'),
]


def source(root, module):
    """The source of the translated `module` of the fixture at `root`: the generator's input
    (`--source`), which `scripts/gen-integrity.py invgen` checks the record against."""
    return f"{root}/{module.replace('.', '/')}.lean"


def generate(root, module, namespace, work):
    """`air2lean-invgen`'s output for `module` (a module of the fixture at `root`), as bytes."""
    # (here, not at the top: scripts/gen-integrity.py reads TARGETS and `source` without Lean)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from theorem_universe import compile_unit, with_lean_path
    rel = module.replace('.', '/')
    src = source(root, module)
    lean_path = [work / 'olean']
    log = work / 'compile.log'
    subprocess.run([sys.executable, '-B', 'scripts/lean-deps.py', '--build', src], cwd=ROOT, check=True)
    error = compile_unit(src, root, work / 'olean' / (rel + '.olean'), lean_path, log)
    if error:
        sys.exit(log.read_text()[-4000:] + error)
    out = work / 'Inv.lean'
    subprocess.run(['lake', 'exe', 'air2lean-invgen', module, namespace, '--source', src, '-o', str(out)],
                   cwd=ROOT, env=with_lean_path(lean_path), check=True)
    return out.read_bytes()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('mode', choices=['check', 'write'])
    parser.add_argument('paths', nargs='*', help='Inv.lean files of TARGETS (default: all)')
    args = parser.parse_args(argv)
    known = {target[0]: target for target in TARGETS}
    unknown = [p for p in args.paths if p not in known]
    if unknown:
        parser.error('not a target of scripts/invgen.py: ' + ', '.join(unknown))
    stale = []
    # The library the generator imports for its pruning walks (Air2Lean/InvGenMain.lean).
    subprocess.run(['lake', 'build', '-q', LIBRARY], cwd=ROOT, check=True)
    for path, root, module, namespace in [known[p] for p in args.paths] or TARGETS:
        with tempfile.TemporaryDirectory(prefix='air2lean-invgen.') as work:
            fresh = generate(root, module, namespace, Path(work))
        committed = ROOT / path
        if committed.is_file() and committed.read_bytes() == fresh:
            continue
        if args.mode == 'check':
            stale.append(path)
        else:
            committed.write_bytes(fresh)
            print('wrote ' + path)
    if stale:
        sys.exit('stale generated invariants (regenerate with scripts/invgen.py write): ' + ', '.join(stale))


if __name__ == '__main__':
    main()
