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

The generator gets the semantic fingerprints of the module's functions (`fingerprints`: a source
map of a fresh translation of the module's committed AIR, so the translator must be built) and
records, per loop, the function that runs it and its fingerprint; `check` names the functions
whose fingerprints changed in each stale file.
"""
import argparse
import functools
import json
import os
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The library modules that air2lean-invgen imports besides the translated module: `fsym` for the
# Houdini pruning walks, and the counted loop rule for the check of the credit-mode invariants.
LIBRARY = ['ZigLean.Sep.Full.AutoAll', 'ZigLean.Sep.Full.Cost']

# (Inv.lean, fixture root, translated module, its namespace)
TARGETS = [
    ('tests/roadmap/loop-tactics/nested/Nested/Inv.lean', 'tests/roadmap/loop-tactics/nested',
     'Nested.Gen', 'Nested'),
    ('tests/roadmap/loop-tactics/counted/Counted/Inv.lean', 'tests/roadmap/loop-tactics/counted',
     'Counted.Gen', 'Counted'),
    ('Proofs/Lists/OpenInv.lean', '.', 'Proofs.Lists.Open', 'Lists.Open'),
    ('Proofs/Lists/AllocInv.lean', '.', 'Proofs.Lists.Open', 'Lists.Open'),
]

# A target generated with contracts (`air2lean-invgen --spec … --contract …`): the hand-written
# specification module that states them (a module of the repository's own Lake package, built by
# `lake build`) and the rules. The file then holds the loops that call by one of them; the
# module's other loops are in its target without contracts.
CONTRACTS = {
    'Proofs/Lists/AllocInv.lean': ('Proofs.Lists.AllocNode', ['Lists.Alloc.destroy_fields']),
}


def source(root, module):
    """The source of the translated `module` of the fixture at `root`: the generator's input
    (`--source`), which `scripts/gen-integrity.py invgen` checks the record against."""
    return (Path(root) / f"{module.replace('.', '/')}.lean").as_posix()


@functools.cache
def integrity():
    """The globals of scripts/gen-integrity.py (run once): its translation cases (`FIXTURES`,
    `Case`, `Translator`), its record prefix and its cached sibling loader."""
    return runpy.run_path(str(Path(__file__).with_name('gen-integrity.py')))


def fingerprints(src, work):
    """`[definition, fingerprint]` of each function of the translated module `src`: its semantic
    fingerprint (docs/stable-generation.md) from a source map of a fresh translation of the
    module's committed AIR (its case of scripts/gen-integrity.py), without the translator's and the
    runtime's revisions. Those two change every fingerprint, at every translator or runtime change,
    while only a change of what they emit or of the library's pruning changes an `Inv.lean`: the
    input hash of the record and `check` cover them. So a fingerprint changes when the function's
    translated AIR, a callee's, the target profile or the translation options change."""
    checks = integrity()
    cases = [case for case in checks['FIXTURES'] if case[0] == src]
    if len(cases) != 1:
        sys.exit(f'{src}: {len(cases)} translation cases in scripts/gen-integrity.py FIXTURES, not one')
    path, air, args, mode = cases[0]
    translator = os.environ.get('AIR2LEAN_TRANSLATOR', str(ROOT / '.lake/build/bin/air2lean'))
    if not os.access(translator, os.X_OK):
        sys.exit('build the translator first: lake build air2lean')
    # (the case's translation as scripts/gen-integrity.py makes it, with the source map)
    sidecar = work / 'Gen.source-map.json'
    case = checks['Case'](path, [ROOT / air], [*args, '--source-map-json', str(sidecar)], mode, path)
    try:
        checks['Translator'](translator, work).output(0, case)
    except ValueError as error:
        sys.exit(f'{src}: {error}')
    semantic = checks['sibling']('semantic-fingerprints.py')
    doc = semantic['load_sidecar'](sidecar)
    unversioned = dict(doc, translator=dict(doc['translator'], revision=''),
                       runtime=dict(doc['runtime'], revision=''))
    return sorted([e['definition'], e['fingerprint']] for e in semantic['fingerprints'](unversioned).values())


def changed_functions(committed, fresh):
    """The functions whose fingerprints differ between the records of two generated files (each
    loop's `function` and `fingerprint`), with their loops; a function only one record has
    counts as changed."""
    def loops(text):
        prefix = integrity()['INVGEN_PREFIX']
        first = text.split(b'\n', 1)[0]
        if not first.startswith(prefix):
            raise ValueError('no record')
        record = json.loads(first[len(prefix):])
        return [(e['loop'], e['function'], e['fingerprint']) for e in record['loops']]
    try:
        old, new = loops(committed), loops(fresh)
    except (ValueError, KeyError, TypeError):
        return 'no comparable record'
    def prints(entries):
        return {f: fp for _, f, fp in entries}
    before, after = prints(old), prints(new)
    changed = sorted(f for f in before.keys() | after.keys() if before.get(f) != after.get(f))
    return ', '.join(f"{f} ({', '.join(sorted({l for l, g, _ in old + new if g == f}))})"
                     for f in changed) or 'none'


def generate(root, module, namespace, work, spec=None, contracts=()):
    """`air2lean-invgen`'s output for `module` (a module of the fixture at `root`), as bytes; with
    the contracts `contracts` of the specification module `spec`, if given."""
    # (here, not at the top: scripts/gen-integrity.py reads TARGETS and `source` without Lean)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from theorem_universe import compile_unit, with_lean_path
    rel = module.replace('.', '/')
    src = source(root, module)
    (work / 'fingerprints.json').write_text(json.dumps(fingerprints(src, work)))
    lean_path = [work / 'olean']
    log = work / 'compile.log'
    subprocess.run([sys.executable, '-B', 'scripts/lean-deps.py', '--build', src], cwd=ROOT, check=True)
    error = compile_unit(src, root, work / 'olean' / (rel + '.olean'), lean_path, log)
    if error:
        sys.exit(log.read_text()[-4000:] + error)
    out = work / 'Inv.lean'
    options = []
    if spec:
        if root != '.':
            sys.exit(f'{spec}: a specification module must be in the repository\'s Lake package (root ".")')
        subprocess.run(['lake', 'build', '-q', spec], cwd=ROOT, check=True)
        options += ['--spec', spec, source(root, spec)]
        for contract in contracts:
            options += ['--contract', contract]
    subprocess.run(['lake', 'exe', 'air2lean-invgen', module, namespace, '--source', src, *options,
                    '--fingerprints', str(work / 'fingerprints.json'), '-o', str(out)],
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
    subprocess.run(['lake', 'build', '-q', *LIBRARY], cwd=ROOT, check=True)
    for path, root, module, namespace in [known[p] for p in args.paths] or TARGETS:
        with tempfile.TemporaryDirectory(prefix='air2lean-invgen.') as work:
            fresh = generate(root, module, namespace, Path(work), *CONTRACTS.get(path, ()))
        committed = ROOT / path
        if committed.is_file() and committed.read_bytes() == fresh:
            continue
        if args.mode == 'check':
            changed = changed_functions(committed.read_bytes(), fresh) if committed.is_file() else 'new file'
            stale.append(f'{path} (functions changed: {changed})')
        else:
            committed.write_bytes(fresh)
            print('wrote ' + path)
    if stale:
        sys.exit('stale generated invariants (regenerate with scripts/invgen.py write): ' + ', '.join(stale))


if __name__ == '__main__':
    main()
