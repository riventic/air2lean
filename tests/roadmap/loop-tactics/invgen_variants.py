#!/usr/bin/env python3
"""P09 retranslation (docs/invariant-synthesis.md, "Retranslation"): another translation of a
program needs a regeneration of its invariants and no hand edit.

    python3 -B tests/roadmap/loop-tactics/invgen_variants.py CLIENT [VARIANT...]

A client (`CLIENTS`) is a program with generated loop invariants and the hand-written files that
are proved over them: specifications and proofs, which exist once. Each of its variants
(scripts/invgen.py `VARIANTS`: another Zig version, permuted struct fields) is a fixture root with
another translation under the same module names and the invariants generated from it. For each
variant (default: all of the client):

* the translation is the translator's output for the variant's committed AIR
  (scripts/gen-integrity.py) and each generated `Inv.lean` is the generator's output for that
  translation (scripts/invgen.py check): both are regenerated, nothing else is;
* the client's hand-written files are elaborated against the variant as they are
  (scripts/lean_overlay.py: the variant's modules replace the first translation's, and every
  module that imports one is compiled again);
* each seeded mutant of the client's `mutants.json` (invgen_mutants.py: `old` replaced by `new` in
  the variant's generated invariants) still elaborates and makes the proof fail inside one of the
  mutant's theorems. A mutant may name its generated file (`inv`, a path below the fixture root;
  default: the client's first) and the hand-written file that must fail (`proof`; default: the
  client's first).

A variant with a source of its own (`source`: permuted struct fields) must differ from the
client's source only in the declaration it names.

Needs a built translator (lake build air2lean); builds the generator and the library modules it
needs itself; no Zig compiler. Lean runs unguarded: run it under scripts/build-guard.py.
AIR2LEAN_MUTANT_JOBS mutants run at a time (default 1).
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import invgen  # noqa: E402
import invgen_mutants  # noqa: E402
import lean_overlay  # noqa: E402

LOOPS = 'tests/roadmap/loop-tactics'
# root: the fixture root of the first translation (the key of scripts/invgen.py VARIANTS);
# files: the hand-written files, relative to the repository; mutants: the seeded mutants;
# source: the program, and the declaration in which a variant's own source may differ.
CLIENTS = {
    'counted': {'root': f'{LOOPS}/counted', 'files': [f'{LOOPS}/counted/Proof.lean'],
                'mutants': f'{LOOPS}/counted/mutants.json'},
    'nested': {'root': f'{LOOPS}/nested', 'files': [f'{LOOPS}/nested/Proof.lean'],
               'mutants': f'{LOOPS}/nested/mutants.json'},
    'lists': {'root': '.', 'mutants': f'{LOOPS}/lists/mutants.json',
              'files': ['Proofs/Lists/Linked.lean', 'Proofs/Lists/Alloc.lean', 'Proofs/Lists/Bounded.lean',
                        f'{LOOPS}/Queue.lean'],
              'source': ('examples/lists/lists.zig', r'pub const Node = (?:extern )?struct \{.*?\n\};\n'),
              # `Node` as an `extern struct`: `val` at offset 0, `next` at 8. The generator follows
              # (scripts/invgen.py PARTIAL); `Linked.node` states `next` at 0 and `val` at 8.
              'rejected': {'layout': {'file': 'Proofs/Lists/Linked.lean', 'in': ['reverse_thread', 'sum_total'],
                                      'families': ['reverse.loop6', 'sum.loop6']}}},
}


def same_but(source, variant, declaration):
    """Why the variant's source is not `source` with only the declaration matched by
    `declaration` changed (to one with the same fields), or None."""
    texts = [(ROOT / p).read_text() for p in (source, variant)]
    found = [re.search(declaration, t, re.S) for t in texts]
    if not all(found):
        return f'{variant}: no declaration {declaration!r} in it or in {source}'
    if [t[:m.start()] + t[m.end():] for t, m in zip(texts, found)][0] != \
            [t[:m.start()] + t[m.end():] for t, m in zip(texts, found)][1]:
        return f'{variant} differs from {source} outside the declaration {declaration!r}'
    fields = [sorted(line.strip() for line in m.group(0).splitlines()[1:-1]) for m in found]
    if fields[0] != fields[1]:
        return f'{variant}: the fields of the declaration are not those of {source}'
    return None


def mutate(client, overlay, vroot, work, mutant, spans):
    """Why `mutant` was not rejected inside its theorems, or None."""
    targets = [target for root, _, target in invgen.variants() if root == vroot]
    inv = mutant.get('inv', Path(targets[0][0]).relative_to(vroot).as_posix())
    proof = mutant.get('proof', client['files'][0])
    if proof not in spans:
        spans[proof] = invgen_mutants.spans(ROOT / proof)
    missing = [t for t in mutant['in'] if t not in spans[proof]]
    if missing:
        return f"{proof} has no theorem {', '.join(missing)}"
    text = (ROOT / vroot / inv).read_text()
    lo, hi, where = 0, len(text), 'the generated file'
    if 'def' in mutant:
        span = invgen_mutants.scope(text, mutant['def'])
        if span is None:
            return f"{vroot}/{inv} does not have exactly one definition {mutant['def']}"
        lo, hi, where = *span, mutant['def']
    if text.count(mutant['old'], lo, hi) != 1:
        return f"{mutant['old']!r} does not occur exactly once in {where} of {vroot}/{inv}"
    mdir = work / f"mutant-{mutant['name']}"
    (mdir / 'src' / inv).parent.mkdir(parents=True)
    (mdir / 'src' / inv).write_text(text[:lo] + text[lo:hi].replace(mutant['old'], mutant['new']) + text[hi:])
    layer = lean_overlay.Overlay([mdir / 'src'], mdir / 'olean', below=overlay)
    try:
        result = layer.elaborate(proof, client['root'])
    except lean_overlay.Failed as error:  # the mutant itself, or a file between it and the proof
        return f'{error}: {error.output[-600:]}'
    if result.returncode == 0:
        return 'accepted'
    lines = [int(n) for n in re.findall(re.escape(Path(proof).name) + r':(\d+):\d+: error', result.stdout)]
    if not any(a <= n < b for t in mutant['in'] for a, b in [spans[proof][t]] for n in lines):
        return f"no error in {', '.join(mutant['in'])}: {result.stdout[-600:]}"
    return None


def rejected(name, expected, overlay, vroot, root):
    """The errors of a variant whose layout a hand-written file states otherwise: the generator
    still finds an invariant for each loop of `expected['families']`, and `expected['file']` is
    rejected inside each theorem of `expected['in']` (its specification does not hold of this
    translation: it is not proved of it, and it is not regenerated either)."""
    prefix = invgen.integrity()['INVGEN_PREFIX'].decode()
    families = {}
    for root_, _, target in invgen.variants():
        if root_ == vroot:
            record = json.loads((ROOT / target[0]).read_text().split('\n', 1)[0][len(prefix):])
            families.update({e['loop']: e.get('family') for e in record['loops']})
    missing = [loop for loop in expected['families'] if not families.get(loop)]
    if missing:
        return [f"{vroot}: no generated invariant for {', '.join(missing)}"]
    file = expected['file']
    try:
        result = overlay.elaborate(file, root)
    except lean_overlay.Failed as error:
        return [f'{vroot}: {error}:\n{error.output[-3000:]}']
    spans = invgen_mutants.spans(ROOT / file)
    lines = [int(n) for n in re.findall(re.escape(Path(file).name) + r':(\d+):\d+: error', result.stdout)]
    kept = [t for t in expected['in'] if not any(spans[t][0] <= n < spans[t][1] for n in lines)]
    if result.returncode == 0 or kept:
        return [f"{vroot}: {file} states another layout and must be rejected in {', '.join(expected['in'])}; "
                f"not rejected: {', '.join(kept) or 'the file'}"]
    print(f"{name}/{Path(vroot).name}: invariants generated for {', '.join(expected['families'])}; "
          f"{file}, which states the first layout, is rejected in {', '.join(expected['in'])}", flush=True)
    return []


def check(name, client, vroot, work):
    """The errors of the variant at `vroot`."""
    variant = Path(vroot).name
    targets = [target[0] for root, _, target in invgen.variants() if root == vroot]
    for command in (['scripts/gen-integrity.py', 'check', '--only', vroot + '/'],
                    ['scripts/invgen.py', 'check', *targets]):
        if subprocess.run([sys.executable, '-B', *command], cwd=ROOT).returncode:
            return [f"{vroot}: {' '.join(command)} failed"]
    own = Path(vroot).parent.parent / variant / Path(client.get('source', ('x', ''))[0]).name
    if 'source' in client and (ROOT / own).is_file():
        error = same_but(client['source'][0], own.as_posix(), client['source'][1])
        if error:
            return [error]
    # The variant's modules in front of the first translation's (a fixture's own root, or the
    # Lake package).
    overlay = lean_overlay.Overlay([vroot] + ([client['root']] if client['root'] != '.' else []),
                                   work / 'olean')
    if variant in client.get('rejected', {}):
        return rejected(name, client['rejected'][variant], overlay, vroot, client['root'])
    try:
        for file in client['files']:
            overlay.check(file, client['root'])
            print(f'{name}/{variant}: {file} checked against the retranslation, unchanged', flush=True)
    except lean_overlay.Failed as error:
        return [f'{vroot}: {error} (regeneration was not enough):\n{error.output[-3000:]}']
    mutants = json.loads((ROOT / client['mutants']).read_text())
    spans = {}
    with ThreadPoolExecutor(max_workers=int(os.environ.get('AIR2LEAN_MUTANT_JOBS', '1'))) as pool:
        results = list(pool.map(lambda m: mutate(client, overlay, vroot, work, m, spans), mutants))
    for mutant, why in zip(mutants, results):
        if not why:
            print(f"{name}/{variant}: mutant {mutant['name']} of the generated invariant rejected", flush=True)
    return [f"{vroot}: mutant {m['name']}: {why}" for m, why in zip(mutants, results) if why]


def main(argv):
    if not argv or argv[0] not in CLIENTS:
        sys.exit(__doc__)
    name, client = argv[0], CLIENTS[argv[0]]
    directory, names = invgen.VARIANTS[client['root']]
    unknown = [v for v in argv[1:] if v not in names]
    if unknown:
        sys.exit(f"{name}: no variant {', '.join(unknown)} (scripts/invgen.py VARIANTS: {', '.join(names)})")
    subprocess.run(['lake', 'build', '-q', 'air2lean-invgen'], cwd=ROOT, check=True)
    errors = []
    for variant in argv[1:] or names:
        with tempfile.TemporaryDirectory(prefix=f'air2lean-variant-{name}.') as work:
            errors += check(name, client, f'{directory}/{variant}', Path(work))
    if errors:
        sys.exit('\n'.join(errors))
    print(f"{name}: {len(argv[1:] or names)} retranslation(s) checked")


if __name__ == '__main__':
    main(sys.argv[1:])
