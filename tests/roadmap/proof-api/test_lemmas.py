"""ROOT-only driver for `--proof-api` unfolding/step lemmas; never invokes Zig or Lean itself.

On committed golden AIR (memory, loops, recursion, errors, concurrency), with the built
translator:

(a) default output (no `--proof-api`) is the committed golden body, and the flag only adds
    lemma blocks: removing them gives the default output back byte for byte;
(b) renumbered AIR (random exporter IDs, shifted debug lines) gives identical lemma names
    and statements;
(c) an added unrelated generic instance leaves every existing lemma name and statement
    unchanged;
(d) a semantic change to one function changes that function's lemma statements, keeps
    their names, and leaves every other function's lemmas unchanged (callers' proofs are
    invalidated through `scripts/semantic-fingerprints.py`, not through statements).

`--retain DIR` keeps the generated modules and downstream clients that use only the
generated lemma names, for kernel checking with `lake env lean` (docs/generated-code.md).
`DIR/*.lean` must check; `DIR/changed/*.lean` (the same clients after the semantic change)
must fail.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import random
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('stable', ROOT/'tests/roadmap/stable-generation/test_cli.py')
stable = importlib.util.module_from_spec(spec); spec.loader.exec_module(stable)
spec = importlib.util.spec_from_file_location('normalizer', ROOT/'scripts/normalize-generated.py')
normalizer = importlib.util.module_from_spec(spec); spec.loader.exec_module(normalizer)

# Example -> function to mutate for (d) (None: no supported mutation site).
# Shared golden AIR that translates on its own to the committed Proofs/<Ex>/Gen.lean.
EXAMPLES = dict(basic='basic.sum', recursion='recursion.isEven', pointers='pointers.addTo',
                errors='errors.parseDigit', variants=None, atomics=None, iogroup=None,
                threads=None, options=None, floats=None, vectors=None, asm=None)
BASE = re.compile(r'air2lean_api(?:_\d+)+?(?=_(?:model|unfold|loop\d+_))')
RECORD = '-- air2lean-proof-lemmas: '


def api(source):
    return 'air2lean_api' + ''.join('_' + str(b) for b in source.encode())


# Downstream clients: statements and proofs mention only generated lemma names (and the
# runtime's `Zig.loop`), never loop/again definitions, exit constructors or locals.
CLIENTS = dict(
    basic=lambda ns: f'''
-- Unfold the function, then step its loop once: the empty array exits immediately.
example : {ns}.{api('basic.sum')}_model #[] = pure 0 := by
  rw [{ns}.{api('basic.sum')}_unfold]
  simp only [pure_bind]
  rw [{ns}.{api('basic.sum')}_loop0_step]
  rfl

-- Two steps: one element is added, then the loop exits. A semantic change to `sum`
-- (`<` becomes `>`) keeps every name but makes this client fail to check.
example : {ns}.{api('basic.sum')}_model #[5] = pure 5 := by
  rw [{ns}.{api('basic.sum')}_unfold]
  simp only [pure_bind]
  rw [{ns}.{api('basic.sum')}_loop0_step, {ns}.{api('basic.sum')}_loop0_step]
  rfl

-- The step lemma is the loop rule over the stable body/again names.
example (p0 : Array (BitVec 32)) (n : BitVec 64) :
    {ns}.{api('basic.sum')}_loop0_body p0 n >>= (fun e =>
      if {ns}.{api('basic.sum')}_loop0_again e then
        Zig.loop ({ns}.{api('basic.sum')}_loop0_body p0 n) {ns}.{api('basic.sum')}_loop0_again
      else pure e) =
    Zig.loop ({ns}.{api('basic.sum')}_loop0_body p0 n) {ns}.{api('basic.sum')}_loop0_again :=
  ({ns}.{api('basic.sum')}_loop0_step p0 n).symm
''',
    recursion=lambda ns: f'''
-- A `partial_fixpoint` function unfolds through its equation lemma.
example : {ns}.{api('recursion.fact')}_model 0 = pure 1 := by
  rw [{ns}.{api('recursion.fact')}_unfold]
  rfl
''')


def blocks(text):
    """`base -> [chunk]` for every `--proof-api` chunk, and the text without them."""
    found, kept = {}, []
    for chunk in text.split('\n\n'):
        head = chunk.lstrip('\n')
        if head.startswith(('-- air2lean-proof-', 'abbrev air2lean_api', 'theorem air2lean_api')):
            match = BASE.search(head)
            assert match, head[:200]
            found.setdefault(match.group(0), []).append(chunk)
        else:
            kept.append(chunk)
    return found, '\n\n'.join(kept)


def statements(found):
    """Lemma blocks without the scalar `air2lean-proof-api-v1` record, whose source map holds
    exporter debug lines (provenance; its facts are checked by test_cli.py)."""
    return {base: ['\n'.join(line for line in chunk.split('\n')
                             if not line.startswith('-- air2lean-proof-api: ')) for chunk in chunks]
            for base, chunks in found.items()}


def records(text):
    found = [json.loads(line[len(RECORD):]) for line in text.splitlines() if line.startswith(RECORD)]
    return {record['source']: record for record in found}


def check_example(binary, ex, target, work, retain):
    golden = ROOT/'tests/golden'/ex/'air'
    docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]
    names = sorted(doc['name'] for doc in docs)
    ns = ex.capitalize()
    plain, _ = stable.translate(binary, golden, work, f'{ex}-plain', ex, source_map=False)
    committed = ROOT/'Proofs'/ns/'Gen.lean'
    assert plain.read_bytes().split(b'\n', 1)[1] == committed.read_bytes(), f'{ex}: default output changed'
    base_gen, _ = stable.translate(binary, golden, work, f'{ex}-api', ex, '--proof-api', source_map=False)
    base_text = base_gen.read_text()
    base_blocks, stripped = blocks(base_text)
    base_blocks = statements(base_blocks)
    # (a) the flag only adds declarations.
    assert stripped == plain.read_text(), f'{ex}: --proof-api changed ordinary definitions'
    index = records(base_text)
    assert sorted(index) == names, (ex, sorted(index))
    assert sorted(base_blocks) == sorted(api(n) for n in names), ex
    for source, record in index.items():
        assert record['model'] == api(source) + '_model' and record['unfold'] == api(source) + '_unfold'
    # Every lemma name is a declaration of the module, and every name follows the encoding.
    report = work/f'{ex}-report.json'
    normalizer.write_report(base_gen, golden, report)
    lemmas = normalizer.load_report(report)['proof_lemmas']['functions']
    for record in lemmas:
        declared = [record['model'], record['unfold']] + [
            name for loop in record.get('loops', []) for name in loop.values()]
        for name in declared:
            assert re.search(rf'^(abbrev|theorem) {name}\b', base_text, re.MULTILINE), (ex, name)

    # (b) renumbered exporter IDs and shifted debug lines.
    rng = random.Random('lemmas-' + ex)
    stable.write_air(work/f'{ex}-renumbered', [stable.renumber(doc, rng) for doc in docs], hashed=True)
    renumbered, _ = stable.translate(binary, work/f'{ex}-renumbered', work, f'{ex}-renumbered-out', ex,
                                     '--proof-api', source_map=False)
    assert statements(blocks(renumbered.read_text())[0]) == base_blocks, f'{ex}: renumbering changed lemmas'

    # (c) an unrelated generic instance.
    extra = copy.deepcopy(docs[0]); extra['name'] = f'{ex}.unrelatedGeneric__anon_424242'
    stable.write_air(work/f'{ex}-unrelated', docs + [extra])
    unrelated, _ = stable.translate(binary, work/f'{ex}-unrelated', work, f'{ex}-unrelated-out', ex,
                                    '--proof-api', source_map=False)
    grown = statements(blocks(unrelated.read_text())[0])
    added = api(f'{ex}.unrelatedGeneric__anon_1')
    assert set(grown) == set(base_blocks) | {added}, (ex, sorted(grown))
    assert {k: v for k, v in grown.items() if k != added} == base_blocks, f'{ex}: unrelated instance changed lemmas'

    if retain:
        client = CLIENTS.get(ex, lambda _: '')(ns)
        for label, path in [('', base_gen), ('.renumbered', renumbered), ('.unrelated', unrelated)]:
            (retain/f'{ns}{label}.lean').write_text(path.read_text() + client)

    # (d) a semantic change.
    if target is None:
        return
    stable.write_air(work/f'{ex}-changed', [stable.mutate(doc) if doc['name'] == target else doc
                                            for doc in docs])
    changed, _ = stable.translate(binary, work/f'{ex}-changed', work, f'{ex}-changed-out', ex,
                                  '--proof-api', source_map=False)
    changed_blocks = statements(blocks(changed.read_text())[0])
    changed_index = records(changed.read_text())
    assert changed_index == index, f'{ex}: a semantic change renamed lemmas'
    differ = sorted(k for k in base_blocks if base_blocks[k] != changed_blocks[k])
    assert differ == [api(target)], (ex, differ)
    if retain and ex == 'basic':
        # The same name-only client against the changed `sum`: it must fail to check.
        (retain/'changed').mkdir(exist_ok=True)
        (retain/'changed'/f'{ns}.lean').write_text(changed.read_text() + CLIENTS[ex](ns))


def check_recursive_loop(binary, work, retain):
    """A loop inside a `partial_fixpoint` group: `basic.sum` calls itself on loop exit.
    Its body lemmas are proved by `eq_def`, and renumbering keeps them."""
    doc = json.loads((ROOT/'tests/golden/basic/air/basic.sum.json').read_text())
    doc['types'].append({'k': 'other', 'name': 'fn ([]const u32) callconv(.c) u64'})
    call = {'id': 100, 'tag': 'call', 'ty': 1, 'args': [{'inst': 0}],
            'callee': {'ty': len(doc['types']) - 1, 'func': 'basic.sum', 'noreturn': False}}
    exit_branch = next(i for i in stable.instructions(doc['body']) if i['tag'] == 'cond_br')
    exit_branch['else'].insert(0, call)
    stable.write_air(work/'recursive-loop', [doc])
    generated, _ = stable.translate(binary, work/'recursive-loop', work, 'recursive-loop-out', 'basic',
                                    '--proof-api', source_map=False)
    text = generated.read_text()
    base = api('basic.sum')
    assert 'partial_fixpoint' in text and f'{base}_loop0_step' in text, 'no recursive loop emitted'
    assert re.search(rf'theorem {base}_loop0_body_unfold .*\n(?:.*\n)*?  sum\.loop\d+\.eq_def p0 ', text)
    stable.write_air(work/'recursive-loop-renumbered', [stable.renumber(doc, random.Random('loop'))])
    renumbered, _ = stable.translate(binary, work/'recursive-loop-renumbered', work,
                                     'recursive-loop-renumbered-out', 'basic', '--proof-api', source_map=False)
    assert statements(blocks(renumbered.read_text())[0]) == statements(blocks(text)[0])
    if retain:
        (retain/'RecursiveLoop.lean').write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('translator', type=Path)
    parser.add_argument('--retain', type=Path, help='directory for generated modules and clients')
    args = parser.parse_args()
    binary = args.translator.resolve(strict=True)
    if args.retain:
        args.retain.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-proof-lemmas-') as temporary:
        for ex, target in EXAMPLES.items():
            check_example(binary, ex, target, Path(temporary), args.retain)
        check_recursive_loop(binary, Path(temporary), args.retain)
    print('proof-api lemma translator checks passed')


if __name__ == '__main__':
    main()
