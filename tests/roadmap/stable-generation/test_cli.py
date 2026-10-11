"""Run the built translator on committed golden AIR; never invokes Zig or Lean itself.

(a) Exporter renumbering, shifted debug lines, hashed storage names and an unrelated
    generic instance keep every fingerprint and proof-interface name.
(b) One semantic change invalidates that function, its recursion group and its
    transitive callers, and nothing else.
The source-map flag must not change generated Lean; golden bodies stay byte-identical.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/semantic-fingerprints.py'
spec = importlib.util.spec_from_file_location('fingerprints', SCRIPT)
fp = importlib.util.module_from_spec(spec); spec.loader.exec_module(fp)

# Example -> (function to mutate, expected invalidated set: itself, its cycle and callers).
SEMANTIC = dict(
    recursion=('recursion.isEven', ['recursion.isEven', 'recursion.isOdd']),
    pointers=('pointers.addTo', ['pointers.addTo', 'pointers.sumTo']),
    errors=('errors.parseDigit', ['errors.digitOrZero', 'errors.parseDigit', 'errors.sumDigits']),
    basic=('basic.tardiness', ['basic.tardiness', 'basic.totalWeightedTardiness',
                               'basic.weightedTardiness']),
    variants=(None, None),
)
SWAP = {'add_safe': 'sub_safe', 'sub_safe': 'add_safe', 'mul_safe': 'add_safe',
        'cmp_eq': 'cmp_neq', 'cmp_neq': 'cmp_eq', 'cmp_lt': 'cmp_gt', 'cmp_gt': 'cmp_lt'}


def instructions(body):
    for inst in body:
        yield inst
        for key in ('body', 'then', 'else'):
            yield from instructions(inst.get(key, []))
        for case in inst.get('cases', []):
            yield from instructions(case['body'])


def renumber(doc, rng):
    """A random injective ID map, applied to definitions, operands and branch targets."""
    doc = copy.deepcopy(doc)
    ids = [inst['id'] for inst in instructions(doc['body'])]
    fresh = rng.sample(range(10_000, 10_000 + 20 * len(ids) + 1), len(ids))
    mapping = dict(zip(ids, fresh))
    def visit(node):
        if isinstance(node, list):
            for item in node: visit(item)
        elif isinstance(node, dict):
            if isinstance(node.get('inst'), int): node['inst'] = mapping[node['inst']]
            for value in node.values(): visit(value)
    visit(doc['body'])
    for inst in instructions(doc['body']):
        inst['id'] = mapping[inst['id']]
        if 'target' in inst: inst['target'] = mapping[inst['target']]
        if inst['tag'] == 'dbg_stmt': inst['line'] += 40
    return doc


def mutate(doc):
    doc = copy.deepcopy(doc)
    inst = next(i for i in instructions(doc['body']) if i['tag'] in SWAP)
    inst['tag'] = SWAP[inst['tag']]
    return doc


def translate(binary, air, work, label, ex, *flags, source_map=True):
    out = work / f'{label}.lean'
    # The committed golden AIR is schema 11: its translation needs the explicit legacy profile.
    command = [str(binary), str(air), '-o', str(out), '--namespace', ex.capitalize(),
               '--prefix', ex + '.', '--profile', 'legacy-abi64-le', *flags]
    sidecar = work / f'{label}.source-map.json'
    if source_map: command += ['--source-map-json', str(sidecar)]
    result = subprocess.run(command, capture_output=True, timeout=300)
    assert result.returncode == 0, (label, result.stderr.decode())
    return out, sidecar


def write_air(directory, documents, hashed=False):
    directory.mkdir()
    for doc in documents:
        name = doc['name']
        stem = ('~air2lean-sha256-' + hashlib.sha256(name.encode()).hexdigest()) if hashed else name
        (directory / f'{stem}.json').write_text(json.dumps(doc, indent=1))


def cli_compare(old, new, old_gen, new_gen):
    result = subprocess.run([sys.executable, '-I', '-B', str(SCRIPT), 'compare', str(old), str(new),
                             '--old-generated', str(old_gen), '--new-generated', str(new_gen),
                             '--fail-on-change'], capture_output=True, text=True, timeout=60)
    return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr


def check_example(binary, ex, work):
    golden = ROOT / 'tests/golden' / ex / 'air'
    docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]
    names = sorted(doc['name'] for doc in docs)

    plain, _ = translate(binary, golden, work, f'{ex}-plain', ex, source_map=False)
    mapped, _ = translate(binary, golden, work, f'{ex}-mapped', ex)
    assert plain.read_bytes() == mapped.read_bytes(), f'{ex}: --source-map-json changed generated Lean'
    committed = ROOT / 'Proofs' / ex.capitalize() / 'Gen.lean'
    assert mapped.read_bytes().split(b'\n', 1)[1] == committed.read_bytes(), f'{ex}: golden body changed'

    base_gen, base_map = translate(binary, golden, work, f'{ex}-base', ex, '--proof-api')
    base = fp.load_sidecar(base_map, base_gen)
    assert sorted(r['source'] for r in base['functions']) == names
    for record in base['functions']:
        assert record['lines'] and all(isinstance(n, int) for _, n in record['lines']), record['source']

    # (a) harmless: renumbered IDs, shifted lines, hashed storage keys, unrelated instance.
    rng = random.Random(ex)
    extra = copy.deepcopy(docs[0]); extra['name'] = f'{ex}.unrelatedGeneric__anon_424242'
    write_air(work / f'{ex}-harmless', [renumber(doc, rng) for doc in docs] + [extra], hashed=True)
    harmless_gen, harmless_map = translate(binary, work / f'{ex}-harmless', work, f'{ex}-harmless-out', ex, '--proof-api')
    status, report, stderr = cli_compare(base_map, harmless_map, base_gen, harmless_gen)
    assert status == 0, (ex, stderr, report)
    assert report['unaffected'] == names and report['added'] == [f'{ex}.unrelatedGeneric__anon_1'], report
    assert not (report['invalidated'] or report['renamed'] or report['removed']), report

    # (b) semantic change: exactly the function, its cycle and its callers.
    target, expected = SEMANTIC[ex]
    if target is None:
        return
    write_air(work / f'{ex}-changed', [mutate(doc) if doc['name'] == target else doc for doc in docs])
    changed_gen, changed_map = translate(binary, work / f'{ex}-changed', work, f'{ex}-changed-out', ex, '--proof-api')
    status, report, stderr = cli_compare(base_map, changed_map, base_gen, changed_gen)
    assert status == 1, (ex, stderr)
    assert report['invalidated'] == expected, (ex, report)
    assert report['unaffected'] == sorted(set(names) - set(expected)), (ex, report)
    assert not (report['renamed'] or report['added'] or report['removed']), report


def with_callee(doc, name, callee):
    """`doc` renamed to `name`, with its calls retargeted to `callee`."""
    doc = copy.deepcopy(doc); doc['name'] = name
    for inst in instructions(doc['body']):
        if 'callee' in inst: inst['callee']['func'] = callee
    return doc


def check_generic_instance(binary, work):
    """Another instance of a generic whose existing instance a caller reaches keeps the
    existing instance's renumbered identity, definition and fingerprint (`Anon.lean`)."""
    golden = ROOT / 'tests/golden/recursion/air'
    docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]
    fact = next(doc for doc in docs if doc['name'] == 'recursion.fact')
    used = 'recursion.factInst__anon_500'
    program = docs + [with_callee(fact, used, used), with_callee(fact, 'recursion.useInst', used)]
    write_air(work / 'instance-base', program)
    base_gen, base_map = translate(binary, work / 'instance-base', work, 'instance-base-out', 'recursion', '--proof-api')
    old = fp.load_sidecar(base_map)
    assert {r['source']: r['air_name'] for r in old['functions']}['recursion.factInst__anon_1'] == used
    # The new instance's raw number sorts first, and nothing references it.
    extra = with_callee(fact, 'recursion.factInst__anon_12', 'recursion.factInst__anon_12')
    write_air(work / 'instance-grown', program + [extra], hashed=True)
    grown_gen, grown_map = translate(binary, work / 'instance-grown', work, 'instance-grown-out', 'recursion', '--proof-api')
    status, report, stderr = cli_compare(base_map, grown_map, base_gen, grown_gen)
    assert status == 0 and report['added'] == ['recursion.factInst__anon_2'], (stderr, report)
    assert report['unaffected'] == sorted(r['source'] for r in old['functions']), report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('translator', type=Path)
    args = parser.parse_args()
    binary = args.translator.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-stable-generation-') as temporary:
        work = Path(temporary)
        for ex in SEMANTIC:
            check_example(binary, ex, work)
        check_generic_instance(binary, work)
        # The translator revision describes this checkout's translator sources.
        translator = fp.load_sidecar(work / 'recursion-base.source-map.json')['translator']
        modules = dict(translator['modules'])
        assert 'Air2Lean.Main' in modules and 'Air2Lean.Emit' in modules, sorted(modules)
        for module, sha in modules.items():
            source = ROOT / (module.replace('.', '/') + '.lean')
            assert hashlib.sha256(source.read_bytes()).hexdigest() == sha, \
                f'{module}: translator built from other sources than this checkout'
        # A sidecar bound to another module's Lean output is rejected as stale.
        stale = subprocess.run([sys.executable, '-I', '-B', str(SCRIPT), 'index',
                                str(work / 'recursion-base.source-map.json'),
                                '--generated', str(work / 'pointers-base.lean')],
                               capture_output=True, text=True, timeout=60)
        assert stale.returncode == 2 and 'declarations differ' in stale.stderr, stale
    print('stable-generation translator checks passed')


if __name__ == '__main__':
    main()
