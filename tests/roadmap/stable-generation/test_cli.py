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


def translate(binary, air, work, label, ex, *flags, source_map=True, profile='legacy-abi64-le'):
    out = work / f'{label}.lean'
    # The shared golden AIR is schema 11: its translation needs the explicit legacy profile.
    # The example's own admissions (examples/<ex>/translate.args, as scripts/check.sh) apply too.
    args = ROOT / 'examples' / ex / 'translate.args'
    admissions = args.read_text().split() if args.is_file() else []
    command = [str(binary), str(air), '-o', str(out), '--namespace', ex.capitalize(),
               '--prefix', ex + '.', '--profile', profile, *admissions, *flags]
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


def version_golden(ex, version, work):
    """The example's golden set for `version` (the shared files replaced by
    tests/golden/<version>/<ex>/air, as scripts/check.sh merges them) as (directory, documents), or
    None unless every function in it is an export of `version`. A shared file that a differently
    numbered instance should replace stays, so the set is not one version's and is skipped."""
    merged = {}
    for directory in (ROOT / 'tests/golden' / ex / 'air', ROOT / 'tests/golden' / version / ex / 'air'):
        merged.update({p.name: p for p in directory.glob('*.json')})
    docs = [json.loads(merged[name].read_text()) for name in sorted(merged)]
    if not docs or any(doc.get('zig_version') != version for doc in docs):
        return None
    write_air(work / f'{ex}-{version}-golden', docs)
    return work / f'{ex}-{version}-golden', docs


def check_example(binary, ex, work, version=None):
    """(a) and (b) on the shared golden AIR, or with `version` (Zig 0.17.1) on that version's golden
    set: schema 12, its own profile, and the compiler's `__func_<n>` instance names, which the
    translator renames to the same stable `__anon_<k>` (Air2Lean/Air/Anon.lean). Returns whether
    the example was checked."""
    if version is None:
        golden, profile, label, marker = ROOT / 'tests/golden' / ex / 'air', 'legacy-abi64-le', ex, '__anon_'
        docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]
    else:
        found = version_golden(ex, version, work)
        if found is None:
            return False
        (golden, docs), profile, label, marker = found, 'abi64-le-v1', f'{ex}-{version}', '__func_'
    names = sorted(doc['name'] for doc in docs)

    plain, _ = translate(binary, golden, work, f'{label}-plain', ex, source_map=False, profile=profile)
    mapped, _ = translate(binary, golden, work, f'{label}-mapped', ex, profile=profile)
    assert plain.read_bytes() == mapped.read_bytes(), f'{label}: --source-map-json changed generated Lean'
    if version is None:
        committed = ROOT / 'Proofs' / ex.capitalize() / 'Gen.lean'
        assert mapped.read_bytes().split(b'\n', 1)[1] == committed.read_bytes(), f'{ex}: golden body changed'

    base_gen, base_map = translate(binary, golden, work, f'{label}-base', ex, '--proof-api', profile=profile)
    base = fp.load_sidecar(base_map, base_gen)
    assert sorted(r['source'] for r in base['functions']) == names
    for record in base['functions']:
        assert record['lines'] and all(isinstance(n, int) for _, n in record['lines']), record['source']

    # (a) harmless: renumbered IDs, shifted lines, hashed storage keys, unrelated instance.
    rng = random.Random(ex)
    extra = copy.deepcopy(docs[0]); extra['name'] = f'{ex}.unrelatedGeneric{marker}424242'
    write_air(work / f'{label}-harmless', [renumber(doc, rng) for doc in docs] + [extra], hashed=True)
    harmless_gen, harmless_map = translate(binary, work / f'{label}-harmless', work, f'{label}-harmless-out', ex,
                                           '--proof-api', profile=profile)
    status, report, stderr = cli_compare(base_map, harmless_map, base_gen, harmless_gen)
    assert status == 0, (ex, stderr, report)
    assert report['unaffected'] == names and report['added'] == [f'{ex}.unrelatedGeneric__anon_1'], report
    assert not (report['invalidated'] or report['renamed'] or report['removed']), report

    # (b) semantic change: exactly the function, its cycle and its callers.
    target, expected = SEMANTIC[ex]
    if target is None:
        return True
    write_air(work / f'{label}-changed', [mutate(doc) if doc['name'] == target else doc for doc in docs])
    changed_gen, changed_map = translate(binary, work / f'{label}-changed', work, f'{label}-changed-out', ex,
                                         '--proof-api', profile=profile)
    status, report, stderr = cli_compare(base_map, changed_map, base_gen, changed_gen)
    assert status == 1, (label, stderr)
    assert report['invalidated'] == expected, (label, report)
    assert report['unaffected'] == sorted(set(names) - set(expected)), (label, report)
    assert not (report['renamed'] or report['added'] or report['removed']), report
    return True


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


def import_closure(root):
    """Modules of `ZigLean` reachable from `import ZigLean`, by reading the checkout's import lines."""
    seen, todo = set(), [root]
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        for line in (ROOT / (name.replace('.', '/') + '.lean')).read_text().splitlines():
            parts = line.split()
            if len(parts) == 2 and parts[0] == 'import' and parts[1].split('.')[0] == 'ZigLean':
                todo.append(parts[1])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('translator', type=Path)
    args = parser.parse_args()
    binary = args.translator.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-stable-generation-') as temporary:
        work = Path(temporary)
        for ex in SEMANTIC:
            check_example(binary, ex, work)
        # Zig 0.17.1 first: the same checks on every example whose 0.17.1 golden set is complete.
        # The list is exact: an example whose goldens become (or stop being) complete must be
        # added (or removed) here, never pass or drop out silently.
        checked = [ex for ex in SEMANTIC if check_example(binary, ex, work, '0.17.1')]
        assert checked == ['basic'], checked
        check_generic_instance(binary, work)
        # The translator revision describes this checkout's translator sources.
        translator = fp.load_sidecar(work / 'recursion-base.source-map.json')['translator']
        modules = dict(translator['modules'])
        assert 'Air2Lean.Main' in modules and 'Air2Lean.Emit' in modules, sorted(modules)
        for module, sha in modules.items():
            source = ROOT / (module.replace('.', '/') + '.lean')
            assert hashlib.sha256(source.read_bytes()).hexdigest() == sha, \
                f'{module}: translator built from other sources than this checkout'
        # The runtime revision is the import closure of `import ZigLean`, hashed from this checkout.
        runtime = fp.load_sidecar(work / 'recursion-base.source-map.json')['runtime']
        rt_modules = dict(runtime['modules'])
        assert 'ZigLean.Basic' in rt_modules and 'ZigLean' in rt_modules, sorted(rt_modules)[:5]
        for module, sha in rt_modules.items():
            source = ROOT / (module.replace('.', '/') + '.lean')
            assert hashlib.sha256(source.read_bytes()).hexdigest() == sha, \
                f'{module}: runtime built from other sources than this checkout'
        assert sorted(rt_modules) == sorted(import_closure('ZigLean')), 'runtime modules differ from the import closure'
        # A sidecar bound to another module's Lean output is rejected as stale.
        stale = subprocess.run([sys.executable, '-I', '-B', str(SCRIPT), 'index',
                                str(work / 'recursion-base.source-map.json'),
                                '--generated', str(work / 'pointers-base.lean')],
                               capture_output=True, text=True, timeout=60)
        assert stale.returncode == 2 and 'declarations differ' in stale.stderr, stale
    print('stable-generation translator checks passed')


if __name__ == '__main__':
    main()
