"""Run the built translator on committed golden AIR; never invokes Zig or Lean itself.

(a) Without `--split-modules` the output is unchanged: byte-identical to the committed
    Proofs/<Ex>/Gen.lean body. With it, the umbrella imports every part and the parts hold
    the same text.
(b) Splitting is deterministic: exporter renumbering, shifted lines and hashed storage names
    give byte-identical modules and manifest.
(c) One semantic edit changes the text of exactly the edited function's module; the
    invalidated modules (`scripts/module-split.py compare`) are exactly that module and its
    transitive importers, and equal the modules holding the functions whose semantic
    fingerprints changed, plus the umbrella.
(d) Rejected flag combinations, and stale generated parts are removed on regeneration.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SPLIT = ROOT / 'scripts/module-split.py'
sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


stable = load('stable_cli', ROOT / 'tests/roadmap/stable-generation/test_cli.py')
split = load('module_split', SPLIT)
fp = split.fp

# Example -> function to mutate (`stable.mutate`).
EXAMPLES = dict(recursion='recursion.isEven', pointers='pointers.addTo', errors='errors.parseDigit',
                basic='basic.tardiness', layout='layout.digit', threads='threads.bump')


def translate(binary, air, work, label, ex, *flags, split_modules=True):
    # One module root for every translation, in separate directories, so they compare directly.
    root = 'Base.Gen'
    out = work / label / 'Base/Gen.lean'
    out.parent.mkdir(parents=True, exist_ok=True)
    command = [str(binary), str(air), '-o', str(out), '--namespace', ex.capitalize(), '--prefix', ex + '.',
               '--source-map-json', str(work / f'{label}.source-map.json'), *flags]
    if split_modules:
        command += ['--split-modules', root]
    result = subprocess.run(command, capture_output=True, timeout=300)
    assert result.returncode == 0, (label, result.stderr.decode())
    return out, root


def files(out):
    """Every generated file (relative to the umbrella's directory) -> bytes."""
    base = out.parent
    paths = [out, out.with_name('Gen.modules.json')] + sorted((base / 'Gen').glob('*.lean'))
    return {str(p.relative_to(base)): p.read_bytes() for p in paths}


def modules_of(out):
    return split.keys(split.load_manifest(out.with_name('Gen.modules.json')))


def compare(old, new, old_map, new_map):
    result = subprocess.run([sys.executable, '-I', '-B', str(SPLIT), 'compare',
                             str(old.with_name('Gen.modules.json')), str(new.with_name('Gen.modules.json')),
                             '--old-source-map', str(old_map), '--new-source-map', str(new_map)],
                            capture_output=True, text=True, timeout=60)
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


def check_example(binary, ex, target, work):
    golden = ROOT / 'tests/golden' / ex / 'air'
    docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]

    # (a) the default single file is unchanged; the split holds the same declarations.
    single, _ = translate(binary, golden, work, f'{ex}-single', ex, split_modules=False)
    committed = (ROOT / 'Proofs' / ex.capitalize() / 'Gen.lean').read_bytes()
    if committed.startswith(b'-- air2lean-profile: '):  # committed with the reference host's header
        committed = committed.split(b'\n', 1)[1]
    assert single.read_bytes().split(b'\n', 1)[1] == committed, f'{ex}: default output changed'
    assert not (single.parent / 'Gen').exists() and not single.with_name('Gen.modules.json').exists()
    base, root = translate(binary, golden, work, f'{ex}-base', ex)
    manifest = json.loads(base.with_name('Gen.modules.json').read_text())
    umbrella = base.read_text()
    assert umbrella.split('\n', 1)[0] == single.read_text().split('\n', 1)[0], f'{ex}: profile header differs'
    parts = [m for m in manifest['modules'] if m['kind'] != 'umbrella']
    assert umbrella.split('\n', 1)[1] == ''.join(f'import {m["module"]}\n' for m in parts)
    sources = sorted(s for m in parts for s in m['functions'])
    assert sources == sorted(r['source'] for r in fp.load_sidecar(work / f'{ex}-base.source-map.json')['functions'])
    # Every declaration of the single file appears in exactly one part, in the same order.
    decls = lambda text: [line for line in text.splitlines() if line.startswith(('def ', 'structure ', 'inductive ', 'theorem '))]
    in_parts = [d for m in parts for d in decls((base.parent / m['file']).read_text())]
    assert in_parts == decls(single.read_text()), f'{ex}: declarations differ between split and single file'

    # (b) harmless input changes give byte-identical output.
    rng = random.Random(ex)
    stable.write_air(work / f'{ex}-harmless-air', [stable.renumber(doc, rng) for doc in docs], hashed=True)
    harmless, _ = translate(binary, work / f'{ex}-harmless-air', work, f'{ex}-base2', ex)
    assert files(harmless) == files(base), \
        f'{ex}: split output is not deterministic'

    # (c) one semantic edit: changed text and invalidation closure.
    stable.write_air(work / f'{ex}-changed-air', [stable.mutate(doc) if doc['name'] == target else doc for doc in docs])
    changed, _ = translate(binary, work / f'{ex}-changed-air', work, f'{ex}-changed', ex)
    report = compare(base, changed, work / f'{ex}-base.source-map.json', work / f'{ex}-changed.source-map.json')
    entries = modules_of(base)
    owner = {s: name for name, e in entries.items() for s in e['functions']}
    assert report['changed'] == [owner[target]], (ex, report)
    closure = split.dependents(entries, report['changed'])
    assert report['invalidated'] == sorted(closure), (ex, report)
    assert report['unaffected'] == sorted(set(entries) - closure), (ex, report)
    assert not (report['added'] or report['removed']), report
    semantic = fp.compare(fp.load_sidecar(work / f'{ex}-base.source-map.json'),
                          fp.load_sidecar(work / f'{ex}-changed.source-map.json'))
    expected = {owner[s] for s in semantic['invalidated']} | {root}
    if any(entries[m]['kind'] == 'dispatch' and m in closure for m in entries):
        expected |= {m for m in entries if entries[m]['kind'] == 'dispatch'}
    assert set(report['invalidated']) == expected, (ex, report, semantic)


def check_rejections_and_stale(binary, work):
    golden = ROOT / 'tests/golden/recursion/air'
    out = work / 'reject/Proofs/Ex/Gen.lean'; out.parent.mkdir(parents=True)
    base = [str(binary), str(golden), '-o', str(out), '--namespace', 'Recursion', '--prefix', 'recursion.']
    for flags, message in [(['--split-modules', 'Proofs.Other.Gen'], 'needs -o ending in Proofs/Other/Gen.lean'),
                           (['--split-modules', 'Proofs..Gen'], 'invalid --split-modules'),
                           (['--split-modules', 'en'], 'needs -o ending in en.lean'),
                           (['--split-modules', 'Proofs.Ex.Gen', '--timing-json', str(out.with_suffix('.modules.json'))],
                            'must not name the module manifest'),
                           (['--split-modules', 'Proofs.Ex.Gen', '--split-modules', 'Proofs.Ex.Gen'], 'duplicate --split-modules'),
                           (['--split-modules'], 'missing value for --split-modules'),
                           (['--split-modules', 'Proofs.Ex.Gen', '--model-registry-template'], 'cannot be combined')]:
        result = subprocess.run(base + flags, capture_output=True, text=True, timeout=60)
        assert result.returncode == 1 and message in result.stderr, (flags, result.stderr)
    assert not out.exists() and not out.with_name('Gen').exists()

    # A removed function's module disappears on regeneration; files without the marker stay.
    docs = [json.loads(p.read_text()) for p in sorted(golden.glob('*.json'))]
    subprocess.run(base + ['--split-modules', 'Proofs.Ex.Gen'], check=True, capture_output=True, timeout=60)
    before = set(p.name for p in (out.parent / 'Gen').iterdir())
    (out.parent / 'Gen/Handwritten.lean').write_text('-- not generated\n')
    keep = [doc for doc in docs if doc['name'] != 'recursion.fact']
    assert len(keep) == len(docs) - 1
    stable.write_air(work / 'reject-air', keep)
    subprocess.run([str(binary), str(work / 'reject-air')] + base[2:] + ['--split-modules', 'Proofs.Ex.Gen'],
                   check=True, capture_output=True, timeout=60)
    after = set(p.name for p in (out.parent / 'Gen').iterdir())
    assert before - after == {'F_fact.lean'} and after - before == {'Handwritten.lean'}, (before, after)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('translator', type=Path)
    args = parser.parse_args()
    binary = args.translator.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='air2lean-modular-output-') as temporary:
        work = Path(temporary)
        for ex, target in EXAMPLES.items():
            check_example(binary, ex, target, work)
        check_rejections_and_stale(binary, work)
    print('modular-output translator checks passed')


if __name__ == '__main__':
    main()
