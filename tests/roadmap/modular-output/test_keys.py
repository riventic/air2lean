"""Pure checks of scripts/module-split.py on synthetic manifests (no translator, Lean or Zig).

Keys propagate along imports (a changed callee invalidates exactly its transitive importers),
profile metadata, the translator revision and semantic fingerprints enter every key, and
malformed manifests, import cycles, escaping paths, inconsistent translator revisions and
mismatched source maps are rejected.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/module-split.py'
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('module_split', SCRIPT)
ms = importlib.util.module_from_spec(spec); spec.loader.exec_module(ms)

METADATA = {'profile': {'name': 'test'}, 'float_semantics': 'ieee', 'correspondence': 'model'}


def translator(emit='e' * 64):
    t = dict(lean='4.34.0', modules=[['Air2Lean.Emit', emit], ['Air2Lean.Main', 'a' * 64]], revision='')
    t['revision'] = ms.fp.translator_revision(t)
    return t


TRANSLATOR = translator()
# a <- b <- c, a <- d; e independent.
GROUPS = dict(a=[], b=['a'], c=['b'], d=['a'], e=[])


def module(name, kind='group', imports=(), functions=()):
    return dict(module=f'R.{name}' if name else 'R', file=f'R/{name}.lean' if name else 'R.lean', kind=kind,
                functions=list(functions), definitions=list(functions), imports=list(imports))


def write(directory, texts=None, metadata=METADATA, extra=(), revision=TRANSLATOR):
    texts = texts or {}
    mods = [module('Types', 'types', ['ZigLean'])]
    for g, callees in GROUPS.items():
        mods.append(module(f'F_{g}', imports=['R.Types'] + [f'R.F_{c}' for c in callees], functions=[f'ex.{g}']))
    mods.append(module('', 'umbrella', [m['module'] for m in mods]))
    mods += list(extra)
    (directory / 'R').mkdir(parents=True, exist_ok=True)
    for m in mods:
        (directory / m['file']).write_text(texts.get(m['module'], f'-- {m["module"]}\n'))
    doc = dict(format=ms.FORMAT, namespace='Ex', root='R', metadata=metadata, translator=revision,
               modules=mods)
    path = directory / 'Gen.modules.json'
    path.write_text(json.dumps(doc))
    return path


def sidecar(directory, changed=()):
    functions = [dict(source=f'ex.{g}', air_name=f'ex.{g}', air_file=f'ex.{g}.json', definition=f'ex.{g}',
                      proof_api=None, callees=[f'ex.{c}' for c in callees],
                      canonical={'body': ['changed' if g in changed else 'same']}, lines=[])
                 for g, callees in GROUPS.items()]
    path = directory / 'map.json'
    path.write_text(json.dumps(dict(format=ms.fp.SIDECAR, namespace='Ex', metadata=METADATA,
                                    options={}, translator=TRANSLATOR, functions=functions)))
    return ms.fp.load_sidecar(path)


def expect_error(fn, text):
    try:
        fn()
    except ValueError as error:
        assert text in str(error), (text, error)
    else:
        raise AssertionError(f'accepted: {text}')


def main():
    with tempfile.TemporaryDirectory(prefix='air2lean-module-keys-') as temporary:
        work = Path(temporary)
        old = ms.keys(ms.load_manifest(write(work / 'old')))
        again = ms.keys(ms.load_manifest(write(work / 'again')))
        assert old == again, 'keys are not deterministic'

        # Text change of `a`: a and its transitive importers b, c, d and the umbrella.
        new = ms.keys(ms.load_manifest(write(work / 'new', {'R.F_a': '-- edited\n'})))
        report = ms.compare(old, new)
        assert report['changed'] == ['R.F_a'], report
        assert report['invalidated'] == ['R', 'R.F_a', 'R.F_b', 'R.F_c', 'R.F_d'], report
        assert report['invalidated'] == sorted(ms.dependents(old, report['changed']))
        assert report['unaffected'] == ['R.F_e', 'R.Types'], report

        # A leaf caller change invalidates only itself and the umbrella.
        leaf = ms.compare(old, ms.keys(ms.load_manifest(write(work / 'leaf', {'R.F_c': '-- edited\n'}))))
        assert leaf['invalidated'] == ['R', 'R.F_c'], leaf

        # The types module is imported by every group: everything rebuilds.
        types = ms.compare(old, ms.keys(ms.load_manifest(write(work / 'types', {'R.Types': '-- edited\n'}))))
        assert types['unaffected'] == [] and types['changed'] == ['R.Types'], types

        # A profile change invalidates every module even with identical text.
        other = dict(METADATA, float_semantics='compiler-rt')
        profile = ms.compare(old, ms.keys(ms.load_manifest(write(work / 'profile', metadata=other))))
        assert profile['changed'] == [] and profile['unaffected'] == [], profile

        # A translator (emitter) change invalidates every module even with identical text and
        # without a source map.
        emitter = ms.compare(old, ms.keys(ms.load_manifest(write(work / 'emitter', revision=translator('f' * 64)))))
        assert emitter['changed'] == [] and emitter['unaffected'] == [], emitter

        # A semantic fingerprint change with identical text still invalidates (source map bound).
        manifest = ms.load_manifest(write(work / 'sem'))
        base = ms.keys(manifest, sidecar(work))
        sem = ms.compare(base, ms.keys(manifest, sidecar(work, changed={'b'})))
        assert sem['changed'] == [] and sem['invalidated'] == ['R', 'R.F_b', 'R.F_c'], sem

        # Rejections.
        doc = json.loads((work / 'old/Gen.modules.json').read_text())
        def bad(mutator, text, name):
            d = copy.deepcopy(doc); mutator(d)
            path = work / 'old' / f'{name}.json'
            path.write_text(json.dumps(d))
            expect_error(lambda: ms.keys(ms.load_manifest(path)), text)
        bad(lambda d: d.update(format='other'), 'not an', 'format')
        bad(lambda d: d['modules'][1].update(kind='weird'), 'malformed module record', 'kind')
        bad(lambda d: d['modules'].append(copy.deepcopy(d['modules'][1])), 'duplicate module', 'dup')
        bad(lambda d: d['modules'][1].update(file='../../escape.lean'), 'escapes', 'escape')
        bad(lambda d: d['modules'][1]['imports'].append('R.F_c'), 'import cycle', 'cycle')
        bad(lambda d: d.pop('translator'), 'not an', 'no-translator')
        bad(lambda d: d['translator']['modules'][0].__setitem__(1, 'f' * 64), 'translator revision', 'forged')
        mismatch = sidecar(work); mismatch['functions'].pop()
        expect_error(lambda: ms.keys(manifest, mismatch), 'different functions')
        renamed = sidecar(work); renamed['functions'][0]['definition'] = 'other'
        expect_error(lambda: ms.keys(manifest, renamed), 'declarations differ')
        moved = sidecar(work); moved['metadata'] = other
        expect_error(lambda: ms.keys(manifest, moved), 'different translations')
        rebuilt = ms.load_manifest(write(work / 'rebuilt', revision=translator('f' * 64)))
        expect_error(lambda: ms.keys(rebuilt, sidecar(work)), 'different translations')

        # CLI: malformed input exits 2.
        result = subprocess.run([sys.executable, '-I', '-B', str(SCRIPT), 'keys', str(work / 'old/cycle.json')],
                                capture_output=True, text=True, timeout=60)
        assert result.returncode == 2 and 'import cycle' in result.stderr, result
    print('modular-output key checks passed')


if __name__ == '__main__':
    main()
