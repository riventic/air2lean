"""Offline checks of the fingerprint call-graph fold and interface classification."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/semantic-fingerprints.py'
spec = importlib.util.spec_from_file_location('fingerprints', SCRIPT)
fp = importlib.util.module_from_spec(spec); spec.loader.exec_module(fp)

# a -> b -> c; d alone; e <-> f (mutual recursion); g -> e; h -> external boundary.
GRAPH = dict(a=['b'], b=['c'], c=[], d=[], e=['f'], f=['e'], g=['e'], h=['ext.model'])


def sidecar():
    functions = [dict(source=name, air_name=name, air_file=name + '.json', definition=name,
                      proof_api=None, callees=callees, lines=[[0, 1]],
                      canonical=dict(body=[dict(id=0, tag='ret', args=[dict(val=name)])]))
                 for name, callees in GRAPH.items()]
    return dict(format=fp.SIDECAR, namespace='Demo', metadata=dict(profile='p'),
                options=dict(spawn_policy='available', models=None), functions=functions)


def change(doc, name):
    doc = copy.deepcopy(doc)
    record = next(r for r in doc['functions'] if r['source'] == name)
    record['canonical']['body'][0]['tag'] = 'unreach'
    return doc


def main():
    base = sidecar()
    entries = fp.fingerprints(base)
    assert entries['e']['recursive_group'] == ['e', 'f'] == entries['f']['recursive_group']
    assert entries['a']['recursive_group'] == [] and entries['h']['boundaries'] == ['ext.model']
    assert len({e['fingerprint'] for e in entries.values()}) == len(GRAPH)

    # Source maps are provenance: line and storage changes alone keep every interface.
    moved = copy.deepcopy(base)
    for record in moved['functions']:
        record['lines'] = [[0, 99]]; record['air_file'] = '~air2lean-sha256-x.json'
    assert fp.compare(base, moved)['unaffected'] == sorted(GRAPH)

    expectations = dict(c=['a', 'b', 'c'], d=['d'], f=['e', 'f', 'g'], a=['a'], h=['h'])
    for name, invalid in expectations.items():
        report = fp.compare(base, change(base, name))
        assert report['invalidated'] == invalid, (name, report)
        assert report['unaffected'] == sorted(set(GRAPH) - set(invalid)), (name, report)

    renamed = copy.deepcopy(base); renamed['functions'][3]['definition'] = 'd_1'
    report = fp.compare(base, renamed)
    assert report['renamed'] == ['d'] and report['invalidated'] == [], report

    grown = copy.deepcopy(base)
    grown['functions'].append(dict(copy.deepcopy(base['functions'][0]), source='new__anon_1'))
    report = fp.compare(base, grown)
    assert report['added'] == ['new__anon_1'] and report['unaffected'] == sorted(GRAPH), report

    # Profile/options participate: a different target or float mode invalidates everything.
    other = copy.deepcopy(base); other['metadata']['profile'] = 'q'
    assert fp.compare(base, other)['invalidated'] == sorted(GRAPH)

    for bad in [dict(base, format='x'), dict(base, functions=base['functions'] * 2),
                dict(base, functions=[dict(base['functions'][0], extra=1)])]:
        try:
            with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as handle:
                json.dump(bad, handle)
            fp.load_sidecar(handle.name)
        except ValueError:
            pass
        else:
            raise AssertionError('malformed sidecar accepted')
        finally:
            Path(handle.name).unlink()

    with tempfile.TemporaryDirectory(prefix='air2lean-fingerprints-') as temporary:
        work = Path(temporary)
        (work / 'old.json').write_text(json.dumps(base))
        (work / 'same.json').write_text(json.dumps(moved))
        (work / 'new.json').write_text(json.dumps(change(base, 'c')))
        run = lambda *args: subprocess.run([sys.executable, '-I', '-B', str(SCRIPT), *args],
                                           capture_output=True, text=True, timeout=60)
        same = run('compare', str(work / 'old.json'), str(work / 'same.json'), '--fail-on-change')
        assert same.returncode == 0, same.stderr
        changed = run('compare', str(work / 'old.json'), str(work / 'new.json'), '--fail-on-change')
        assert changed.returncode == 1 and json.loads(changed.stdout)['invalidated'] == ['a', 'b', 'c']
        malformed = run('index', str(work / 'missing.json'))
        assert malformed.returncode == 2 and 'error:' in malformed.stderr
    print('stable-generation fingerprint checks passed')


if __name__ == '__main__':
    main()
