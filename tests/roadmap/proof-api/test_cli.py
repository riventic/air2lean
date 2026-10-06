"""ROOT-only driver for the built translator; never invokes Zig or Lean itself."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('report', ROOT/'scripts/normalize-generated.py')
n = importlib.util.module_from_spec(spec); spec.loader.exec_module(n)


def fixture():
    doc = json.loads((ROOT/'tests/roadmap/profiles/current.json').read_text())
    doc.update(name='api.add', params=[0, 0], ret=0,
               types=[dict(k='int', signed=False, bits=32, abi_size=4, abi_align=4), dict(k='noreturn')],
               body=[dict(id=21, tag='arg', ty=0, param=0), dict(id=9, tag='arg', ty=0, param=1),
                     dict(id=84, tag='add_safe', ty=0, args=[dict(inst=21), dict(inst=9)]),
                     dict(id=333, tag='ret', ty=1, args=[dict(inst=84)])])
    return doc


def invoke(binary, documents, work, label):
    air = work/label; air.mkdir()
    for i, doc in enumerate(documents): (air/f'{i}.json').write_text(json.dumps(doc))
    generated = work/f'{label}.lean'
    result = subprocess.run([str(binary), str(air), '-o', str(generated), '--namespace', 'Stable',
                             '--prefix', 'api.', '--proof-api'], capture_output=True, timeout=15)
    assert result.returncode == 0, result.stderr.decode()
    report = work/f'{label}.json'
    n.write_report(generated, air, report)
    return generated, n.load_report(report)


def check(binary, retain):
    with tempfile.TemporaryDirectory(prefix='air2lean-proof-api-') as temporary:
        work = Path(temporary); doc = fixture()
        original, first = invoke(binary, [doc], work, 'first')
        renamed = copy.deepcopy(doc)
        renumber = {21: 120, 9: 400, 84: 17, 333: 2}
        for instruction in renamed['body']:
            instruction['id'] = renumber[instruction['id']]
            for value in instruction.get('args', []): value['inst'] = renumber[value['inst']]
        renumbered_output, second = invoke(binary, [renamed], work, 'renumbered')
        unrelated = copy.deepcopy(doc); unrelated['name'] = 'api.unrelated__anon_999'
        unrelated_output, third = invoke(binary, [unrelated, doc], work, 'unrelated')
        def entry(report):
            records = report['proof_api']['interfaces']
            assert len(records) == 1 and records[0]['source'] == 'api.add', records
            return records[0]
        for report in [second, third]:
            for key in ['model', 'unfold', 'semantic_sha256']:
                assert entry(first)[key] == entry(report)[key], key
        changed = copy.deepcopy(doc); changed['body'][2]['tag'] = 'sub_safe'
        changed_output, fourth = invoke(binary, [changed], work, 'semantic-change')
        assert entry(first)['semantic_sha256'] != entry(fourth)['semantic_sha256']
        # Persist ROOT's actual output so its generated `rfl` interface and a downstream
        # arithmetic contract can be kernel checked with the ordinary Lean compiler.
        retain.write_bytes(original.read_bytes())
        base = entry(first)['model']; unfold = entry(first)['unfold']
        client = ('\nexample : Stable.'+base+' 2 3 = pure (5 : BitVec 32) := by\n'+
                  '  rw [Stable.'+unfold+']\n  rfl\n')
        for label, output in [('client', original), ('renumbered.client', renumbered_output),
                              ('unrelated.client', unrelated_output), ('changed.client', changed_output)]:
            retain.with_suffix('.'+label+'.lean').write_text(output.read_text()+client)



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('translator', type=Path)
    parser.add_argument('--retain', type=Path, required=True)
    args = parser.parse_args()
    check(args.translator.resolve(strict=True), args.retain)
