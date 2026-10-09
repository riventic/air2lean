"""Portable report/index regressions. Synthetic records never attest translator execution."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('normalizer', ROOT / 'scripts/normalize-generated.py')
n = importlib.util.module_from_spec(spec)
spec.loader.exec_module(n)


def record(source='api.add'):
    base = 'air2lean_api' + ''.join('_' + str(b) for b in source.encode())
    return dict(format='air2lean-proof-api-v1', source=source, definition='add',
                model=base+'_model', unfold=base+'_unfold',
                facts=dict(format='air2lean-scalar-ir-v1', source=source,
                           parameters=[], **{'return': 'scalar'},
                           instructions=[{'id': 0, 'operation': {'return': 42}}]),
                source_map=[{'instruction': 0, 'source_line': 12}])


def body(r, pretty=False):
    # The actual generator emits one compact JSON line, never multiline JSON.
    return ('-- air2lean-proof-api: '+json.dumps(r, sort_keys=pretty)+'\n').encode()


class Reports(unittest.TestCase):
    def test_raw_identity_locations_and_semantics_are_separate(self):
        r = record()
        metadata = {'profile': {'pointer_bits': 64}, 'float_semantics': 'ieee'}
        sources = {'api.add': {'file': 'raw.json', 'sha256': 'a'*64}}
        first = n.proof_api_records(body(r), metadata, sources)[0]
        changed_map = copy.deepcopy(r); changed_map['source_map'][0]['source_line'] = 99
        sources['api.add']['sha256'] = 'b'*64
        second = n.proof_api_records(body(changed_map, True), metadata, sources)[0]
        self.assertEqual(first['semantic_sha256'], second['semantic_sha256'])
        self.assertNotEqual(first['raw_air'], second['raw_air'])
        self.assertNotEqual(first['source_map'], second['source_map'])
        changed = copy.deepcopy(r); changed['facts']['instructions'][0]['operation']['return'] = 43
        self.assertNotEqual(first['semantic_sha256'], n.proof_api_records(body(changed), metadata, sources)[0]['semantic_sha256'])
        self.assertNotEqual(first['semantic_sha256'], n.proof_api_records(body(r), dict(metadata, float_semantics='compiler-rt'), sources)[0]['semantic_sha256'])

    def test_identity_collisions_and_malformed_records_fail_closed(self):
        r = record(); sources = {'api.add': {'file': 'raw.json', 'sha256': 'a'*64}}
        for candidate in [body(r)+body(r), body(r).replace(b'_unfold', b'_wrong'),
                          body(dict(r, extra=True)), body(dict(r, facts={})),
                          body(r).replace(b'"source": "api.add"', b'"source": "missing"')]:
            with self.assertRaises(ValueError): n.proof_api_records(candidate, {}, sources)
        with self.assertRaises(ValueError):
            n.proof_api_records(b'-- air2lean-proof-api: {"format":1,"format":2}\n', {}, sources)

    def test_lemma_names_follow_source_encoding_and_loop_order(self):
        source = 'api.sum'
        base = 'air2lean_api' + ''.join('_' + str(b) for b in source.encode())
        loop = lambda k: dict(body=f'{base}_loop{k}_body', again=f'{base}_loop{k}_again',
                              body_unfold=f'{base}_loop{k}_body_unfold', step=f'{base}_loop{k}_step')
        r = dict(format='air2lean-proof-lemmas-v1', source=source, definition='sum',
                 model=base+'_model', unfold=base+'_unfold', loops=[loop(0), loop(1)])
        line = lambda r: ('-- air2lean-proof-lemmas: '+json.dumps(r)+'\n').encode()
        sources = {source: {}}
        self.assertEqual(n.proof_lemma_records(line(r), sources), [r])
        plain = {k: v for k, v in r.items() if k != 'loops'}
        self.assertEqual(n.proof_lemma_records(line(plain), sources), [plain])
        for bad in [dict(r, loops=[loop(1), loop(0)]), dict(r, loops=[]), dict(r, extra=1),
                    dict(r, step='x'), dict(r, model='x'), dict(r, source='missing')]:
            with self.assertRaises(ValueError): n.proof_lemma_records(line(bad), sources)
        with self.assertRaises(ValueError): n.proof_lemma_records(line(r)+line(r), sources)

    def test_roundtrip_extends_the_existing_profile_report(self):
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary); air = work/'air'; air.mkdir()
            doc = json.loads((ROOT/'tests/roadmap/profiles/current.json').read_text())
            doc['name'] = 'api.add'
            (air/'raw.json').write_text(json.dumps(doc))
            metadata = dict(profile=n.profile_for_air(doc), float_semantics='ieee', correspondence='model')
            generated = work/'Gen.lean'
            generated.write_bytes(n.PREFIX+json.dumps(metadata).encode()+b'\n'+body(record()))
            output = work/'report.json'
            n.write_report(generated, air, output)
            parsed = n.load_report(output)
            self.assertEqual(parsed['proof_api']['interfaces'][0]['source'], 'api.add')
            self.assertEqual(n.checked_generated(generated, output)[0], generated.read_bytes())
            generated.write_bytes(generated.read_bytes()+b'-- edited\n')
            with self.assertRaises(ValueError): n.checked_generated(generated, output)


if __name__ == '__main__':
    unittest.main()
