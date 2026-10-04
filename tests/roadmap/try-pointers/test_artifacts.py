import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('guard', Path(__file__).with_name('check-artifacts.py'))
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.case = self.repo / 'case'
        (self.case / 'air/0.16.0').mkdir(parents=True)
        (self.case / 'TryPointers').mkdir()
        (self.repo / 'source.zig').write_text('fixture source')
        (self.repo / 'exporter.zig').write_text('fixture exporter')
        (self.case / 'TryPointers/Gen.lean').write_text('fixture generated output')
        for name, tag in [('hot', 'try_ptr'), ('cold', 'try_ptr_cold')]:
            (self.case / ('air/0.16.0/' + name + '.json')).write_text(json.dumps({
                'schema': 11, 'zig_version': '0.16.0', 'target_endian': 'little',
                'name': 'try_pointers.' + name, 'body': [{'tag': tag}]}))
        self.manifest = {'source': 'source.zig', 'source_sha256': guard.digest(self.repo/'source.zig'),
                         'exporter': 'exporter.zig', 'exporter_sha256': guard.digest(self.repo/'exporter.zig'),
                         'functions': ['hot', 'cold'], 'artifacts': {}}
        self.save()
        guard.inspect(self.repo, self.case, record=True)
        self.manifest = json.loads((self.case/'provenance.json').read_text())

    def save(self):
        (self.case/'provenance.json').write_text(json.dumps(self.manifest))

    def test_complete_inventory_and_stale_source(self):
        self.assertEqual(len(guard.inspect(self.repo, self.case)), 3)
        (self.repo/'source.zig').write_text('modified')
        with self.assertRaisesRegex(ValueError, 'stale source'): guard.inspect(self.repo, self.case)

    def test_expected_hash_format_and_exporter(self):
        self.manifest['source_sha256'] = 'not a SHA-256'
        self.save()
        with self.assertRaisesRegex(ValueError, 'invalid source'): guard.inspect(self.repo, self.case)
        self.manifest['source_sha256'] = guard.digest(self.repo/'source.zig')
        self.save()
        (self.repo/'exporter.zig').write_text('modified')
        with self.assertRaisesRegex(ValueError, 'stale exporter'): guard.inspect(self.repo, self.case)

    def test_missing_and_duplicate_function_inventory(self):
        hot = self.case/'air/0.16.0/hot.json'
        hot.unlink()
        with self.assertRaisesRegex(ValueError, 'function inventory'): guard.inspect(self.repo, self.case)
        hot.write_text((self.case/'air/0.16.0/cold.json').read_text())
        with self.assertRaisesRegex(ValueError, 'function inventory'): guard.inspect(self.repo, self.case)

    def test_unsupported_and_wrong_profile(self):
        hot = self.case/'air/0.16.0/hot.json'
        data = json.loads(hot.read_text())
        data['body'][0]['unsupported'] = True
        hot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'unsupported'): guard.inspect(self.repo, self.case)
        data['body'][0].pop('unsupported')
        data['zig_version'] = '0.15.2'
        hot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'profile differs'): guard.inspect(self.repo, self.case)

    def test_required_cold_and_hot_tags(self):
        cold = self.case/'air/0.16.0/cold.json'
        data = json.loads(cold.read_text())
        data['body'][0]['tag'] = 'try_ptr'
        cold.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'both pointer-try tags'): guard.inspect(self.repo, self.case)

    def test_generated_hash_and_exact_recorded_inventory(self):
        (self.case/'TryPointers/Gen.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'artifact inventory'): guard.inspect(self.repo, self.case)
        guard.inspect(self.repo, self.case, record=True)
        self.manifest = json.loads((self.case/'provenance.json').read_text())
        self.manifest['artifacts']['not-an-artifact'] = '0'*64
        self.save()
        with self.assertRaisesRegex(ValueError, 'artifact inventory'): guard.inspect(self.repo, self.case)

if __name__ == '__main__': unittest.main()
