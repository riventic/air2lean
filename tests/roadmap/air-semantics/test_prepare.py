"""Confined controls for certificate preparation; no Lean compiler is invoked."""
import contextlib
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location('certificate_query', ROOT / 'scripts/certificate-query.py')
QUERY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(QUERY)


class Preparation(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='certificate-query-control-')
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.library = self.root / 'base'
        (self.library / 'tools').mkdir(parents=True)
        (self.library / 'tools/Assurance.olean').write_bytes(b'checked reader')
        (self.library / 'ZigLean.olean').write_bytes(b'checked runtime')
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'scripts/theorem_universe.py'):
            path = self.root / name
            path.parent.mkdir(exist_ok=True)
            path.write_text('control input')
        self.request = {'module': 'Fresh.Gen', 'modules': [
            {'name': 'Fresh.Gen', 'source': 'import ZigLean\ndef f := 1\n', 'imports': ['ZigLean']}],
            'translator': self.revision('Air2Lean.Control'), 'runtime': self.revision('ZigLean.Control')}
        self.sources, self.outputs, self.calls = [], [], []
        self.mutation = None
        self.payload = {'fixpoint_groups': []}
        for target in (patch.object(QUERY, 'ROOT', self.root),
                       patch.object(QUERY.assumptions, 'run', self.run_command),
                       patch.object(sys.modules['theorem_universe'], 'run', self.compile_command),
                       patch.object(QUERY.assumptions, 'prepared_tool', self.prepared_tool),
                       patch.object(QUERY.assumptions, 'verify_extractor_inputs')):
            target.start()
            self.addCleanup(target.stop)

    def revision(self, name):
        path = self.root / (name.replace('.', '/') + '.lean')
        path.parent.mkdir(exist_ok=True)
        path.write_text('def original := 1\n')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        return {'lean': 'control', 'modules': [[name, digest]],
                'revision': hashlib.sha256(f'control\n{name} {digest}\n'.encode()).hexdigest()}

    @contextlib.contextmanager
    def prepared_tool(self, *args):
        yield {'toolchain_runtime_sha256': 'control-runtime'}

    def run_command(self, command, **kwargs):
        self.calls.append(command)
        if command[:3] == ['lake', '--rehash', 'build']:
            return ''
        if command == ['lake', 'env', 'printenv', 'LEAN_PATH']:
            return str(self.library) + '\n'
        if '-o' in command:
            source = Path(command[-1])
            output = Path(command[command.index('-o') + 1])
            self.sources.append(source)
            self.outputs.append(output)
            output.write_bytes(b'compiled from:' + source.read_bytes())
            return ''
        driver = Path(command[-1]).read_text()
        self.assertIn('run_meta do\n', driver)
        self.assertIn('Air2Lean.Assurance.partialFixpointData', driver)
        if self.mutation == 'source':
            self.sources[0].write_text('changed after compilation')
        if self.mutation == 'artifact':
            self.outputs[0].write_bytes(b'changed after compilation')
        if self.mutation == 'lookup':
            (self.library / 'New.olean').write_bytes(b'new lookup input')
        result = QUERY.MARKER + json.dumps(self.payload) + '\n'
        return result * 2 if self.mutation == 'duplicate' else result

    def compile_command(self, command, env=None):
        return subprocess.CompletedProcess(command, 0, self.run_command(command))

    def test_exact_source_and_new_artifact_are_bound(self):
        result = QUERY.query(self.request)
        self.assertEqual(result['fixpoint_groups'], [])
        expected = hashlib.sha256(self.request['modules'][0]['source'].encode()).hexdigest()
        self.assertEqual(result['preparation']['sources'], {'Fresh.Gen': expected})
        self.assertEqual(len(self.outputs), 1)
        self.assertFalse(self.outputs[0].exists(), 'private outputs must be cleaned after the query')

    def test_split_plan_compiles_dependencies_before_umbrella(self):
        self.request['modules'] = [
            {'name': 'Fresh.Gen.Body', 'source': 'import ZigLean\ndef f := 1\n', 'imports': ['ZigLean']},
            {'name': 'Fresh.Gen', 'source': 'import Fresh.Gen.Body\n', 'imports': ['Fresh.Gen.Body']}]
        result = QUERY.query(self.request)
        self.assertEqual(list(result['preparation']['sources']), ['Fresh.Gen.Body', 'Fresh.Gen'])
        self.assertEqual([path.name for path in self.outputs], ['Body.olean', 'Gen.olean'])

    def test_stale_invoking_binary_refuses_before_build(self):
        (self.root / 'Air2Lean/Control.lean').write_text('new source')
        with self.assertRaisesRegex(ValueError, 'differs from the invoking binary'):
            QUERY.query(self.request)
        self.assertEqual(self.calls, [])

    def test_private_namespace_cannot_fall_back_to_runtime(self):
        self.request['module'] = self.request['modules'][0]['name'] = 'ZigLean.Gen'
        with self.assertRaisesRegex(ValueError, 'no compiled module for ZigLean'):
            QUERY.query(self.request)
        self.assertEqual(self.outputs, [])

    def test_reversed_split_dependencies_refuse_before_build(self):
        self.request['modules'].insert(0, {
            'name': 'Fresh.Umbrella', 'source': 'import Fresh.Gen\n', 'imports': ['Fresh.Gen']})
        with self.assertRaisesRegex(ValueError, 'not in compiler dependency order'):
            QUERY.query(self.request)
        self.assertEqual(self.calls, [])

    def test_source_artifact_lookup_and_duplicate_payload_mutations_refuse(self):
        for mutation, message in [('source', 'source changed'), ('artifact', 'output changed'),
                                  ('lookup', 'lookup inputs changed'), ('duplicate', 'exactly one')]:
            with self.subTest(mutation=mutation):
                self.mutation = mutation
                with self.assertRaisesRegex(ValueError, message):
                    QUERY.query(copy.deepcopy(self.request))
                (self.library / 'New.olean').unlink(missing_ok=True)
                self.sources.clear()
                self.outputs.clear()


if __name__ == '__main__':
    unittest.main()
