"""I06 analyzed/exported evidence: bound to an I07 artifact manifest, stale or foreign evidence fails closed.

Uses the artifact-manifest test's tiny fixture repository (git, no Zig/Lake/Lean).
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


project = load('project', ROOT / 'scripts/project.py')
fixtures = load('manifest_fixtures', ROOT / 'tests/roadmap/artifact-manifest/test_manifest.py')


class ExportEvidenceTests(unittest.TestCase):
    def setUp(self):
        # Reuse the fixture repository builder; only its setUp/record/write helpers are used.
        self.fixture = fixtures.ManifestTests('setUp')
        self.fixture.setUp()
        self.addCleanup(self.fixture.tearDown)
        self.fixture.record()
        self.repo = self.fixture.repo
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        copy = lambda name, source: (self.base / name).write_bytes((self.repo / source).read_bytes())
        copy('demo.zig', 'examples/demo/demo.zig')
        copy('add.json', 'tests/golden/0.16.0/demo/air/demo.add.json')
        for name in ('runtime', 'toolchain', 'patch'):
            (self.base / name).write_text(name + '\n')
        (self.base / 'profile.json').write_text(json.dumps(fixtures.PROFILE))
        self.manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['demo.zig'],
                         'components': {'compiler_patch': ['patch'], 'runtime': ['runtime'], 'toolchain': ['toolchain']},
                         'allowed_assumptions': [],
                         'roots': [{'id': 'add', 'function': 'demo.add', 'air': ['add.json'], 'namespace': 'Demo',
                                    'prefix': 'demo.', 'contracts': [], 'goals': [], 'assumptions': [], 'exclusions': []}]}
        self.path = self.base / 'project.json'
        self.save()

    def save(self):
        self.path.write_text(json.dumps(self.manifest))

    def stages(self, **kwargs):
        result = project.coverage(self.path, export_manifest=self.fixture.manifest, repo_root=self.repo, **kwargs)
        self.assertEqual(result['diagnostics'], [])
        return result['roots'][0]['stages']

    def assert_failed(self, stages, text):
        for name in ('analyzed', 'exported'):
            self.assertEqual(stages[name]['status'], 'failed', name)
            self.assertIn(text, stages[name]['reason'])

    def test_current_manifest_binds_analyzed_and_exported(self):
        stages = self.stages()
        for name in ('analyzed', 'exported'):
            self.assertEqual(stages[name]['status'], 'passed', stages[name])
            self.assertEqual(stages[name]['manifest_sha256'],
                             json.loads(self.fixture.manifest.read_text())['manifest_sha256'])
        self.assertEqual(sorted(stages['exported']['links']), ['air', 'compiler_patch', 'profile', 'source'])
        self.assertIn('not rerun', stages['exported']['reason'])

    def test_no_manifest_is_not_evidence(self):
        stages = project.coverage(self.path)['roots'][0]['stages']
        self.assertEqual((stages['analyzed']['status'], stages['exported']['status']), ('not_run', 'not_run'))

    def test_stale_links_fail_closed(self):
        self.fixture.write('examples/demo/demo.zig', 'export fn add(a: u32, b: u32) u32 { return a -% b; }\n')
        self.assert_failed(self.stages(), 'stale export manifest: links [\'source\']')

    def test_unrelated_stale_links_do_not_matter(self):
        self.fixture.write('Proofs/Demo/Proofs.lean', fixtures.PROOFS.replace('theorem toplevel', 'theorem renamed'))
        self.assertEqual(self.stages()['exported']['status'], 'passed')

    def test_foreign_air_or_source_or_profile_is_not_covered(self):
        (self.base / 'add.json').write_text(fixtures.air('demo.add').replace('"params": []', '"params": [0]'))
        self.assert_failed(self.stages(), 'AIR [\'add.json\'] not among recorded AIR files')
        (self.base / 'add.json').write_bytes((self.repo / 'tests/golden/0.16.0/demo/air/demo.add.json').read_bytes())
        (self.base / 'demo.zig').write_text('other\n')
        self.assert_failed(self.stages(), 'sources [\'demo.zig\'] not among recorded source files')

    def test_profile_difference_fails(self):
        (self.base / 'demo.zig').write_bytes((self.repo / 'examples/demo/demo.zig').read_bytes())
        (self.base / 'profile.json').write_text(json.dumps(dict(fixtures.PROFILE, cpu='other')))
        stages = project.coverage(self.path, export_manifest=self.fixture.manifest, repo_root=self.repo)['roots'][0]['stages']
        for name in ('analyzed', 'exported'):
            self.assertEqual(stages[name]['status'], 'failed')

    def test_missing_or_tampered_manifest_fails(self):
        def tamper(path):
            edited = json.loads(path.read_text())
            edited['links']['source']['sha256'] = '0' * 64
            path.write_text(json.dumps(edited))
        for edit in (lambda p: p.unlink(), tamper):
            edit(self.fixture.manifest)
            result = project.coverage(self.path, export_manifest=self.fixture.manifest, repo_root=self.repo)
            stages = result['roots'][0]['stages']
            self.assertEqual((stages['analyzed']['status'], stages['exported']['status']), ('failed', 'failed'))
            self.fixture.manifest.unlink(missing_ok=True)
            self.fixture.record()

    def test_dirty_manifest_provenance_fails(self):
        self.fixture.manifest.unlink()
        (self.repo / 'examples/demo/dirty.zig').write_text('pub const x = 1;\n')
        self.fixture.record()
        (self.repo / 'examples/demo/dirty.zig').unlink()
        stages = project.coverage(self.path, export_manifest=self.fixture.manifest, repo_root=self.repo)['roots'][0]['stages']
        self.assertEqual(stages['exported']['status'], 'failed')

    def test_level_gate(self):
        def record(analyzed, exported, **extra):
            names = ('analyzed', 'exported', 'translated', 'compiled', 'tested', 'proved')
            stages = {n: {'status': 'passed', 'reason': ''} for n in names}
            stages['analyzed'], stages['exported'] = {'status': analyzed, 'reason': 'r'}, {'status': exported, 'reason': 'r'}
            goal = {'theorem': 't', 'binding': 'direct', 'strength': 'total_correctness', 'derived_strength': 'total_correctness'}
            return {'stages': stages, 'goals': [goal], 'input_validation': {'status': 'passed'}, 'absence_claims': {}}
        level = lambda *a, **k: project.coverage_level(record(*a), **k)[0]
        self.assertEqual(level('passed', 'passed', require_export=True), 'functionally_verified_total')
        self.assertEqual(level('not_run', 'not_run'), 'functionally_verified_total')  # opt-in gate
        self.assertEqual(level('not_run', 'not_run', require_export=True), 'proved_scoped')
        self.assertEqual(level('passed', 'failed'), 'proved_scoped')  # a failed stage always blocks
        self.assertEqual(level('failed', 'passed'), 'proved_scoped')

    def test_cli_require_export_evidence(self):
        argv = [sys.executable, str(ROOT / 'scripts/project.py'), 'coverage', str(self.path),
                '--export-manifest', str(self.fixture.manifest), '--export-root', str(self.repo)]
        result = subprocess.run(argv + ['--require-export-evidence', '--format', 'text'], capture_output=True, text=True, timeout=60)
        self.assertIn('analyzed    passed', result.stdout, result.stderr)
        self.assertIn('exported    passed', result.stdout)


if __name__ == '__main__':
    unittest.main()
