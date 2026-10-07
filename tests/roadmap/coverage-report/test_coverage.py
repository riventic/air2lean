"""Offline I06 coverage-report regressions: fixture receipts, audits and diff summaries only."""
import hashlib
import importlib.util
import json
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / 'scripts' / 'project.py'
spec = importlib.util.spec_from_file_location('project', SCRIPT)
project = importlib.util.module_from_spec(spec)
spec.loader.exec_module(project)

GENERATED = 'namespace Example\nend Example\n'
VERIFIER = '''import json, pathlib, sys
attempt = pathlib.Path(sys.argv[2])
if (attempt / 'STALE').exists():
    print('proof receipt unavailable/stale: receipt stale', file=sys.stderr)
    sys.exit(2)
print(json.dumps({'status': 'current', 'checking': 'not_rerun', 'authentication': 'not_attested'}))
'''


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        for name in ('source.zig', 'patch.zig', 'runtime.lean', 'toolchain', 'contract.lean'):
            (self.base / name).write_text(name + '\n')
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        (self.base / 'air.json').write_text(json.dumps({'schema': 11, 'name': 'example.root', 'zig_version': '0.16.0', 'body': []}))
        self.manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['source.zig'],
                         'components': {'compiler_patch': ['patch.zig'], 'runtime': ['runtime.lean'], 'toolchain': ['toolchain']},
                         'allowed_assumptions': ['allocator-policy'],
                         'roots': [{'id': 'root', 'function': 'example.root', 'air': ['air.json'],
                                    'namespace': 'Example', 'prefix': 'example.', 'contracts': ['contract.lean'],
                                    'goals': [{'theorem': 'root_spec', 'strength': 'total_correctness', 'domain': 'all u32 inputs'}],
                                    'assumptions': ['allocator-policy'], 'exclusions': ['backend correspondence unqualified']}]}
        self.path = self.base / 'project.json'
        self.save()
        translator = self.base / 'translator'
        translator.write_text('#!' + sys.executable + "\nimport pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text(%r)\n" % GENERATED)
        translator.chmod(0o755)
        self.artifact = self.base / 'artifact'
        result = subprocess.run([sys.executable, str(SCRIPT), 'translate', str(self.path), '--translator', str(translator),
                                 '--out', str(self.artifact)], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.verifier = self.base / 'verifier.py'
        self.verifier.write_text(VERIFIER)
        self.attempt = self.base / 'attempt'
        self.nodes = [{'name': 'Example.root', 'module': 'Gen.Example.Gen', 'kind': 'definition', 'dependencies': []},
                      {'name': 'Example.root_spec', 'module': 'contract', 'kind': 'theorem', 'dependencies': ['Example.root', 'propext']},
                      {'name': 'propext', 'module': 'Init.Core', 'kind': 'axiom', 'dependencies': []}]
        self.generated_sha = sha(GENERATED)
        self.write_receipt()
        self.diff = self.base / 'diff.json'
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}] * 3)

    def save(self):
        self.path.write_text(json.dumps(self.manifest))

    def write_receipt(self):
        self.attempt.mkdir(exist_ok=True)
        lib = self.base / '.lake/build/lib/lean'
        write = lambda name, value: (self.attempt / name).write_text(json.dumps(value))
        write('receipt.json', {'schema': 1, 'status': 'audited', 'authentication': 'not_attested',
                               'proof_scope': 'selected compiled Lean theorem dependency policy only',
                               'source_correspondence': 'not_attested', 'native_adequacy': 'not_attested',
                               'attempt': str(self.attempt), 'theorem_count': 1, 'artifacts': []})
        write('plan.json', {'schema': 1, 'root': str(self.base), 'modules': ['contract'], 'scope': 'explicit-modules'})
        theorems = [{'name': n['name'], 'module': n['module'], 'axioms': ['propext'], 'opaque_dependencies': [],
                     'extern_dependencies': [], 'compiler_redirections': [], 'violations': [], 'allowed': True}
                    for n in self.nodes if n['kind'] == 'theorem']
        write('audit.json', {'schema_version': 1, 'status': 'pass', 'modules': ['contract'], 'theorem_count': len(theorems),
                             'theorems': theorems, 'nodes': self.nodes, 'violations': []})
        write('after.json', {'context': {'sources': [{'path': str(self.base / 'contract.lean'), 'kind': 'regular',
                                                      'sha256': sha('contract.lean\n'), 'bytes': 14}]},
                             'compiled': [{'path': str(lib / 'contract.olean')}, {'path': str(lib / 'Gen/Example/Gen.olean')}],
                             'profiles': {'Gen/Example/Gen.lean': {'sha256': self.generated_sha, 'metadata': None,
                                                                   'scope': 'legacy-or-unannotated'}}})

    def write_diff(self, rows, sources=None):
        self.diff.write_text(json.dumps({'schema': 1, 'complete': True, 'qualified': False,
                                         'runner_runtime_sources': sources or {'source.zig': sha('source.zig\n')}}))
        Path(str(self.diff) + '.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))

    def run_coverage(self, receipt=True, diff=True, artifact=True):
        return project.coverage(self.path, self.artifact if artifact else None, self.attempt if receipt else None,
                                self.verifier, [self.diff] if diff else [])['roots'][0]

    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), 'coverage', str(self.path), '--artifact', str(self.artifact),
                               '--receipt', str(self.attempt), '--receipt-verifier', str(self.verifier),
                               '--diff', str(self.diff), *args], capture_output=True, text=True, timeout=30)

    def assertNotFunctional(self, root):
        self.assertFalse(root['fully_functionally_verified'])
        self.assertNotIn(root['level'], ('functionally_verified_partial', 'functionally_verified_total'))

    def test_complete_evidence_is_fully_functionally_verified(self):
        root = self.run_coverage()
        self.assertEqual(root['level'], 'functionally_verified_total', root['blockers'])
        self.assertTrue(root['fully_functionally_verified'])
        for name in ('translated', 'compiled', 'tested', 'proved'):
            self.assertEqual(root['stages'][name]['status'], 'passed', name)
        self.assertEqual(root['stages']['tested']['scope'], 'sampled')
        for name in ('analyzed', 'exported'):
            self.assertEqual(root['stages'][name]['status'], 'not_run')
        self.assertEqual(root['goals'][0]['binding'], 'direct')
        self.assertEqual(root['goals'][0]['audited_theorem'], 'Example.root_spec')
        self.assertEqual(root['contract_domain'][0]['domain'], 'all u32 inputs')
        self.assertEqual(root['theorem_strength']['direct'], ['total_correctness'])
        self.assertEqual(root['assumptions']['declared'], ['allocator-policy'])
        self.assertEqual(root['assumptions']['audited']['axioms'], ['propext'])
        self.assertIn('backend correspondence unqualified', root['exclusions'])
        self.assertIn('proof receipt native_adequacy: not_attested', root['exclusions'])

    def test_wrapper_only_theorem_is_not_functional(self):
        self.nodes[1]['dependencies'] = ['Example.wrapper']
        self.nodes.append({'name': 'Example.wrapper', 'module': 'contract', 'kind': 'definition', 'dependencies': ['Example.root']})
        self.write_receipt()
        root = self.run_coverage()
        self.assertEqual(root['goals'][0]['binding'], 'wrapper_or_unrelated')
        self.assertEqual(root['stages']['proved']['status'], 'failed')
        self.assertEqual(root['level'], 'tested_sampled')
        self.assertNotFunctional(root)

    def test_theorem_about_other_definition_is_wrapper(self):
        self.nodes[1]['dependencies'] = ['Example.spec_model']
        self.nodes.append({'name': 'Example.spec_model', 'module': 'contract', 'kind': 'definition', 'dependencies': []})
        self.write_receipt()
        root = self.run_coverage(diff=False)
        self.assertEqual(root['goals'][0]['binding'], 'wrapper_or_unrelated')
        self.assertEqual(root['level'], 'compiled')
        self.assertNotFunctional(root)

    def test_sampled_tests_only_are_not_functional(self):
        root = self.run_coverage(receipt=False)
        self.assertEqual(root['stages']['tested']['status'], 'passed')
        self.assertEqual(root['stages']['proved']['status'], 'not_run')
        self.assertEqual(root['level'], 'translated')
        self.assertNotFunctional(root)
        # Even with compiled evidence and no theorem goals, passing samples stop at tested_sampled.
        self.manifest['roots'][0]['goals'] = []
        self.save()
        self.rebuild_artifact()
        root = self.run_coverage()
        self.assertEqual(root['level'], 'tested_sampled')
        self.assertIn('no declared theorem goals', root['blockers'])
        self.assertNotFunctional(root)

    def test_stale_receipt(self):
        (self.attempt / 'STALE').write_text('')
        root = self.run_coverage()
        self.assertEqual(root['stages']['compiled']['status'], 'failed')
        self.assertEqual(root['stages']['proved']['status'], 'failed')
        self.assertIn('stale', root['stages']['proved']['reason'])
        self.assertEqual(root['goals'][0]['binding'], 'stale_receipt')
        self.assertNotFunctional(root)

    def test_mismatched_generated_hash(self):
        self.generated_sha = sha('other generated bytes')
        self.write_receipt()
        root = self.run_coverage()
        self.assertEqual(root['stages']['compiled']['status'], 'failed')
        self.assertIn('source hash mismatch', root['stages']['compiled']['reason'])
        self.assertEqual(root['goals'][0]['binding'], 'source_hash_mismatch')
        self.assertNotFunctional(root)

    def test_mismatched_contract_hash(self):
        after = json.loads((self.attempt / 'after.json').read_text())
        after['context']['sources'][0]['sha256'] = sha('contract bytes the receipt compiled')
        (self.attempt / 'after.json').write_text(json.dumps(after))
        root = self.run_coverage()
        self.assertEqual(root['stages']['translated']['status'], 'passed')
        self.assertEqual(root['stages']['compiled']['status'], 'failed')
        self.assertIn('contract contract.lean differs', root['stages']['compiled']['reason'])
        self.assertEqual(root['goals'][0]['binding'], 'source_hash_mismatch')
        self.assertNotFunctional(root)

    def test_uncompiled_generated_module(self):
        after = json.loads((self.attempt / 'after.json').read_text())
        after['compiled'] = after['compiled'][:1]
        (self.attempt / 'after.json').write_text(json.dumps(after))
        root = self.run_coverage()
        self.assertEqual(root['stages']['compiled']['status'], 'failed')
        self.assertNotFunctional(root)

    def test_stale_translation_artifact(self):
        (self.base / 'source.zig').write_text('edited\n')
        root = self.run_coverage()
        self.assertEqual(root['stages']['translated']['status'], 'failed')
        self.assertEqual(root['level'], 'none')

    def test_missing_goal_theorem(self):
        self.manifest['roots'][0]['goals'].append({'theorem': 'root_bound', 'strength': 'safety', 'domain': 'n < 10'})
        self.save()
        self.rebuild_artifact()
        root = self.run_coverage()
        self.assertEqual([g['binding'] for g in root['goals']], ['direct', 'missing'])
        self.assertEqual(root['stages']['proved']['status'], 'partial')
        self.assertEqual(root['level'], 'proved_scoped')
        self.assertNotFunctional(root)

    def test_strength_rules(self):
        for strength, level in (('partial_correctness', 'functionally_verified_partial'), ('safety', 'proved_scoped'),
                                ('resource_bound', 'proved_scoped'), ('correspondence', 'proved_scoped')):
            with self.subTest(strength=strength):
                self.manifest['roots'][0]['goals'][0]['strength'] = strength
                self.save()
                self.rebuild_artifact()
                root = self.run_coverage()
                self.assertEqual(root['level'], level, root['blockers'])
                self.assertFalse(root['fully_functionally_verified'])

    def test_outside_contract_and_policy_violation(self):
        self.nodes[1]['module'] = 'Elsewhere'
        self.write_receipt()
        self.assertEqual(self.run_coverage()['goals'][0]['binding'], 'outside_contracts')
        self.nodes[1]['module'] = 'contract'
        self.write_receipt()
        audit = json.loads((self.attempt / 'audit.json').read_text())
        audit['theorems'][0].update(allowed=False, violations=['sorryAx'])
        (self.attempt / 'audit.json').write_text(json.dumps(audit))
        root = self.run_coverage()
        self.assertEqual(root['goals'][0]['binding'], 'policy_violation')
        self.assertNotFunctional(root)

    def test_differential_failures_and_staleness(self):
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'mismatch'}])
        self.assertEqual(self.run_coverage()['stages']['tested']['status'], 'failed')
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}],
                        {'source.zig': sha('older source')})
        tested = self.run_coverage()['stages']['tested']
        self.assertEqual(tested['status'], 'failed')
        self.assertIn('stale differential evidence', tested['reason'])
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}], {'other.zig': 'x'})
        self.assertIn('does not hash', self.run_coverage()['stages']['tested']['reason'])
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'unspecified_exclusion'},
                         {'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}])
        root = self.run_coverage()
        self.assertEqual(root['stages']['tested']['status'], 'passed')
        self.assertIn('differential unspecified_exclusion: 1 sampled case(s)', root['exclusions'])
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'future_status'},
                         {'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}])
        self.assertEqual(self.run_coverage()['stages']['tested']['status'], 'failed')  # unknown statuses fail closed
        self.diff.write_text(json.dumps({'schema': 1, 'complete': False}))
        self.assertEqual(self.run_coverage()['stages']['tested']['status'], 'failed')

    def test_symlinked_contract_binds_by_tracked_path(self):
        (self.base / 'contract-target.lean').write_text('contract.lean\n')
        (self.base / 'contract.lean').unlink()
        (self.base / 'contract.lean').symlink_to('contract-target.lean')
        root = self.run_coverage()
        self.assertEqual(root['stages']['compiled']['status'], 'passed', root['stages']['compiled'])
        self.assertEqual(root['goals'][0]['binding'], 'direct')

    def test_deleted_contract_reports_without_aborting(self):
        (self.base / 'contract.lean').unlink()
        root = self.run_coverage()
        self.assertEqual(root['input_validation']['status'], 'failed')
        self.assertEqual(root['goals'][0]['binding'], 'unbound')
        self.assertEqual(root['level'], 'none')

    def test_no_evidence(self):
        root = self.run_coverage(receipt=False, diff=False, artifact=False)
        self.assertEqual(root['level'], 'none')
        self.assertTrue(all(root['stages'][s]['status'] == 'not_run' for s in project.STAGES))

    def test_cli_json_text_and_required_level(self):
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['roots'][0]['level'], 'functionally_verified_total')
        text = self.cli('--format', 'text')
        self.assertIn('root (example.root): functionally_verified_total [fully functionally verified]', text.stdout)
        self.assertIn('goal root_spec [total_correctness] domain: all u32 inputs -> direct', text.stdout)
        out = self.base / 'coverage.json'
        self.assertEqual(self.cli('--out', out).returncode, 0)
        self.assertEqual(json.loads(out.read_text())['kind'], 'air2lean-coverage-report')
        self.assertNotEqual(self.cli('--out', out).returncode, 0)  # no-clobber by default
        (self.attempt / 'STALE').write_text('')
        self.assertEqual(self.cli('--require-level', 'functionally_verified_total').returncode, 1)
        self.assertEqual(self.cli('--require-level', 'translated').returncode, 0)

    def rebuild_artifact(self):
        shutil.rmtree(self.artifact)
        result = subprocess.run([sys.executable, str(SCRIPT), 'translate', str(self.path), '--translator',
                                 str(self.base / 'translator'), '--out', str(self.artifact)],
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
