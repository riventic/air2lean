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
# Theorem entries extracted from tests/roadmap/assurance/StatementBinding.lean; that check.sh
# requires the real extraction to match this file exactly.
STATEMENT_FIXTURE = json.loads((Path(__file__).parent / 'statement-binding.json').read_text())
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
        # Statement-only dependencies per theorem: (statement, conclusion). Unlisted theorems state
        # their conclusion about every non-axiom declaration they depend on.
        self.statements = {}
        # Kernel conclusion shapes per theorem; unlisted theorems conclude a Zig.TotalTriple.
        self.conclusions = {}
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
        write('receipt.json', {'schema': 2, 'status': 'audited', 'authentication': 'not_attested',
                               'proof_scope': 'selected compiled Lean theorem dependency policy only',
                               'source_correspondence': 'not_attested', 'native_adequacy': 'not_attested',
                               'attempt': str(self.attempt), 'theorem_count': 1, 'artifacts': []})
        write('plan.json', {'schema': 1, 'root': str(self.base), 'modules': ['contract'], 'scope': 'explicit-modules'})
        def statement(node):
            default = [d for d in node['dependencies'] if d != 'propext']
            deps, conclusion = self.statements.get(node['name'], (default, default))
            return {'statement_dependencies': deps, 'conclusion_dependencies': conclusion,
                    'conclusion': self.conclusions.get(node['name'], {'head': 'Zig.TotalTriple', 'args': []})}
        theorems = [{'name': n['name'], 'module': n['module'], 'axioms': ['propext'], 'opaque_dependencies': [],
                     'extern_dependencies': [], 'compiler_redirections': [], 'violations': [], 'allowed': True,
                     **statement(n)} for n in self.nodes if n['kind'] == 'theorem']
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

    def use_statement_fixture(self, *goals):
        """Bind goals against real extracted theorems; the fixture's root stands in for generated code."""
        self.nodes = [{'name': 'StatementFixture.root', 'module': 'Gen.Example.Gen', 'kind': 'definition', 'dependencies': []}]
        for theorem in STATEMENT_FIXTURE['theorems']:
            self.nodes.append({'name': theorem['name'], 'module': 'contract', 'kind': 'theorem',
                               'dependencies': theorem['dependencies']})
            self.statements[theorem['name']] = (theorem['statement_dependencies'], theorem['conclusion_dependencies'])
            self.conclusions[theorem['name']] = theorem['conclusion']
        self.write_receipt()
        self.manifest['roots'][0]['namespace'] = 'StatementFixture'
        self.manifest['roots'][0]['goals'] = [{'theorem': g, 'strength': 'total_correctness', 'domain': 'all'} for g in goals]
        self.save()
        self.rebuild_artifact()
        return self.run_coverage()

    def test_only_statements_about_the_root_bind(self):
        names = ['wrapper_spec', 'trivial_spec', 'premise_only', 'root_spec']
        # Every fixture proof term mentions the root, so declaration edges alone would bind all four.
        self.assertTrue(all('StatementFixture.root' in t['dependencies'] for t in STATEMENT_FIXTURE['theorems']))
        self.assertEqual(sorted(t['name'] for t in STATEMENT_FIXTURE['theorems']),
                         sorted('StatementFixture.' + n for n in names))
        root = self.use_statement_fixture(*names)
        self.assertEqual([g['binding'] for g in root['goals']], ['wrapper_or_unrelated'] * 3 + ['direct'])
        self.assertEqual(root['stages']['proved']['status'], 'partial')
        self.assertNotFunctional(root)
        for name in names[:3]:
            with self.subTest(goal=name):
                root = self.use_statement_fixture(name)
                self.assertEqual(root['goals'][0]['binding'], 'wrapper_or_unrelated')
                self.assertEqual(root['stages']['proved']['status'], 'failed')
                self.assertNotFunctional(root)
        root = self.use_statement_fixture('root_spec')
        self.assertEqual(root['goals'][0]['binding'], 'direct')
        # `root x = x + 1` is about the root but is no Zig triple or exact-success equation:
        # claims.py derives no strength, so the declared total_correctness is not credited.
        self.assertEqual((root['goals'][0]['derived_strength'], root['goals'][0]['claim_class']), (None, 'unclassified'))
        self.assertEqual(root['level'], 'proved_scoped')
        self.assertNotFunctional(root)
        self.conclusions['StatementFixture.root_spec'] = {'head': 'Zig.TotalTriple', 'args': []}
        self.write_receipt()
        root = self.run_coverage()
        self.assertEqual(root['level'], 'functionally_verified_total', root['blockers'])

    def test_trivial_conclusion_cannot_reach_functional_levels(self):
        # `Example.root x = Example.root x`: the conclusion names the root, so statement binding passes,
        # but its right-hand side is the root itself: it fixes no result. It is a trivial_conclusion,
        # not a direct goal, whatever strength the manifest declares.
        self.conclusions['Example.root_spec'] = {'head': 'Eq', 'args': [{'head': 'Example.root'}]}
        self.write_receipt()
        for strength in ('total_correctness', 'partial_correctness', 'safety'):
            with self.subTest(strength=strength):
                self.manifest['roots'][0]['goals'][0]['strength'] = strength
                self.save()
                self.rebuild_artifact()
                root = self.run_coverage()
                goal = root['goals'][0]
                self.assertEqual((goal['binding'], goal['derived_strength'], goal['claim_class']),
                                 ('trivial_conclusion', None, 'unclassified'))
                self.assertIn('only relates the generated root Example.root to itself', goal['reason'])
                self.assertEqual(root['stages']['proved']['status'], 'failed')
                self.assertEqual(root['level'], 'tested_sampled')
                self.assertNotFunctional(root)
                self.assertTrue(any('trivial_conclusion' in b for b in root['blockers']), root['blockers'])
                self.assertEqual(root['theorem_strength']['direct'], [])
                self.assertEqual(root['theorem_strength']['derived'], [])
                self.assertEqual({c: v['status'] for c, v in root['absence_claims'].items()},
                                 {'no-panic': 'not_proved', 'guaranteed-return': 'not_proved'})
        # Without sampled tests it stays merely compiled, never proved_scoped.
        self.assertEqual(self.run_coverage(diff=False)['level'], 'compiled')
        # Beside a real theorem the trivial one still blocks the root and is not counted.
        self.nodes.append({'name': 'Example.second_spec', 'module': 'contract', 'kind': 'theorem',
                           'dependencies': ['Example.root', 'propext']})
        self.write_receipt()
        self.manifest['roots'][0]['goals'] = [
            {'theorem': 'root_spec', 'strength': 'total_correctness', 'domain': 'all'},
            {'theorem': 'second_spec', 'strength': 'total_correctness', 'domain': 'all'}]
        self.save()
        self.rebuild_artifact()
        root = self.run_coverage()
        self.assertEqual([g['binding'] for g in root['goals']], ['trivial_conclusion', 'direct'])
        self.assertEqual(root['stages']['proved']['status'], 'partial')
        self.assertEqual(root['level'], 'proved_scoped')
        self.assertNotFunctional(root)
        self.manifest['roots'][0]['goals'] = self.manifest['roots'][0]['goals'][:1]
        self.save()
        self.rebuild_artifact()
        # `root x = x + 1` has the same unclassified strength but is not called trivial.
        self.conclusions['Example.root_spec'] = {'head': 'Eq', 'args': [{'head': 'HAdd.hAdd'}]}
        self.write_receipt()
        root = self.run_coverage()
        self.assertEqual((root['goals'][0]['binding'], root['level']), ('direct', 'proved_scoped'))
        # A partial triple cannot be credited as total correctness; it still counts as partial.
        self.conclusions['Example.root_spec'] = {'head': 'Zig.Triple', 'args': []}
        self.write_receipt()
        self.manifest['roots'][0]['goals'][0]['strength'] = 'total_correctness'
        self.save()
        self.rebuild_artifact()
        root = self.run_coverage()
        self.assertEqual(root['level'], 'proved_scoped')
        self.assertTrue(any('exceeds type-derived partial_correctness' in b for b in root['blockers']), root['blockers'])
        self.manifest['roots'][0]['goals'][0]['strength'] = 'partial_correctness'
        self.save()
        self.rebuild_artifact()
        self.assertEqual(self.run_coverage()['level'], 'functionally_verified_partial')
        # An audit from an extractor without conclusion shapes derives nothing.
        audit = json.loads((self.attempt / 'audit.json').read_text())
        for theorem in audit['theorems']:
            del theorem['conclusion']
        (self.attempt / 'audit.json').write_text(json.dumps(audit))
        self.assertEqual(self.run_coverage()['level'], 'proved_scoped')

    def test_audit_without_statement_dependencies_fails_closed(self):
        audit = json.loads((self.attempt / 'audit.json').read_text())
        for theorem in audit['theorems']:
            del theorem['statement_dependencies'], theorem['conclusion_dependencies']
        (self.attempt / 'audit.json').write_text(json.dumps(audit))
        root = self.run_coverage()
        self.assertEqual(root['goals'][0]['binding'], 'unbound')
        self.assertIn('statement dependencies', root['goals'][0]['reason'])
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

    def test_evidence_cap_matches_the_receipt_writer(self):
        # A receipt proof-receipt.py may write (an all-shipped audit.json exceeds 64 MiB) must be readable.
        receipt_spec = importlib.util.spec_from_file_location('proof_receipt', SCRIPT.parent / 'proof-receipt.py')
        receipt = importlib.util.module_from_spec(receipt_spec)
        receipt_spec.loader.exec_module(receipt)
        self.assertEqual(project.EVIDENCE_JSON['max_file_bytes'], receipt.MAX_JSON)

    def test_stale_receipt(self):
        (self.attempt / 'STALE').write_text('')
        root = self.run_coverage()
        self.assertEqual(root['stages']['compiled']['status'], 'failed')
        self.assertEqual(root['stages']['proved']['status'], 'failed')
        self.assertIn('stale', root['stages']['proved']['reason'])
        self.assertEqual(root['goals'][0]['binding'], 'stale_receipt')
        self.assertNotFunctional(root)

    def test_headerless_module_binds_to_headed_translation(self):
        header = ('-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"unverified",'
                  '"backend":"unverified","build_mode":"unverified","cpu":"unverified","endian":"little",'
                  '"error_layout":"reference-model","error_set_bits":16,"error_tracing":null,"export_stage":"unverified",'
                  '"features":[],"float_mode":"unverified","name":"legacy-abi64-le","pointer_bits":64,"schema":11,'
                  '"target_triple":"unverified","zig_version":"0.16.0"}}\n')
        translator = self.base / 'translator'
        translator.write_text(translator.read_text().replace(repr(GENERATED), repr(header + GENERATED)))
        self.rebuild_artifact()
        # The receipt's module (fixture: no profile record, metadata None) equals the translation body.
        self.assertEqual(self.run_coverage()['level'], 'functionally_verified_total')
        # A module carrying the record must match the whole file.
        self.generated_sha = sha(GENERATED)
        self.write_receipt()
        after = json.loads((self.attempt / 'after.json').read_text())
        entry = after['profiles']['Gen/Example/Gen.lean']
        entry['metadata'] = {'profile': 'recorded'}
        (self.attempt / 'after.json').write_text(json.dumps(after))
        self.assertEqual(self.run_coverage()['stages']['compiled']['status'], 'failed')
        entry['sha256'] = sha(header + GENERATED)
        (self.attempt / 'after.json').write_text(json.dumps(after))
        self.assertEqual(self.run_coverage()['stages']['compiled']['status'], 'passed')

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

    def test_absence_claims_from_outcome_taxonomy(self):
        root = self.run_coverage()
        self.assertEqual({c: v['status'] for c, v in root['absence_claims'].items()},
                         {'no-panic': 'proved', 'guaranteed-return': 'proved'})
        self.assertEqual(root['outcomes'], {'valid': 3})
        # Error returns are values, not panics: they never refuse no-panic.
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'error_return_match',
                          'model_kind': 'error_return'}] * 2)
        root = self.run_coverage()
        self.assertEqual(root['level'], 'functionally_verified_total', root['blockers'])
        self.assertEqual(root['absence_claims']['no-panic']['status'], 'proved')
        capped = {'status': 'capped', 'runs': 8, 'cap': 8, 'fuel': 100, 'saw_no_result': False}
        refusing = [{'status': 'search_cap', 'model_kind': 'value', 'schedule': capped},
                    {'status': 'unspecified_exclusion', 'model_kind': 'unspecified'},
                    {'status': 'bounded_no_result', 'model_kind': 'bounded_no_result',
                     'schedule': dict(capped, status='bounded', saw_no_result=True)}]
        for extra in refusing:
            with self.subTest(extra=extra):
                self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'},
                                 dict(extra, schema=1, example='example', function='root')])
                root = self.run_coverage()
                self.assertEqual(root['stages']['tested']['status'], 'passed')
                self.assertEqual(root['absence_claims']['no-panic']['status'], 'refused')
                self.assertTrue(any(b.startswith('absence claim no-panic refused') for b in root['blockers']))
                self.assertEqual(root['level'], 'proved_scoped')
        # Sampled tests alone never prove absence, even when clean.
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}])
        root = self.run_coverage(receipt=False)
        self.assertEqual(root['absence_claims']['no-panic']['status'], 'not_proved')
        # Partial correctness asserts no-panic but not a guaranteed return.
        self.manifest['roots'][0]['goals'][0]['strength'] = 'partial_correctness'
        self.save()
        self.rebuild_artifact()
        claims = self.run_coverage()['absence_claims']
        self.assertEqual((claims['no-panic']['status'], claims['guaranteed-return']['status']), ('proved', 'not_proved'))

    def test_unsupported_timer_is_distinct_and_refuses_absence(self):
        timer = {'schema': 1, 'example': 'example', 'function': 'root', 'status': 'unspecified_timer_exclusion',
                 'model_kind': 'unspecified_timer'}
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'}, timer])
        root = self.run_coverage()
        self.assertEqual(root['stages']['tested']['status'], 'passed')
        self.assertIn('differential unspecified_timer_exclusion: 1 sampled case(s)', root['exclusions'])
        self.assertEqual(root['outcomes'], {'valid': 1, 'unspecified_timer': 1})
        for claim in ('no-panic', 'guaranteed-return'):
            verdict = root['absence_claims'][claim]
            self.assertEqual(verdict['status'], 'refused')
            self.assertEqual(verdict['blocking'], {'unspecified_timer': 1})
            self.assertIn('unsupported timer', verdict['reason'])
        self.assertEqual(root['level'], 'proved_scoped')
        # A non-timer unspecified result stays `unspecified`.
        self.write_diff([{'schema': 1, 'example': 'example', 'function': 'root', 'status': 'value_match'},
                         dict(timer, status='unspecified_exclusion', model_kind='unspecified')])
        root = self.run_coverage()
        self.assertEqual(root['outcomes'], {'valid': 1, 'unspecified_behavior': 1})
        self.assertNotIn('unsupported timer', root['absence_claims']['no-panic']['reason'])

    def test_unsupported_air_is_an_outcome_and_not_proved_absence(self):
        (self.base / 'air.json').write_text(json.dumps({'schema': 11, 'name': 'example.root', 'zig_version': '0.16.0',
                                                        'body': [{'id': 1, 'tag': 'future', 'unsupported': True}]}))
        root = self.run_coverage()
        self.assertEqual(root['outcomes'].get('unsupported_semantics'), 1, root['outcomes'])
        self.assertNotEqual(root['absence_claims']['no-panic']['status'], 'proved')
        self.assertEqual(project.absence_claims([{'theorem': 't', 'binding': 'direct', 'strength': 'safety', 'derived_strength': 'safety'}],
                                                root['outcomes'])['no-panic']['status'], 'refused')

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
