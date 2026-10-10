#!/usr/bin/env python3
"""F01 float-semantics label regressions, with negative controls. No Lean build.

The checked-environment controls (a compiled unlabeled theorem) are in
tests/roadmap/assurance/check.sh; these tests drive the same code on synthetic graphs.
"""
import copy
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


fs = load('float_semantics', 'scripts/float-semantics.py')
audit = load('assumptions', 'scripts/assumptions.py')
ALL = ['0.14.1', '0.15.2', '0.16.0']
BOTH = ['aarch64-macos', 'x86_64-linux']
IEEE = {'semantics': 'ieee', 'targets': BOTH, 'correspondence': 'model'}
ABSTRACT = {'semantics': 'abstract-spec', 'targets': BOTH, 'correspondence': 'model'}
RT = {'semantics': 'compiler-rt', 'zig_versions': ALL, 'targets': BOTH, 'correspondence': 'model'}


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


class GeneratedNameTests(unittest.TestCase):
    def test_private_theorems_are_not_compiler_generated(self):
        self.assertFalse(fs.is_auxiliary('_private.ZigLean.Float.Ops.0.add_comm'))
        self.assertFalse(fs.is_auxiliary('Foo._bar'))
        self.assertTrue(fs.is_auxiliary('_private.ZigLean.Float.Ops.0.add_comm._proof_1'))
        for name in ('A._proof_1_2', 'A.b._simp_1', 'A._sparseCasesOn_1', 'A.eq_1', 'A.injEq'):
            self.assertTrue(fs.is_auxiliary(name), name)


class RegistryTests(unittest.TestCase):
    def setUp(self):
        self.registry = json.loads((ROOT / 'assurance/float-semantics.json').read_text())
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        write(self.root / 'zig-patch/versions.toml', (ROOT / 'zig-patch/versions.toml').read_text())

    def tearDown(self):
        self.temporary.cleanup()

    def load(self, registry):
        write(self.root / 'assurance/float-semantics.json', json.dumps(registry))
        return fs.load_registry(root=self.root)

    def test_shipped_registry_is_valid_and_complete(self):
        registry = fs.load_registry()
        self.assertEqual(fs.check_sources(ROOT, registry), [])
        semantics = {entry['semantics'] for entry in registry['theorems'].values()}
        self.assertEqual(semantics, set(fs.SEMANTICS))
        self.assertTrue(all(e['correspondence'] == 'model' for e in registry['theorems'].values()))
        # The compiler-rt example's helper-dependent theorems are labeled with their versions.
        self.assertEqual(registry['theorems']['Proofs.Floatops.Proofs::op16_spec'], RT)
        self.assertEqual(registry['theorems']['Proofs.Floats.Proofs::clamp_spec'], IEEE)
        self.assertEqual(registry['theorems']['ZigLean.Float.RoundTrip::Zig.roundRat_finiteToRat'], ABSTRACT)

    def test_binary_correspondence_claims_are_rejected(self):
        for claim in ('binary', 'native', 'bit-exact', None):
            with self.subTest(claim=claim):
                bad = copy.deepcopy(self.registry)
                bad['theorems']['Proofs.Floats.Proofs::clamp_spec']['correspondence'] = claim
                with self.assertRaisesRegex(ValueError, 'unsupported binary-correspondence claim'):
                    self.load(bad)
        bad = copy.deepcopy(self.registry)
        bad['checks']['tests/review/Floats.lean']['correspondence'] = 'native'
        with self.assertRaisesRegex(ValueError, 'unsupported binary-correspondence claim'):
            self.load(bad)

    def test_malformed_labels_are_rejected(self):
        key = 'Proofs.Floatops.Proofs::op16_spec'
        cases = [
            ({'semantics': 'x87', 'targets': BOTH, 'correspondence': 'model'}, 'unknown float semantics'),
            ({'semantics': 'compiler-rt', 'targets': BOTH, 'correspondence': 'model'}, 'invalid label fields'),
            ({'semantics': 'ieee', 'correspondence': 'model'}, 'sorted unique targets'),
            (dict(IEEE, targets=[]), 'sorted unique targets'),
            (dict(IEEE, targets=['x86_64-linux', 'aarch64-macos']), 'sorted unique targets'),
            (dict(IEEE, targets=['wasm32-wasi']), 'sorted unique targets'),
            (dict(RT, zig_versions=[]), 'sorted unique Zig versions'),
            (dict(RT, zig_versions=['0.16.0', '0.15.2']), 'sorted unique Zig versions'),
            (dict(RT, zig_versions=['0.13.0']), 'unsupported Zig version'),
            (dict(IEEE, zig_versions=ALL), 'invalid label fields'),
            (dict(IEEE, note='x'), 'invalid label fields'),
        ]
        for entry, message in cases:
            with self.subTest(entry=entry):
                bad = copy.deepcopy(self.registry)
                bad['theorems'][key] = entry
                with self.assertRaisesRegex(ValueError, message):
                    self.load(bad)
        bad = copy.deepcopy(self.registry)
        bad['non_numerical'][key] = 'both'
        with self.assertRaisesRegex(ValueError, 'both labeled and exempt'):
            self.load(bad)
        bad = copy.deepcopy(self.registry)
        bad['theorems']['no-separator'] = IEEE
        with self.assertRaisesRegex(ValueError, 'invalid registry key'):
            self.load(bad)
        bad = copy.deepcopy(self.registry)
        bad['checks']['tests/review/Floats.lean']['labels'] = ['compiler-rt']
        with self.assertRaises(ValueError):
            self.load(bad)
        write(self.root / 'assurance/float-semantics.json', '{"schema_version": 1, "schema_version": 1}')
        with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
            fs.load_registry(root=self.root)

    def test_witness_commands_declare_companions(self):
        text = 'namespace A\nnonvacuity_witness t := ⟨Float.zero⟩\nliveness_witness t :=\n  rfl\nend A\n'
        self.assertEqual([(k, n) for k, n, _ in fs.declarations(text)],
                         [('theorem', 'A.t.nonvacuous'), ('theorem', 'A.t.returns')])

    def test_removed_label_is_reported_by_source_check(self):
        registry = fs.load_registry()
        del registry['theorems']['Proofs.Floatops.Proofs::op16_spec']
        self.assertIn('Proofs.Floatops.Proofs::op16_spec: numerical theorem lacks a float-semantics label',
                      fs.check_sources(ROOT, registry))
        registry = fs.load_registry()
        registry['theorems']['Proofs.Floats.Proofs::renamed_away'] = IEEE
        self.assertIn('Proofs.Floats.Proofs::renamed_away: registry names no declared theorem',
                      fs.check_sources(ROOT, registry))


class SourceTests(unittest.TestCase):
    """A small synthetic repository: each control changes one fact."""
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        write(self.root / 'zig-patch/versions.toml', (ROOT / 'zig-patch/versions.toml').read_text())
        write(self.root / 'ZigLean/Float/Fixture.lean',
              'namespace Zig\n\ntheorem fmt_fact (fmt : FloatFmt) : fmt = fmt := rfl\n\nend Zig\n')
        write(self.root / 'Proofs/Ex/Proofs.lean',
              'open Ex\n\ntheorem op_spec (x : Zig.F64) : f x = g x := by\n  rfl\n\n'
              'theorem nat_only (n : Nat) : n = n := rfl\n')
        write(self.root / 'tests/review/Check.lean', 'example : (Zig.Float.zero false : Zig.F32).isNaN = false := rfl\n')
        self.registry = {'schema_version': 1, 'non_numerical': {},
                         'theorems': {'ZigLean.Float.Fixture::Zig.fmt_fact': ABSTRACT, 'Proofs.Ex.Proofs::op_spec': IEEE},
                         'checks': {'tests/review/Check.lean': {'labels': ['ieee'], 'correspondence': 'model'}}}

    def tearDown(self):
        self.temporary.cleanup()

    def problems(self, registry=None):
        write(self.root / 'assurance/float-semantics.json', json.dumps(registry or self.registry))
        return fs.check_sources(self.root)

    def test_positive_control(self):
        self.assertEqual(self.problems(), [])

    def test_unlabeled_theorems_fail(self):
        registry = copy.deepcopy(self.registry)
        del registry['theorems']['ZigLean.Float.Fixture::Zig.fmt_fact']
        self.assertEqual(self.problems(registry),
                         ['ZigLean.Float.Fixture::Zig.fmt_fact: numerical theorem lacks a float-semantics label'])
        write(self.root / 'Proofs/Ex/More.lean', 'theorem added (x : Zig.F32) : x = x := rfl\n')
        self.assertEqual(self.problems(), ['Proofs.Ex.More::added: numerical theorem lacks a float-semantics label'])

    def test_mutual_end_keeps_namespace(self):
        write(self.root / 'Proofs/Ex/Mutual.lean', 'namespace Ex\n\nmutual\ndef a : Nat := 0\nend\n\n'
              'theorem after (x : Zig.F32) : x = x := rfl\n\nend Ex\n')
        self.assertEqual(self.problems(), ['Proofs.Ex.Mutual::Ex.after: numerical theorem lacks a float-semantics label'])

    def test_unlisted_or_inconsistent_checks_fail(self):
        write(self.root / 'tests/other/Rt.lean', 'example : Zig.Float.mulRt (1 : Zig.F128) 1 = 1 := by native_decide\n')
        self.assertEqual(len(self.problems()), 1)
        registry = copy.deepcopy(self.registry)
        registry['checks']['tests/other/Rt.lean'] = {'labels': ['ieee'], 'correspondence': 'model'}
        self.assertEqual(self.problems(registry),
                         ['tests/other/Rt.lean: compiler-rt helper used but no compiler-rt label listed'])
        registry['checks']['tests/other/Rt.lean']['labels'] = ['compiler-rt@0.16.0']
        self.assertEqual(self.problems(registry), [])
        registry['checks']['tests/missing/None.lean'] = {'labels': ['ieee'], 'correspondence': 'model'}
        self.assertEqual(self.problems(registry), ['tests/missing/None.lean: listed check has no float example or theorem'])

    def test_aarch64_rule_needs_aarch64_target(self):
        write(self.root / 'Proofs/Ex/A64.lean', 'theorem div_a64 (x : Zig.F80) : Zig.Float.divXf3 x x = Zig.Float.divXf3 x x := rfl\n')
        registry = copy.deepcopy(self.registry)
        registry['theorems']['Proofs.Ex.A64::div_a64'] = dict(IEEE, targets=['x86_64-linux'])
        self.assertEqual(self.problems(registry),
                         ['Proofs.Ex.A64::div_a64: uses an aarch64-only float rule but its label lists no aarch64 target'])
        registry['theorems']['Proofs.Ex.A64::div_a64'] = dict(IEEE, targets=['aarch64-macos'])
        self.assertEqual(self.problems(registry), [])

    def test_compiler_rt_label_needs_compiler_rt_translation(self):
        registry = copy.deepcopy(self.registry)
        registry['theorems']['Proofs.Ex.Proofs::op_spec'] = RT
        self.assertEqual(self.problems(registry),
                         ['Proofs.Ex.Proofs::op_spec: compiler-rt label but the translation selects ieee'])
        write(self.root / 'examples/ex/translate.args', '--float-semantics compiler-rt\n')
        self.assertEqual(self.problems(registry), [])
        header = {'correspondence': 'model', 'float_semantics': 'ieee', 'profile': {}}
        write(self.root / 'Proofs/Ex/Gen.lean', '-- air2lean-profile: ' + json.dumps(header) + '\n')
        self.assertEqual(self.problems(registry),
                         ['Proofs.Ex.Proofs::op_spec: compiler-rt label but the translation selects ieee'])
        header['correspondence'] = 'binary'
        write(self.root / 'Proofs/Ex/Gen.lean', '-- air2lean-profile: ' + json.dumps(header) + '\n')
        with self.assertRaisesRegex(ValueError, 'generated code claims unsupported correspondence'):
            self.problems(registry)

    def test_cli_exit_codes(self):
        write(self.root / 'assurance/float-semantics.json', json.dumps(self.registry))
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(fs.main(['check', '--root', str(self.root)]), 0)
            write(self.root / 'Proofs/Ex/More.lean', 'theorem added (x : Zig.F32) : x = x := rfl\n')
            self.assertEqual(fs.main(['check', '--root', str(self.root)]), 1)
            write(self.root / 'assurance/float-semantics.json', '{}')
            self.assertEqual(fs.main(['check', '--root', str(self.root)]), 2)


class GraphTests(unittest.TestCase):
    """The audit applies labels to the checked declaration graph."""
    def setUp(self):
        self.policy = audit.load_policy(ROOT / 'assurance/policy.json')
        self.registry = fs.load_registry()

    def node(self, name, module, dependencies=(), kind='definition', user_name=None):
        return {'name': name, 'user_name': user_name or name, 'module': module, 'kind': kind,
                'dependencies': list(dependencies), 'unsafe': False}

    def raw(self, theorems, extra=()):
        nodes = [self.node('Zig.Float.add', 'ZigLean.Float.Ops', ['Zig.Float.roundRat']),
                 self.node('Zig.Float.roundRat', 'ZigLean.Float.Round'),
                 self.node('Zig.Float.mulRt', 'ZigLean.Float.CompilerRt', ['Zig.Float.add']),
                 self.node('Zig.Float.divXf3', 'ZigLean.Float.CompilerRt', ['Zig.Float.add']),
                 self.node('Nat.add', 'Init.Prelude'), *extra]
        rows = []
        for name, dependencies in theorems:
            nodes.append(self.node(name, 'Proofs.Fixture', dependencies, kind='theorem'))
            rows.append({'name': name, 'module': 'Proofs.Fixture', 'axioms': []})
        return {'schema_version': 1, 'modules': ['Proofs.Fixture'], 'project_declarations': [],
                'theorems': rows, 'nodes': nodes}

    def labels(self, **entries):
        registry = copy.deepcopy(self.registry)
        registry['theorems'].update({'Proofs.Fixture::' + k: v for k, v in entries.items()})
        return registry

    def report(self, raw, registry):
        # Every project module of the fixture graph passed kernel replay.
        modules = sorted({*raw['modules'], *(n['module'] for n in raw['nodes'] if audit.needs_replay(n['module']))})
        replay = {'schema_version': 1, 'tool': 'leanchecker', 'tool_sha256': '0' * 64, 'lean_sha256': '1' * 64,
                  'toolchain': 'leanprover/lean4:test', 'modules': modules,
                  'modules_sha256': audit.modules_digest(modules), 'reused': [], 'rejected': [], 'status': 'pass'}
        return audit.apply_policy(dict(raw, kernel_replay=replay), self.policy, registry)

    def classes(self, report):
        return sorted((v['name'], v['trust_class']) for v in report['violations'])

    def test_unlabeled_numerical_theorem_fails_and_plain_theorem_passes(self):
        raw = self.raw([('add_spec', ['Zig.Float.add']), ('nat_spec', ['Nat.add'])])
        report = self.report(raw, self.registry)
        self.assertEqual(report['status'], 'fail')
        self.assertEqual(self.classes(report), [('add_spec', 'unlabeled-numerical-theorem')])
        theorems = {t['name']: t for t in report['theorems']}
        self.assertFalse(theorems['add_spec']['allowed'])
        self.assertTrue(theorems['nat_spec']['allowed'])
        self.assertNotIn('float_semantics', theorems['nat_spec'])

    def test_labels_are_recorded_without_binary_claims(self):
        raw = self.raw([('add_spec', ['Zig.Float.add']), ('round_spec', ['Zig.Float.roundRat']),
                        ('mul_spec', ['Zig.Float.mulRt'])])
        report = self.report(raw, self.labels(add_spec=IEEE, round_spec=ABSTRACT, mul_spec=RT))
        self.assertEqual(report['status'], 'pass', report['violations'])
        records = {t['name']: t['float_semantics'] for t in report['theorems']}
        self.assertEqual(records['mul_spec'], {'scope': 'stated', 'label': 'compiler-rt@0.14.1,0.15.2,0.16.0',
                                               'semantics': 'compiler-rt', 'zig_versions': ALL, 'targets': BOTH,
                                               'correspondence': 'model', 'binary_correspondence': 'not_claimed'})
        self.assertEqual(records['add_spec']['label'], 'ieee')
        self.assertEqual(records['round_spec']['label'], 'abstract-spec')
        summary = report['float_semantics']
        self.assertEqual(summary['labels'], {'abstract-spec': 1, 'compiler-rt@0.14.1,0.15.2,0.16.0': 1, 'ieee': 1})
        self.assertEqual((summary['numerical_theorems'], summary['binary_correspondence']), (3, 'not_claimed'))
        self.assertEqual(summary['registry_sha256'], self.registry['sha256'])
        self.assertEqual(fs.report_problems(report, self.labels(add_spec=IEEE, round_spec=ABSTRACT, mul_spec=RT)), [])

    def test_labels_must_match_the_dependency_graph(self):
        cases = [
            ('add_spec', ['Zig.Float.add'], ABSTRACT, 'float-semantics-mismatch'),
            ('add_spec', ['Zig.Float.add'], RT, 'float-semantics-mismatch'),
            ('mul_spec', ['Zig.Float.mulRt'], IEEE, 'float-semantics-mismatch'),
            ('mul_spec', ['Zig.Float.mulRt'], ABSTRACT, 'float-semantics-mismatch'),
            ('nat_spec', ['Nat.add'], IEEE, 'stale-float-semantics-label'),
        ]
        for name, dependencies, entry, trust in cases:
            with self.subTest(name=name, entry=entry):
                report = self.report(self.raw([(name, dependencies)]), self.labels(**{name: entry}))
                self.assertEqual(self.classes(report), [(name, trust)])

    def test_labels_record_targets(self):
        for targets in (['aarch64-macos'], ['x86_64-linux'], BOTH):
            with self.subTest(targets=targets):
                report = self.report(self.raw([('div_spec', ['Zig.Float.divXf3'])]),
                                     self.labels(div_spec=dict(RT, targets=targets)))
                self.assertEqual(report['status'], 'pass', report['violations'])
                record = next(t for t in report['theorems'] if t['name'] == 'div_spec')['float_semantics']
                self.assertEqual(record['targets'], targets)

    def test_stale_and_wrong_exemptions_fail(self):
        registry = self.labels(gone=IEEE)
        report = self.report(self.raw([('nat_spec', ['Nat.add'])]), registry)
        self.assertEqual(self.classes(report), [('Proofs.Fixture::gone', 'stale-float-semantics-label')])
        registry = copy.deepcopy(self.registry)
        registry['non_numerical']['Proofs.Fixture::add_spec'] = 'claimed not numerical'
        report = self.report(self.raw([('add_spec', ['Zig.Float.add'])]), registry)
        self.assertEqual(self.classes(report), [('add_spec', 'float-semantics-mismatch')])
        # Labels of modules outside an explicit audit scope are not stale.
        report = self.report(self.raw([('nat_spec', ['Nat.add'])]), self.registry)
        self.assertEqual(report['status'], 'pass')

    def test_cycles_private_names_and_generated_companions(self):
        extra = [self.node('Fix.a', 'Proofs.Fixture', ['Fix.b']), self.node('Fix.b', 'Proofs.Fixture', ['Fix.a', 'Zig.Float.mulRt'])]
        raw = self.raw([('cyclic', ['Fix.a']), ('cyclic.eq_1', ['Fix.a']), ('Fix._proof_1', ['Zig.Float.add'])], extra)
        theorem = next(n for n in raw['nodes'] if n['name'] == 'cyclic')
        theorem['name'] = raw['theorems'][0]['name'] = '_private.Proofs.Fixture.0.cyclic'
        report = self.report(raw, self.labels(cyclic=RT))
        self.assertEqual(report['status'], 'pass', report['violations'])
        records = {t['name']: t['float_semantics'] for t in report['theorems']}
        self.assertEqual(records['_private.Proofs.Fixture.0.cyclic']['label'], 'compiler-rt@0.14.1,0.15.2,0.16.0')
        self.assertEqual(records['cyclic.eq_1']['scope'], 'compiler-generated')
        self.assertEqual(records['Fix._proof_1']['scope'], 'compiler-generated')
        self.assertEqual(report['float_semantics']['compiler_generated'], 2)
        report = self.report(raw, self.labels(cyclic=IEEE))
        self.assertEqual(self.classes(report), [('_private.Proofs.Fixture.0.cyclic', 'float-semantics-mismatch')])

    def test_report_and_receipt_claims_are_rejected(self):
        registry = self.labels(add_spec=IEEE)
        report = self.report(self.raw([('add_spec', ['Zig.Float.add'])]), registry)
        self.assertEqual(fs.report_problems(report, registry), [])
        tampered = copy.deepcopy(report)
        tampered['theorems'][0]['float_semantics']['binary_correspondence'] = 'claimed'
        problems = fs.report_problems(tampered, registry)
        self.assertTrue(any('unsupported binary/native correspondence claim' in p for p in problems), problems)
        tampered = copy.deepcopy(report)
        tampered['float_semantics']['binary_correspondence'] = 'claimed'
        self.assertTrue(fs.report_problems(tampered, registry))
        tampered = copy.deepcopy(report)
        del tampered['theorems'][0]['float_semantics']
        self.assertTrue(any('differs from the checked graph' in p for p in fs.report_problems(tampered, registry)))
        tampered = copy.deepcopy(report)
        tampered['theorems'][0]['float_semantics']['correspondence'] = 'native'
        self.assertTrue(fs.report_problems(tampered, registry))
        tampered = copy.deepcopy(report)
        del tampered['float_semantics']
        self.assertIn('$.float_semantics: missing float-semantics summary', fs.report_problems(tampered, registry))
        receipt = {'schema': 2, 'native_adequacy': 'not_attested', 'source_correspondence': 'not_attested',
                   'float_semantics': dict(report['float_semantics'], theorems={'add_spec': 'ieee'})}
        self.assertEqual(fs.report_problems(receipt, registry), [])
        for key in ('native_adequacy', 'source_correspondence'):
            with self.subTest(key=key):
                self.assertTrue(fs.report_problems(dict(receipt, **{key: 'attested'}), registry))
        self.assertTrue(fs.report_problems(dict(receipt, binary_correspondence='claimed'), registry))
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stderr(io.StringIO()):
            good, bad = Path(directory, 'good.json'), Path(directory, 'bad.json')
            good.write_text(json.dumps(receipt))
            bad.write_text(json.dumps(dict(receipt, native_adequacy='bit-exact')))
            self.assertEqual(fs.main(['check-report', str(good)]), 0)
            self.assertEqual(fs.main(['check-report', str(good), str(bad)]), 1)


if __name__ == '__main__':
    unittest.main()
