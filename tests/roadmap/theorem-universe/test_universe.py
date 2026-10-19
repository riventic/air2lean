#!/usr/bin/env python3
"""Offline regressions for the theorem universe (F2), kernel replay (S1) and freshness (H1).

No Lean, Lake or Zig: Lean and leanchecker are replaced by small scripts. The compiled audit
itself runs in CI (`theorem_universe.py audit`) and in tests/roadmap/architecture-audit/claims.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module  # dataclasses resolve their defining module
    spec.loader.exec_module(module)
    return module


universe = load('theorem_universe', 'theorem_universe.py')
assumptions = load('assumptions', 'assumptions.py')
premises = load('premises', 'premises.py')


class FixtureTests(unittest.TestCase):
    """Path/header selection and mocked compiler dispatch; no repository audit or tool runs."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.config = json.loads((ROOT / 'assurance/premises.json').read_text())
        for directory in ['ZigLean', *self.config['theorem_roots']]:
            (self.root / directory).mkdir(parents=True, exist_ok=True)
        self.write('ZigLean.lean', 'import ZigLean.Basic\n')
        self.write('ZigLean/Basic.lean', 'def basic : Nat := 0\n')
        self.write('Proofs/Present.lean', 'theorem present : True := True.intro\n')
        self.write('assurance/premises.json', json.dumps(self.config))
        self.write('assurance/lean-files.json', json.dumps(dict(
            schema_version=2, description='fixture controls', owners={}, reject={}, contextual={})))
        gates = mock.patch.object(universe, 'GATES', {})
        gates.start()
        self.addCleanup(gates.stop)

    def write(self, rel, source):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        return path

    def selected(self):
        with mock.patch.object(premises, 'load_repository',
                               side_effect=AssertionError('source index controlled eligibility')):
            return universe.universe(self.root)

    def test_every_nonexcluded_path_is_enrolled_without_declaration_recognition(self):
        sources = {'Normal': 'theorem normal : True := True.intro\n',
                   'Public': 'module\npublic theorem public_thm : True := True.intro\n',
                   'Multiline': 'module\npublic\n noncomputable\n theorem multiline : True := True.intro\n',
                   'Custom': 'custom_command_that_can_generate_a_theorem\n',
                   'Data': 'def data : Nat := 0\n'}
        for name, body in sources.items():
            self.write(f'tests/roadmap/new/{name}.lean', body)
        self.write('tests/roadmap/assurance/Excluded.lean', 'theorem excluded : False := by sorry\n')
        _, units = self.selected()
        paths = {unit.file for unit in units}
        self.assertTrue({f'tests/roadmap/new/{name}.lean' for name in sources} <= paths)
        self.assertNotIn('tests/roadmap/assurance/Excluded.lean', paths)
        self.assertEqual(self.config, json.loads((self.root / 'assurance/premises.json').read_text()))

    def test_control_registry_excludes_exact_control_without_a_filename_family_exemption(self):
        control = 'tests/roadmap/new/Control.lean'
        prefix = 'tests/roadmap/new/Control.leanExtra.lean'
        client = 'tests/roadmap/new/Client.lean'
        for file in (control, prefix, client):
            self.write(file, 'theorem checked : True := True.intro\n')
        self.write('assurance/lean-files.json', json.dumps(dict(schema_version=2, description='fixture controls',
            owners={}, reject={control: 'intentional fixture rejection'}, contextual={})))
        _, units = self.selected()
        paths = {unit.file for unit in units}
        self.assertNotIn(control, paths)
        self.assertIn(prefix, paths)
        self.assertIn(client, paths)

    def test_nested_interpolation_never_blocks_compiled_enrollment_or_dispatch(self):
        rel = 'tests/roadmap/new/Nested.lean'
        self.write(rel, 'import ZigLean.Basic\ndef msg : String := s!"{r#"a " b"#}"\n')
        _, units = self.selected()
        self.assertIn(rel, {unit.file for unit in units})
        result = {'status': 'pass', 'exit_code': 0, 'collision': False, 'violations': []}
        with mock.patch.object(universe, 'universe', return_value=([], units)), \
                mock.patch.object(universe, 'compile_all', return_value=[]) as compile_all, \
                mock.patch.object(universe, 'audit_modules', return_value=result) as audit:
            report = universe.audit(self.root / 'out', False, None, None)
        self.assertEqual(report['status'], 'pass')  # Mocked compiler/auditor only.
        self.assertIn(rel, {unit.file for unit in compile_all.call_args.args[0]})
        self.assertTrue(audit.called)

    def test_body_discovery_cannot_bypass_a_reported_compiler_failure(self):
        rel = 'tests/roadmap/new/Broken.lean'
        for body in ('def broken := "unterminated\n',
                     'def msg : String := s!"{(show Nat from by sorry)}"\n'):
            with self.subTest(body=body):
                self.write(rel, 'import ZigLean.Basic\n' + body)
                _, units = self.selected()
                self.assertIn(rel, {unit.file for unit in units})
                with mock.patch.object(universe, 'universe', return_value=([], units)), \
                        mock.patch.object(universe, 'compile_all', return_value=['compiler rejected body']), \
                        mock.patch.object(universe, 'audit_modules') as audit:
                    report = universe.audit(self.root / 'out', False, None, None)
                self.assertEqual(report['status'], 'fail')
                audit.assert_not_called()

    def test_missing_import_and_missing_gate_remain_visible(self):
        rel = 'tests/roadmap/new/Client.lean'
        self.write(rel, 'import Missing.Module\n')
        with self.assertRaisesRegex(ValueError, 'unresolved and not an allowed generated import'):
            self.selected()
        generated = next(iter(self.config['generated_imports']))
        self.write(rel, f'import {generated}\n')
        with self.assertRaisesRegex(ValueError, 'add its auditing gate to GATES'):
            self.selected()

    def test_staged_path_encoding_and_compiled_artifacts_are_injective(self):
        paths = ['tests/roadmap/a-b/Proofs.lean', 'tests/roadmap/a_b/Proofs.lean',
                 'tests/roadmap/a/b/Proofs.lean']
        for rel in paths:
            self.write(rel, 'theorem check : True := True.intro\n')
        units = {u.file: u for u in self.selected()[1]}
        selected = [units[rel] for rel in paths]
        self.assertTrue(all(u.root is None for u in selected))
        self.assertEqual(len({u.module for u in selected}), len(paths))
        self.assertEqual(len({universe.compiled_artifact(self.root / 'out', u) for u in selected}), len(paths))
        for u in selected:
            self.assertIsNotNone(premises.DEPS.MODULE_NAME.fullmatch(u.module))
            encoded = ''.join(part[1:] for part in u.module.split('.')[1:])
            self.assertEqual(bytes.fromhex(encoded).decode('utf-8'), u.file)
        long_name = universe.staged_module('tests/roadmap/' + 'x' * 240 + '.lean')
        self.assertTrue(all(len(part) <= 121 for part in long_name.split('.')))

    def test_imported_supported_module_spelling_is_preserved(self):
        directory = 'tests/roadmap/spelling'
        for name in ("Dep'", 'Dep!', 'Dep?'):
            self.write(f'{directory}/{name}.lean', 'def item : Nat := 0\n')
        self.write(f'{directory}/Client.lean', "import Dep' import Dep! import Dep?\n")
        units = {u.file: u for u in self.selected()[1]}
        for name in ("Dep'", 'Dep!', 'Dep?'):
            u = units[f'{directory}/{name}.lean']
            self.assertEqual((u.module, u.root), (name, directory))
        self.write(f'{directory}/Client.lean', 'import «Dep.x»\n')
        with self.assertRaisesRegex(ValueError, 'unsupported module spelling'):
            self.selected()

    def test_inherited_gate_does_not_silently_cover_an_unregistered_dependent(self):
        source, client = 'tests/roadmap/gated/Source.lean', 'tests/roadmap/gated/Client.lean'
        gate = 'tests/roadmap/gated/check.sh'
        generated = next(iter(self.config['generated_imports']))
        self.write(source, f'import {generated}\n')
        self.write(client, 'import Source\n')
        self.write(gate, '# fixture only: theorem_universe.py gate\n')
        with mock.patch.object(universe, 'GATES', {source: gate}):
            with self.assertRaisesRegex(ValueError, 'inherited gate') as failure:
                self.selected()
            for context in (source, client, gate, 'audit coverage', 'no registered auditing gate'):
                self.assertIn(context, str(failure.exception))
        # Only explicit per-file gate registration supplies the existing coverage contract.
        with mock.patch.object(universe, 'GATES', {source: gate, client: gate}):
            units = {u.file: u for u in self.selected()[1]}
            self.assertEqual({u.file: u.gate for u in units.values() if u.gate}, {source: gate, client: gate})

    def test_tracked_nonexcluded_hidden_path_is_enrolled(self):
        rel = 'tests/roadmap/.hidden/Check.lean'
        self.write(rel, 'public theorem hidden_root : True := True.intro\n')
        subprocess.run(['git', 'init', '-q'], cwd=self.root, check=True, capture_output=True)
        subprocess.run(['git', 'add', rel], cwd=self.root, check=True, capture_output=True)
        tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', rel], cwd=self.root,
                                 check=True, capture_output=True, text=True)
        self.assertEqual(tracked.stdout.strip(), rel)
        self.assertFalse(premises.is_excluded(self.config, rel))
        self.assertIn(rel, {u.file for u in self.selected()[1]})
        self.assertNotIn(self.root / rel, list(premises.lean_files(self.root / 'tests/roadmap')))

    def test_artifact_collision_stops_before_writes_or_build_dispatch(self):
        units = [universe.Unit('a.lean', None, 'Universe.A', (), (), None),
                 universe.Unit('b.lean', None, 'Universe.A', (), (), None)]
        output = self.root / 'not-created'
        by_file = {u.file: u for u in units}
        with mock.patch.object(universe, 'staged') as staged, \
                mock.patch.object(universe, 'compile_unit') as compile_unit:
            with self.assertRaisesRegex(ValueError, 'compiled artifact collision'):
                universe.compile_all(units, by_file, output)
            staged.assert_not_called()
            compile_unit.assert_not_called()
        with mock.patch.object(universe, 'universe', return_value=([], units)), \
                mock.patch.object(universe, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'compiled artifact collision'):
                universe.audit(output, True, None, None)
            run.assert_not_called()
            with self.assertRaisesRegex(ValueError, 'compiled artifact collision'):
                universe.compile_witness_fixtures(list(by_file), output, True)
            run.assert_not_called()
        self.assertFalse(output.exists())
        # The guard also catches a collision in the existing library-directory fingerprint.
        distinct_roots = [universe.Unit('a/Main.lean', 'a', 'Main', (), (), None),
                          universe.Unit('b/Main.lean', 'b', 'Main', (), (), None)]
        with mock.patch.object(universe, 'lib_of', return_value=output / 'same-library'):
            with self.assertRaisesRegex(ValueError, 'compiled artifact collision'):
                universe.check_artifact_identities(distinct_roots, output)

    def test_bundles_preserve_module_library_separation_without_source_names(self):
        units = [universe.Unit('a/Main.lean', 'a', 'Main', (), (), None),
                 universe.Unit('a/Solution.lean', 'a', 'Solution', (), (), None),
                 universe.Unit('b/Main.lean', 'b', 'Main', (), (), None),
                 universe.Unit('c/X.lean', 'c', 'X', (), (), None)]
        by_file = {u.file: u for u in units}
        bundles = universe.bundles(units, by_file, self.root / 'out')
        for bundle in bundles:
            self.assertFalse({'a/Main.lean', 'b/Main.lean'} <= {u.file for u in bundle})
        self.assertTrue(any({'a/Main.lean', 'a/Solution.lean'} <= {u.file for u in bundle} for bundle in bundles))
        self.assertEqual(sorted(u.file for bundle in bundles for u in bundle), sorted(by_file))
        with mock.patch.object(universe, 'universe', return_value=([], units)), \
                mock.patch('builtins.print') as printed:
            self.assertEqual(universe.main(['list']), 0)
        self.assertTrue(all('names' not in u for u in json.loads(printed.call_args.args[0])['units']))

    def test_auditor_forwards_supported_module_names_exactly(self):
        modules = ["Dep'", "Ns.Dep!", "Ns.Dep?"]
        output = self.root / 'audit.json'

        def run(command, env):
            self.assertEqual(command, [sys.executable, '-B', str(universe.ROOT / 'scripts/assumptions.py'),
                                       '--no-build', '--allow-no-theorems', '--output', str(output),
                                       '--module', "Dep'", '--module', 'Ns.Dep!', '--module', 'Ns.Dep?'])
            self.assertEqual(env['LEAN_PATH'], str(self.root / 'lib'))
            output.write_text(json.dumps({'status': 'pass', 'modules': modules, 'theorem_count': 3}))
            return subprocess.CompletedProcess(command, 0, '')

        with mock.patch.object(universe, 'run', side_effect=run) as runner:
            result = universe.audit_modules(modules, [self.root / 'lib'], output)
        runner.assert_called_once()
        self.assertEqual(result['modules'], modules)
        self.assertEqual(json.loads(output.read_text())['modules'], modules)
        self.assertEqual((result['status'], result['exit_code'], result['theorem_count']), ('pass', 0, 3))

    def test_compiled_declaration_collision_still_splits_the_bundle(self):
        units = [universe.Unit('a.lean', '.', 'A', (), (), None),
                 universe.Unit('b.lean', '.', 'B', (), (), None)]

        def audited(modules, *args):
            collision = len(modules) > 1
            return {'status': 'fail' if collision else 'pass', 'exit_code': int(collision),
                    'collision': collision, 'violations': ['declaration collision'] if collision else []}

        with mock.patch.object(universe, 'universe', return_value=([], units)), \
                mock.patch.object(universe, 'compile_all', return_value=[]), \
                mock.patch.object(universe, 'audit_modules', side_effect=audited) as audit:
            report = universe.audit(self.root / 'out', False, None, None)
        self.assertEqual(report['status'], 'pass')
        self.assertEqual([run['status'] for run in report['audits']], ['split', 'pass', 'pass'])
        self.assertEqual([call.args[0] for call in audit.call_args_list], [['A', 'B'], ['A'], ['B']])


class UniverseTests(unittest.TestCase):
    def test_every_indexed_theorem_file_is_audited(self):
        shipped, units = universe.universe()
        self.assertEqual(shipped, assumptions.shipped_modules())
        config = premises.load_config(ROOT / premises.CONFIG)
        indexed = {f.rel for f in premises.theorem_files(premises.load_repository(ROOT, config))}
        audited = {u.file for u in units} | {m.replace('.', '/') + '.lean' for m in shipped}
        self.assertEqual(indexed - audited, set())
        self.assertTrue({'tutorials/first-proof/Main.lean', 'tests/roadmap/vcs/Result.lean',
                         'case-studies/flow-time/FlowTime/Proofs.lean'} <= audited)
        gated = {u.file: u.gate for u in units if u.gate}
        self.assertEqual(gated, universe.GATES)

    def test_witness_fixtures_are_registered_universe_files(self):
        # The shipped audit loads them (assurance/witness-fixtures.json): ungated universe units.
        files = assumptions.witness_fixtures()
        self.assertIn('tests/roadmap/lists-fba/ListsFba/Witness.lean', files)
        units = {u.file: u for u in universe.universe()[1]}
        for rel in files:
            self.assertIsNone(units[rel].gate, rel)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'assurance').mkdir()
            for entries, error in (([{'file': 'Proofs/X.lean', 'reason': 'r'}], 'not a test source'),
                                   ([{'file': 'tests/missing.lean', 'reason': 'r'}], 'not a test source'),
                                   ([{'file': 'tests/a.lean'}], 'file, reason')):
                (root / 'assurance/witness-fixtures.json').write_text(
                    json.dumps({'description': 'd', 'fixtures': entries}))
                with self.assertRaisesRegex(ValueError, error):
                    assumptions.witness_fixtures(root)

    def test_witness_theorems_leave_the_audit_scope(self):
        report = {'modules': ['A', 'W'], 'theorem_count': 2,
                  'theorems': [{'name': 'a', 'module': 'A'}, {'name': 'a.nonvacuous', 'module': 'W'}]}
        assumptions.split_witnesses(report, ['A'], ['W'])
        self.assertEqual((report['modules'], report['witness_modules'], report['theorem_count']), (['A'], ['W'], 1))
        self.assertEqual([t['name'] for t in report['witness_theorems']], ['a.nonvacuous'])

    def test_reserved_or_invalid_module_names_are_staged(self):
        units = {u.file: u for u in universe.universe()[1]}
        for rel in ('tests/roadmap/dispatch/Proofs.lean', 'tests/roadmap/local-parent/Proofs.lean'):
            self.assertIsNone(units[rel].root)
            self.assertTrue(units[rel].module.startswith('Universe.'))
        self.assertEqual(units['tests/roadmap/idle-loops/IdleLoop/Gen.lean'].module, 'IdleLoop.Gen')

    def test_scan_rejects_kernel_bypass_and_placeholders(self):
        source = ('-- sorry in a comment is fine\n/- set_option debug.skipKernelTC true -/\n'
                  'theorem a : True := by sorry\nset_option debug.skipKernelTC true in\n'
                  'run_cmd withOptions (·.setBool `debug.skipKernelTC true) (pure ())\n'
                  'unsafe def b := 0\n@[extern "c"] opaque c : Nat\n')
        errors, tokens = universe.scan_source('X.lean', source)
        self.assertEqual(errors, ['X.lean:3: sorry', 'X.lean:4: kernel-check bypass (set_option debug.)',
                                  'X.lean:5: kernel-check bypass (debug.skipKernelTC)'])
        self.assertEqual(tokens, {'unsafe': 1, '@[extern': 1})
        self.assertEqual(universe.scan(), [])

    def test_compile_rejects_sorry_warnings(self):
        # `lean` exits 0 on `declaration uses 'sorry'`, and examples never reach the olean.
        outputs = iter([(0, "X.lean:1:0: warning: declaration uses 'sorry'\n"), (0, ''), (1, 'error')])
        original = universe.run
        universe.run = lambda *a, **k: subprocess.CompletedProcess(a, *next(outputs))
        try:
            with tempfile.TemporaryDirectory() as temp:
                base = Path(temp)
                compile_once = lambda: universe.compile_unit('X.lean', '.', base / 'X.olean', [], base / 'x.log')
                self.assertIn("declaration uses 'sorry'", compile_once() or '')
                self.assertIsNone(compile_once())
                self.assertIn('exited 1', compile_once())
        finally:
            universe.run = original


class ReplayTests(unittest.TestCase):
    """assumptions.kernel_replay against a stand-in leanchecker that rejects module `Bad`."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.toolchain = Path(self.temp.name)
        (self.toolchain / 'bin').mkdir()
        self.calls = self.toolchain / 'calls'
        checker = self.toolchain / 'bin/leanchecker'
        checker.write_text(f'#!/bin/sh\necho "$1" >> {self.calls}\n[ "$1" != Bad ] || {{ echo rejected; exit 1; }}\n')
        checker.chmod(0o755)
        (self.toolchain / 'bin/lean').write_text('lean')

    def checked(self):
        return sorted(self.calls.read_text().split()) if self.calls.exists() else []

    def test_rejection_is_recorded_and_fails(self):
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g'}, self.toolchain, '')
        self.assertEqual((record['status'], [r['module'] for r in record['rejected']]), ('fail', ['Bad']))
        self.assertEqual(assumptions.replay_record(record), ({'Bad', 'Good'}, {'Bad'}))

    def test_cache_reuses_only_identical_passed_lake_oleans(self):
        cache, lake = self.toolchain / 'cache.json', frozenset({'Bad', 'Good', 'Other'})
        assumptions.kernel_replay({'Bad': 'b', 'Good': 'g', 'Other': 'o', 'Local': 'l'}, self.toolchain, '', cache, lake)
        self.calls.unlink()
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g', 'Local': 'l', 'New': 'n'},
                                           self.toolchain, '', cache, lake)
        # Rejected and non-Lake modules (test roots reuse names such as `Main`) are re-checked.
        self.assertEqual((record['reused'], self.checked()), (['Good'], ['Bad', 'Local', 'New']))
        self.calls.unlink()
        record = assumptions.kernel_replay({'Good': 'g', 'Other': 'changed'}, self.toolchain, '', cache, lake)
        self.assertEqual((record['reused'], self.checked()), ([], ['Good', 'Other']))


class FreshnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.olean = Path(self.temp.name) / 'M.olean'
        self.olean.write_bytes(b'olean')
        self.report = {'freshness': {
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'artifacts': [{'module': 'M', 'olean': str(self.olean), 'olean_sha256': assumptions.file_sha256(self.olean),
                           'source': None, 'source_sha256': None}]}}

    def test_changed_artifact_or_revision_is_stale(self):
        self.assertEqual(assumptions.verify_fresh(self.report, allow_dirty=True)['artifacts'], 1)
        self.olean.write_bytes(b'other')
        with self.assertRaisesRegex(ValueError, 'stale'):
            assumptions.verify_fresh(self.report, allow_dirty=True)
        self.report['freshness']['revision'] = {'head': '0' * 40, 'tracked_dirty': False}
        with self.assertRaisesRegex(ValueError, 'revision'):
            assumptions.verify_fresh(self.report, allow_dirty=True)

    def test_dirty_report_needs_permission(self):
        self.report['freshness']['revision']['tracked_dirty'] = True
        with self.assertRaisesRegex(ValueError, 'allow-dirty'):
            assumptions.verify_fresh(self.report)
        self.assertTrue(assumptions.verify_fresh(self.report, allow_dirty=True)['dirty_allowed'])


if __name__ == '__main__':
    unittest.main()
