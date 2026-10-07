#!/usr/bin/env python3
"""V03 trust report regressions: committed report current, and each invalid table rejected."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('trust_report', ROOT / 'scripts/trust-report.py')
t = importlib.util.module_from_spec(spec)
spec.loader.exec_module(t)
DATA = json.loads((ROOT / t.STAGES).read_text(encoding='utf-8'))


def stage(data, sid):
    return next(s for s in data['stages'] if s['id'] == sid)


class TrustReport(unittest.TestCase):
    def problems(self, change):
        data = copy.deepcopy(DATA)
        change(data)
        return t.validate(data)

    def assertProblem(self, change, needle):
        problems = self.problems(change)
        self.assertTrue(any(needle in p for p in problems), f'{needle!r} not in {problems}')

    def test_committed_table_is_valid_and_report_current(self):
        self.assertEqual(t.validate(DATA), [])
        self.assertEqual((ROOT / t.REPORT).read_text(encoding='utf-8'), t.render(DATA))

    def test_every_class_is_used(self):
        self.assertEqual({s['class'] for s in DATA['stages']}, set(t.CLASSES))

    def test_missing_required_stage(self):
        self.assertProblem(lambda d: d['stages'].remove(stage(d, 'native-backend')),
                           "'native-backend': required pipeline stage is missing")

    def test_unknown_or_missing_class(self):
        self.assertProblem(lambda d: stage(d, 'sema').update({'class': 'proved'}), "class 'proved'")
        self.assertProblem(lambda d: stage(d, 'sema').pop('class'), 'class None')

    def test_undefined_premise(self):
        self.assertProblem(lambda d: stage(d, 'emitter').update(premises=['TRU-99']),
                           'premise TRU-99 is not defined')
        self.assertProblem(lambda d: stage(d, 'emitter').update(premises=[]), 'cites no premise')

    def test_uncited_trust_premise(self):
        def change(d):
            for s in d['stages']:
                s['premises'] = [p for p in s['premises'] if p != 'TRU-03']
        self.assertProblem(change, 'TRU-03: compiler/tool trust premise is cited by no stage')

    def test_checked_classes_need_checks(self):
        self.assertProblem(lambda d: stage(d, 'exporter').pop('checks'), 'cites no checker and test')
        self.assertProblem(lambda d: stage(d, 'theorems').pop('checks'), 'cites no checker and test')

    def test_kernel_checked_needs_trusted_base(self):
        self.assertProblem(lambda d: stage(d, 'theorems').update(premises=['TRU-04']),
                           'must cite its trusted base TRU-01')

    def test_unverified_stage_cannot_list_checks(self):
        def change(d):
            stage(d, 'sema')['checks'] = copy.deepcopy(stage(d, 'exporter')['checks'])
        self.assertProblem(change, 'unverified-assumption stage lists checks')

    def test_missing_checker_test_or_component(self):
        self.assertProblem(lambda d: stage(d, 'exporter')['checks'][0].update(checker='scripts/nope.py'),
                           "missing file 'scripts/nope.py'")
        self.assertProblem(lambda d: stage(d, 'exporter')['checks'][0].update(test='tests/nope.py'),
                           "missing file 'tests/nope.py'")
        self.assertProblem(lambda d: stage(d, 'decode')['components'].append('Air2Lean/Nope.lean'),
                           "missing file 'Air2Lean/Nope.lean'")
        # Citations must stay inside the checkout.
        self.assertProblem(lambda d: stage(d, 'decode')['components'].append(str(ROOT / 'lean-toolchain')),
                           'missing file')
        self.assertProblem(lambda d: stage(d, 'decode')['components'].append('scripts/../lean-toolchain'),
                           "missing file 'scripts/../lean-toolchain'")

    def test_check_must_run_in_ci(self):
        self.assertProblem(lambda d: stage(d, 'exporter')['checks'][0].update(ci=['python3 never-run.py']),
                           "CI command 'python3 never-run.py' is not in")
        # A test that exists but no CI command (or script it names) runs.
        self.assertProblem(lambda d: stage(d, 'provenance')['checks'][0].update(
            test='tests/roadmap/byte-permutation/test_portable.py'), 'test_portable.py is not run by CI')

    def test_test_reached_through_ci_script(self):
        # check-export-names.sh is named by CI and runs test_order_cli.py.
        check = stage(DATA, 'exporter')['checks'][2]
        ci = (ROOT / t.CI).read_text(encoding='utf-8')
        self.assertNotIn(check['test'], ci)
        self.assertTrue(t.runs_in_ci(check['test'], ci, check['ci'], ROOT))

    def test_check_mode_detects_stale_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for entry in ROOT.iterdir():
                if entry.name not in ('docs', '.git'):
                    os.symlink(entry, root / entry.name)
            (root / 'docs').mkdir()
            for entry in (ROOT / 'docs').iterdir():
                if entry.name != 'trust-report.md':
                    os.symlink(entry, root / 'docs' / entry.name)
            self.assertEqual(t.main(['check'], root=root), 1)
            self.assertEqual(t.main(['write'], root=root), 0)
            self.assertEqual(t.main(['check'], root=root), 0)
            report = root / t.REPORT
            report.write_text(report.read_text(encoding='utf-8') + 'edit\n', encoding='utf-8')
            self.assertEqual(t.main(['check'], root=root), 1)


if __name__ == '__main__':
    unittest.main()
