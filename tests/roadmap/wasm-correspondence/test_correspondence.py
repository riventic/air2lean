#!/usr/bin/env python3
"""T05: the native/wasm32 relation checker passes on the committed records and fails closed on
unclassified exports, changed observations, stale records, out-of-tolerance floats, wrong
profile models and relabeled theorems. Runs no compiler."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('wasm_correspondence', ROOT / 'scripts/wasm-correspondence.py')
wc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wc)


class Relation(unittest.TestCase):
    def setUp(self):
        self.relation = wc.load_relation()
        self.tmp = Path(tempfile.mkdtemp(prefix='air2lean-t05-test-'))
        self.records = self.tmp / 'records'
        shutil.copytree(wc.RECORDS, self.records)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def check(self, relation=None):
        return wc.check(relation or self.relation, ROOT, self.records)[0]

    def edit(self, version, target, change):
        path = self.records / version / f'{target}.json'
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def test_committed_records_hold(self):
        errors, summary = wc.check(self.relation, ROOT, self.records)
        self.assertEqual(errors, [])
        self.assertTrue(all(counts['exact'] and counts['tolerated'] and counts['target-specific']
                            for counts in summary.values()))
        self.assertIn('0.17.0 x86_64-linux/wasm32-freestanding', summary)

    def test_unclassified_export_fails(self):
        relation = copy.deepcopy(self.relation)
        del relation['kernels']['int_mix']
        self.assertTrue(any('int_mix has no relation entry' in e for e in self.check(relation)))

    def test_unknown_class_fails(self):
        relation = copy.deepcopy(self.relation)
        relation['kernels']['int_mix']['class'] = 'close-enough'
        self.assertTrue(any('unknown class' in e for e in self.check(relation)))

    def test_changed_exact_observation_fails(self):
        self.edit('0.17.0', 'wasm32-freestanding',
                  lambda d: d['results']['des_time_add64'].__setitem__(0, 12345))
        self.assertTrue(any('des_time_add64' in e and 'exact' in e for e in self.check()))

    def test_trap_against_value_fails(self):
        self.edit('0.17.0', 'x86_64-linux', lambda d: d['results']['int_mix'].__setitem__(3, 'trap'))
        self.assertTrue(any('int_mix' in e for e in self.check()))

    def test_stale_record_fails(self):
        self.edit('0.16.0', 'aarch64-macos',
                  lambda d: d['sources_sha256'].__setitem__(self.relation['source'], '0' * 64))
        self.assertTrue(any('stale record' in e for e in self.check()))

    def test_missing_record_fails(self):
        (self.records / '0.17.0/x86_64-linux.json').unlink()
        self.assertTrue(any('missing record' in e for e in self.check()))

    def test_target_specific_model_is_per_profile(self):
        # The wasm32 observation of the native width is refused: each side meets its own model.
        native = json.loads((self.records / '0.17.0/x86_64-linux.json').read_text())
        self.edit('0.17.0', 'wasm32-freestanding',
                  lambda d: d['results'].__setitem__('usize_bits', native['results']['usize_bits']))
        self.assertTrue(any('usize_bits' in e and 'bits 32' in e for e in self.check()))

    def test_float_tolerance(self):
        f64 = {'class': 'tolerated', 'format': 'f64', 'ulp': 1}
        one = 0x3FF0000000000000
        self.assertIsNone(wc.relate(f64, [], 0x7FF8000000000000, 0xFFF8000000000001, {}))  # NaN class
        self.assertIsNone(wc.relate(f64, [], one, one + 1, {}))
        self.assertIn('2 ulp', wc.relate(f64, [], one, one + 2, {}))
        self.assertIn('only one side is NaN', wc.relate(f64, [], 0x7FF8000000000000, one, {}))
        self.assertIsNone(wc.relate(f64, [], 0, 1 << 63, {}))  # +0 and -0 are one ulp apart
        self.assertIsNotNone(wc.relate({**f64, 'ulp': 0}, [], 0, 1 << 63, {}))

    def test_f32_high_bits_are_observed(self):
        f32 = {'class': 'tolerated', 'format': 'f32', 'ulp': 0}
        self.assertIsNone(wc.relate(f32, [], 0x3F800000, 0x3F800000, {}))
        self.assertIn('above bit 31', wc.relate(f32, [], 0x3F800000, 0xDEADBEEF3F800000, {}))

    def test_expect_sees_the_record_version(self):
        entry = {'class': 'target-specific', 'expect': 'TRAP if zig < 15 else a'}
        bits = {'native': 64, 'wasm32': 32}
        self.assertIsNone(wc.relate(entry, [5], 'trap', 'trap', bits, 14))
        self.assertIsNotNone(wc.relate(entry, [5], 'trap', 'trap', bits, 17))

    def test_mislabelled_record_is_not_compared(self):
        self.edit('0.16.0', 'x86_64-linux', lambda d: d.__setitem__('zig_version', '0.17.0'))
        errors, summary = wc.check(self.relation, ROOT, self.records)
        self.assertTrue(any('records Zig 0.17.0' in e for e in errors))
        self.assertNotIn('0.16.0 x86_64-linux/wasm32-freestanding', summary)

    def test_illegal_cases_are_not_compared(self):
        entry = self.relation['kernels']['f64_to_i64']
        self.assertTrue(wc.illegal(entry, [0x7FF8000000000000], 17))
        self.assertFalse(wc.illegal(entry, [0x43E0000000000000], 17))  # 2^63: checked from 0.15.2
        self.assertTrue(wc.illegal(entry, [0x43E0000000000000], 14))
        self.assertFalse(wc.illegal(entry, [0xC3E0000000000000], 14))  # minInt(i64) fits

    def test_expect_language_is_closed(self):
        with self.assertRaises(ValueError):
            wc.evaluate("__import__('os').getpid()", wc.expect_env([], 32))
        self.assertEqual(wc.evaluate('NONE if a >= 2 ** bits else a', wc.expect_env([2 ** 32], 32)), wc.MASK64)

    def test_relabeled_native_theorem_fails(self):
        relation = copy.deepcopy(self.relation)
        relation['claims'][0] = {**relation['claims'][0], 'theorem': 'PointerWidth.Proofs.byteCount_x64'}
        errors = self.check(relation)
        self.assertTrue(any('never relabeled' in e and 'x86_64-linux' in e for e in errors), errors)

    def test_claim_about_x86_case_study_is_not_a_wasm_claim(self):
        relation = copy.deepcopy(self.relation)
        relation['claims'].append({'kernel': 'des_time_add32', 'target': 'wasm32-freestanding',
                                   'theorem': 'FlowTime.timestamp32_exact',
                                   'file': 'case-studies/flow-time/FlowTime/Proofs.lean'})
        self.assertTrue(any('des_time_add32' in e for e in self.check(relation)))

    def test_mixed_target_theorem_fails(self):
        relation = copy.deepcopy(self.relation)
        relation['claims'][0] = {**relation['claims'][0], 'theorem': 'PointerWidth.Proofs.byteCount_boundary'}
        self.assertTrue(any('never relabeled' in e for e in self.check(relation)))


if __name__ == '__main__':
    unittest.main()
