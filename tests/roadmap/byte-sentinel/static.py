#!/usr/bin/env python3
"""Offline gate/anchor checks; invokes no compiler."""
import importlib.util
from pathlib import Path
import unittest
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
spec = importlib.util.spec_from_file_location('mutations', HERE / 'mutations.py')
mutations = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mutations)
class Static(unittest.TestCase):
    def test_runtime_mutations(self):
        source = mutations.runtime_definition((ROOT / 'ZigLean/Mem/Alloc.lean').read_text())
        for name in mutations.MUTANTS:
            self.assertNotEqual(source, mutations.mutated(source, name))
            with self.assertRaises(ValueError): mutations.mutated('', name)
    def test_mutant_template_preserves_claims_and_kernel_reduction(self):
        baseline = (HERE / 'Check.lean').read_text()
        definition = mutations.runtime_definition((ROOT / 'ZigLean/Mem/Alloc.lean').read_text())
        for name in mutations.MUTANTS:
            source = mutations.mutant_fixture(baseline, definition, name)
            self.assertEqual(source.count(mutations.MUTANT_PROOF), 5)
            self.assertNotIn('+kernel +kernel', source)
            self.assertNotIn('by decide', source)
            expected = baseline.replace('Allocator.allocSentinel', 'Allocator.mutantSentinel')
            expected = expected.replace('by decide +kernel', 'by decide')
            actual = source.replace(mutations.MUTANT_PROOF, 'by decide')
            insertion = 'namespace Zig\n' + mutations.mutated(definition, name) + '\nend Zig\n'
            self.assertEqual(actual.replace(insertion, '', 1), expected)
    def test_source_gate_requires_fresh_metadata(self):
        source = (HERE / 'check.sh').read_text()
        self.assertIn("p.get('sentinel_byte') == sentinel", source)
        self.assertIn('diff -u "$work/native.txt" "$work/lean.txt"', source)
        self.assertIn('lake build air2lean ZigLean ZigLean.Sep.Sentinel', source)
        self.assertIn('overflow-before-allocation', source)
    def test_classifier_rejects_mixed_false_and_heartbeat(self):
        false = "mutant.lean:37:45: error: Tactic `decide` proved that the proposition\n  good = true\nis false\n"
        heartbeat = "mutant.lean:99:1: error: (deterministic) timeout at `whnf`, maximum number of heartbeats reached\n"
        self.assertTrue(mutations.is_semantic_rejection(1, false))
        for output in (false + heartbeat, heartbeat + false):
            self.assertFalse(mutations.is_semantic_rejection(1, output))
        for status in (0, 2, -9, 137):
            self.assertFalse(mutations.is_semantic_rejection(status, false))
    def test_standalone_mutant_driver_owns_single_baseline(self):
        gate = (HERE / "check.sh").read_text()
        driver = (HERE / "mutations.py").read_text()
        self.assertNotIn("lake env lean tests/roadmap/byte-sentinel/Check.lean", gate)
        self.assertEqual(driver.count("subprocess.run(['lake', 'env', 'lean', str(baseline)]"), 1)
    def test_optional_work_retention_matches_existing_gate(self):
        source = (HERE / "check.sh").read_text()
        self.assertIn('case "${AIR2LEAN_SENTINEL_KEEP_WORK:-0}" in', source)
        self.assertIn("0) trap 'rm -rf \"$work\"' EXIT", source)
        self.assertIn('retained fresh byte sentinel artifacts: $work', source)
        self.assertIn('AIR2LEAN_SENTINEL_KEEP_WORK must be 0 or 1', source)
    def test_kernel_checks_have_no_native_escape(self):
        source = (HERE / 'Check.lean').read_text()
        self.assertNotIn('by native_decide', source)
        self.assertIn('blk.bytes != #[.undef, .undef, .undef, .int 42]', source)
        self.assertIn('Allocator.free {} 1 s', source)
if __name__ == '__main__': unittest.main()
