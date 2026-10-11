#!/usr/bin/env python3
"""Portable reference arithmetic and source integration checks; no compiler execution."""
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('coverage_inventory', ROOT / 'scripts/coverage.py')
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)

def index(width, bit):
    return (width // 8 - 1 - bit // 8) * 8 + bit % 8

def swap(value, width):
    return sum(((value >> index(width, bit)) & 1) << bit for bit in range(width))

class PortableTests(unittest.TestCase):
    def test_all_legal_width_index_permutations(self):
        # Every Zig byte-aligned width, including the largest legal width.
        for width in range(0, 65536, 8):
            bits = {0, 1, 7, width // 2, width - 8, width - 1}
            for bit in bits:
                if not 0 <= bit < width:
                    continue
                other = index(width, bit)
                self.assertLess(other, width)
                self.assertGreaterEqual(other, 0)
                self.assertEqual(index(width, other), bit)
                self.assertEqual(other % 8, bit % 8)

    def test_exhaustive_two_byte_reference(self):
        for value in range(65536):
            expected = int.from_bytes(value.to_bytes(2, 'little'), 'big')
            self.assertEqual(swap(value, 16), expected)

    def test_asymmetric_runtime_assertions(self):
        self.assertEqual(swap(0x123456, 24), 0x563412)
        self.assertEqual(swap(0x0123456789abcdeffedcba9876543210, 128), 0x1032547698badcfeefcdab8967452301)
        self.assertEqual(int(f'{0x1234:016b}'[::-1], 2), 11336)

    def test_exporter_ty_op_and_normalizer(self):
        exporter = coverage.tokens((ROOT / 'zig-patch/air-json/json.zig').read_text())
        arms = coverage.switch_arms(coverage.function_body(exporter, 'writeInst'), ['tag'], 1)
        rows = coverage.op_table()['tags']
        for tag in ('byte_swap', 'bit_reverse'):
            self.assertEqual(arms[tag], ['try', 'w', '.', 'writeArgs', '(', '&', '.', '{', 'w', '.', 'data', '(', 'inst', ')', '.', 'ty_op', '.', 'operand', '}', ')'])
            self.assertEqual(rows[tag]['constructor'], 'permuteBits')

    def test_pipeline_operand_routing(self):
        effects = (ROOT / 'Air2Lean/Air/Effects.lean').read_text()
        emitter = (ROOT / 'Air2Lean/Emit.lean').read_text()
        self.assertIn('.countBits _ a | .permuteBits _ a | .not a', effects)
        self.assertIn('.countBits _ a | .permuteBits _ a => #[a]', emitter)
        self.assertIn('.permuteBits o a => some (#[a], fun v => .permuteBits o v[0]!)', emitter)
        self.assertIn('"Zig.byteSwap"', emitter)
        self.assertIn('"Zig.bitReverse"', emitter)

    def test_native_export_inventory(self):
        spec = importlib.util.spec_from_file_location('permutation_exports', Path(__file__).with_name('check_exports.py'))
        exports = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(exports)
        source = Path(__file__).with_name('byte_permutation.zig').read_text()
        self.assertEqual(set(re.findall(r'export fn (\w+)\(', source)), exports.NAMES)
        self.assertEqual(len(exports.NAMES), 30)

if __name__ == '__main__':
    unittest.main()
