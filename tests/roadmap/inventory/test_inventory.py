"""Offline synthetic compiler regression tests; no Zig or Lean process."""
import importlib.util
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('coverage_inventory', ROOT/'scripts/coverage.py')
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)


class InventoryTests(unittest.TestCase):
    def test_nested_comments_strings_and_methods(self):
        source = '''pub const Tag = enum(u8) {
          // fake_tag,
          add, @"return", special = nested(1, .{2, 3}),
          pub const Nested = struct { invented: u8, };
          pub fn method(x: Tag) void { const s = "not,a,tag"; }
        };'''
        self.assertEqual(coverage.members(source, 'Tag', 'enum'), ['add', 'return', 'special'])

    def test_union_payloads_and_wildcard(self):
        source = 'const Key = union(enum) { int: Int, @"extern": Extern, nested: struct { a: u8, b: u16 }, };'
        self.assertEqual(coverage.members(source, 'Key', 'union'), ['int', 'extern', 'nested'])
        self.assertEqual(coverage.members('const Tag = enum { a, _, };', 'Tag', 'enum'), ['a'])

    def test_fail_closed(self):
        for source in ('const Tag = enum { a b, };', 'const Tag = enum { a, a, };',
                       'const Tag = enum { a };', 'const Tag = enum { a, '):
            with self.assertRaises(ValueError): coverage.members(source, 'Tag', 'enum')
        with self.assertRaises(ValueError):
            coverage.members('const Tag = enum { a, }; const Tag = enum { b, };', 'Tag', 'enum')

    def test_switch_scopes(self):
        body = coverage.function_body('fn writeInst() void { switch (tag) { .a => {}, else => {}, } switch (tag) { .a, .b => { switch (x) { .fake => {}, } }, else => if (v14) { field("unsupported"); } else {}, } }', 'writeInst')
        arms = coverage.switch_arms(body, ['tag'], 1)
        self.assertEqual(set(arms), {'a', 'b', '*'})
        self.assertNotIn('fake', arms)
        self.assertIn('"unsupported"', arms['*'])

    def test_complete_synthetic_source_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)
            for relative, data in {
                'src/Air.zig': 'pub const Inst = struct { pub const Tag = enum(u8) { add, new_tag, }; };',
                'lib/std/builtin.zig': 'pub const Type = union(enum) { int: Int, @"struct": Struct, };',
                'src/InternPool.zig': 'pub const Key = union(enum) { int_type: IntType, int: Int, pub const Ptr = struct { pub const BaseAddr = union(enum) { nav: Nav, int: u64, }; }; };',
            }.items():
                path = source/relative; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(data)
            universe, fingerprints = coverage.compiler_inventory(source)
            self.assertEqual(universe['air_tags'], ['add', 'new_tag'])
            self.assertEqual(universe['types'], ['int', 'struct'])
            self.assertEqual(universe['intern_keys'], ['int_type', 'int'])
            self.assertEqual(universe['pointer_bases'], ['nav', 'int'])
            self.assertEqual(len(fingerprints), 11)
            self.assertIsNone(fingerprints['lib/std/Io.zig'])
            report = coverage.generate('synthetic-no-goldens', source)
            self.assertEqual(len(report['tags']), 2)
            new = next(row for row in report['tags'] if row['tag'] == 'new_tag')
            self.assertEqual(new['exporter']['status'], 'fallback-unclassified')
            self.assertEqual(new['tests']['paths'], [])
            self.assertNotIn('supported', new['disposition'])
            self.assertTrue(all(row['proofs']['status'] == 'symbol-index-only-not-proof-coverage' for row in report['tags']))
            snapshot = source/'inventory.json'
            command = [sys.executable, str(ROOT/'scripts/coverage.py')]
            arguments = ['--version', 'synthetic-no-goldens', '--source', str(source), '--inventory', str(snapshot)]
            generated = subprocess.run(command + ['generate'] + arguments, capture_output=True, text=True)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            checked = subprocess.run(command + ['check'] + arguments, capture_output=True, text=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            # A renamed AIR tag and payload-only changes both fail the fingerprint gate.
            (source/'src/Air.zig').write_text('pub const Tag = enum(u8) { add, renamed_tag, };')
            upgraded = coverage.generate('synthetic-next', source)
            delta = coverage.changes(report, upgraded)
            self.assertEqual(delta['universes']['air_tags']['added'], ['renamed_tag'])
            self.assertEqual(delta['universes']['air_tags']['removed'], ['new_tag'])
            self.assertTrue(delta['compiler_sources_changed'])
            stale = subprocess.run(command + ['check'] + arguments, capture_output=True, text=True)
            self.assertEqual(stale.returncode, 1, stale.stderr)
            self.assertIn('renamed_tag', stale.stdout)
            self.assertIn('Inventory stale', stale.stderr)
            missing = subprocess.run(command + ['check', '--version', 'synthetic', '--source', str(source/'missing'), '--inventory', str(snapshot)], capture_output=True, text=True)
            self.assertEqual(missing.returncode, 2, missing.stderr)
            old_fingerprint = fingerprints['src/InternPool.zig']
            with (source/'src/InternPool.zig').open('a') as f: f.write('\n// changed layout assumption\n')
            _, new_fingerprints = coverage.compiler_inventory(source)
            self.assertNotEqual(old_fingerprint, new_fingerprints['src/InternPool.zig'])

    def test_normalizer_branch_does_not_capture_fallback(self):
        sample = '\n  match raw.tag with\n  | "add" | "add_safe" => return .arith .add\n  | "try" => return .«try» a\n  | "assembly" => return .asm a\n  | tag =>\n    return .call target args\n'
        self.assertEqual(coverage.normalizer(sample), {'add': ['arith'], 'add_safe': ['arith'], 'try': ['try'], 'assembly': ['asm']})

    def test_model_recognition_is_not_verification(self):
        data = (ROOT/'Air2Lean/Memory.lean').read_text()
        entries = coverage.model_inventory(data)
        self.assertTrue(any(row['name'] == 'Thread.yield' and row['disposition'] == 'translation-rejected' for row in entries))
        self.assertTrue(any(row['name'] == 'time.Timer.read' and row['disposition'] == 'recognized-model-boundary' for row in entries))
        self.assertTrue(all('source-only' in row['qualification'] for row in entries))


if __name__ == '__main__':
    unittest.main()
