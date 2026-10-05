"""Offline synthetic compiler regression tests; no Zig or Lean process."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest
from unittest.mock import patch

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

    def test_zig_quoted_identifier_escapes(self):
        self.assertEqual(coverage.identifier(r'@"\x61\u{62}"'), 'ab')
        self.assertEqual(coverage.identifier(r'@"\xC3\xA9"'), 'é')
        self.assertEqual(coverage.identifier(r'@"\u{1f600}"'), '😀')
        for token in (r'@"\xFF"', r'@"\u{D800}"', r'@"\u{110000}"',
                      r'@"\u{}"', r'@"\x0"', r'@"\b"', r'@"\f"'):
            with self.assertRaises(ValueError, msg=token): coverage.identifier(token)
        with self.assertRaises(ValueError):
            coverage.members(r'const Tag = enum { a, @"\x61", };', 'Tag', 'enum')

    def test_selected_shared_version_and_os_goldens(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'examples/demo').mkdir(parents=True)
            (root/'examples/excluded').mkdir(parents=True)
            (root/'examples/excluded/zig-versions').write_text('0.14.1\n')
            paths = ['tests/golden/demo/air/shared.json',
                     'tests/golden/demo/air/override.json',
                     'tests/golden/demo/air/generic__anon_1.json',
                     'tests/golden/demo/air/generic__anon_2.json',
                     'tests/golden/0.16.0/demo/air/override.json',
                     'tests/golden/0.16.0/demo/air/generic__anon_3.json',
                     'tests/golden/0.16.0/demo/air/generic__anon_4.json',
                     'tests/golden/0.16.0/demo/air-linux/generic__anon_5.json',
                     'tests/golden/0.16.0/demo/air-darwin/darwin.json',
                     'tests/golden/excluded/air/skipped.json']
            for relative in paths:
                p = root/relative; p.parent.mkdir(parents=True, exist_ok=True); p.write_text('{}')
            with patch.object(coverage, 'ROOT', root):
                selected = [str(p.relative_to(root)) for p in coverage.golden_paths('0.16.0', 'linux')]
                self.assertCountEqual(selected, [paths[0], paths[4], paths[7]])
                darwin = [str(p.relative_to(root)) for p in coverage.golden_paths('0.16.0', 'darwin')]
                self.assertCountEqual(darwin, [paths[0], paths[4], paths[5], paths[6], paths[8]])

    def test_pointer_classification_follows_new_source_arm(self):
        body = coverage.function_body('fn writePtr() void { while (true) switch (base) { .nav => |n| { use(n); }, .int => |i| { conditional(i); }, else => { field("unsupported"); }, }; }', 'writePtr')
        arms = coverage.switch_arms(body, ['base'])
        rows = coverage.pointer_dispositions(['nav', 'int', 'field'], arms)
        self.assertEqual(rows[1]['disposition'], 'exporter-explicit-arm-conditional-review')
        self.assertEqual(rows[2]['disposition'], 'exporter-fallback-unsupported-marker-review')
        self.assertTrue(all('review' in row['disposition'] for row in rows))

    def test_optional_compiler_file_requires_exact_case(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            (parent/'io.zig').write_text('// older Zig namespace')
            # Simulate macOS's permissive file lookup even on a Linux test host.
            with patch.object(Path, 'is_file', return_value=True):
                self.assertFalse(coverage.exact_file(parent/'Io.zig'))
                self.assertTrue(coverage.exact_file(parent/'io.zig'))
            (parent/'io.zig').unlink()
            (parent/'Io.zig').write_text('// newer Zig namespace')
            self.assertTrue(coverage.exact_file(parent/'Io.zig'))

    def test_file_cache_reuses_bytes_and_new_invocation_is_fresh(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'source.zig'
            path.write_text('const Tag = enum { a, };')
            cache = coverage.SourceCache()
            read_bytes = Path.read_bytes
            with patch.object(Path, 'read_bytes', autospec=True) as read:
                read.side_effect = read_bytes
                first = cache.digest(path)
                self.assertEqual(cache.tokens(path), cache.tokens(path))
                cache.text(path); cache.digest(path)
                self.assertEqual(read.call_count, 1)
            path.write_text('const Tag = enum { b, };')
            self.assertEqual(cache.digest(path), first)  # Consistent within an invocation.
            fresh = coverage.SourceCache()
            self.assertNotEqual(fresh.digest(path), first)
            self.assertEqual(coverage.members(fresh.tokens(path), 'Tag', 'enum'), ['b'])

    def test_union_payloads_and_wildcard(self):
        source = 'const Key = union(enum) { int: Int, @"extern": Extern, nested: struct { a: u8, b: u16 }, };'
        self.assertEqual(coverage.members(source, 'Key', 'union'), ['int', 'extern', 'nested'])
        self.assertEqual(coverage.members('const Tag = enum { a, _, };', 'Tag', 'enum'), ['a'])

    def test_project_fingerprints_ignore_warm_caches_but_keep_source_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = ['tests/diff/Main.lean', 'tests/diff/inputs/case.jsonl',
                       'tests/diff/nested/out/source.json', 'tests/different/out/source.json']
            for relative in sources:
                path = root/relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('source bytes\n')
            with patch.object(coverage, 'ROOT', root):
                def fingerprints():
                    return coverage.project_source_hashes(['tests'], coverage.SourceCache())
                clean = fingerprints()
                self.assertEqual(set(clean), set(sources))  # No Git checkout is needed.
                for relative in ['tests/diff/.lake/build/lib/Main.olean',
                                 'tests/diff/__pycache__/helper.pyc',
                                 'tests/diff/out/native-result.json',
                                 'tests/different/.lake/build/trace.json']:
                    path = root/relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b'transient build/test output')
                self.assertEqual(fingerprints(), clean)
                changed_source = root/sources[0]
                changed_source.write_text('edited source bytes\n')
                changed = fingerprints()
                self.assertEqual(set(changed), set(clean))
                self.assertNotEqual(changed[sources[0]], clean[sources[0]])
                self.assertEqual({key: changed[key] for key in sources[1:]},
                                 {key: clean[key] for key in sources[1:]})
                added = root/'tests/diff/new-source.lean'
                added.write_text('new untracked source bytes\n')
                self.assertIn('tests/diff/new-source.lean', fingerprints())

    def test_project_fingerprints_never_descend_into_transient_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            caches = [root/'tests/diff/.lake', root/'tests/diff/__pycache__',
                      root/'tests/diff/out']
            for cache in caches:
                cache.mkdir(parents=True)
                (cache/'entry').write_bytes(b'build/test artifacts')
            source = root/'tests/diff/Main.lean'
            source.write_text('source bytes\n')
            (root/'tests/diff/Alias.lean').symlink_to(source)
            (root/'tests/diff/Missing.lean').symlink_to(root/'absent.lean')
            external = root/'external'
            external.mkdir()
            (external/'External.lean').write_text('outside the selected roots\n')
            (root/'tests/diff/linked-directory').symlink_to(external, target_is_directory=True)
            # Observe filesystem access instead of relying on cache entry counts
            # or permissions (the test also works for privileged users).
            scandir = os.scandir
            def reject_cache_scan(path):
                self.assertNotIn(Path(path), caches, 'inventory descended into a transient directory')
                return scandir(path)
            with patch.object(coverage, 'ROOT', root), patch.object(os, 'scandir', reject_cache_scan):
                result = coverage.project_source_hashes(['tests'], coverage.SourceCache())
            self.assertEqual(set(result), {'tests/diff/Main.lean', 'tests/diff/Alias.lean'})
            self.assertEqual(result['tests/diff/Main.lean'], result['tests/diff/Alias.lean'])

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

    def test_upgrade_first_duplicate_behavior_is_preserved(self):
        minimal = {'zig_version': 'test', 'universe': {}, 'project_source_sha256': {},
                   'compiler_source_sha256': {}, 'models': [], 'tags': [{'tag': 'a', 'value': 1}, {'tag': 'a', 'value': 2}]}
        changed_duplicate = dict(minimal, tags=[{'tag': 'a', 'value': 1}, {'tag': 'a', 'value': 3}])
        self.assertEqual(coverage.changes(minimal, changed_duplicate)['tag_dispositions_changed'], [])
        changed_first = dict(minimal, tags=[{'tag': 'a', 'value': 4}, {'tag': 'a', 'value': 2}])
        self.assertEqual(coverage.changes(minimal, changed_first)['tag_dispositions_changed'], ['a'])

    def test_normalizer_branch_does_not_capture_fallback(self):
        sample = '\n  match raw.tag with\n  | "add" | "add_safe" => return .arith .add\n  | "try" => return .«try» a\n  | "assembly" => return .asm a\n  | tag =>\n    return .call target args\n'
        self.assertEqual(coverage.normalizer(sample), {'add': ['arith'], 'add_safe': ['arith'], 'try': ['try'], 'assembly': ['asm']})

    def test_model_recognition_is_not_verification(self):
        sample = '''def allocFn? (name : String) := none
/-- Synthetic recognized model section. -/
def threadFn? (name : String) :=
  if name == "time.Timer.read" then some .noClock else none
/-- Synthetic rejected model section. -/
def rejectedThreadFn? (name : String) :=
  if name == "Thread.yield" then some "unsupported" else none
'''
        entries = coverage.model_inventory(sample)
        self.assertEqual([(row['name'], row['disposition']) for row in entries], [
            ('time.Timer.read', 'recognized-model-boundary'),
            ('Thread.yield', 'translation-rejected')])
        self.assertTrue(all('source-only' in row['qualification'] for row in entries))
        current = coverage.model_inventory((ROOT/'Air2Lean/Memory.lean').read_text())
        self.assertTrue(current)
        self.assertTrue(all('source-only' in row['qualification'] for row in current))


if __name__ == '__main__':
    unittest.main()
