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
        body = coverage.function_body('fn resolvePtr() void { while (true) switch (base) { .nav => |n| { use(n); }, .int => |i| { conditional(i); }, .arr_elem => return .{ .unsupported = "arr_elem" }, else => return .{ .unsupported = @tagName(base) }, }; }', 'resolvePtr')
        arms = coverage.switch_arms(body, ['base'])
        rows = coverage.pointer_dispositions(['nav', 'int', 'arr_elem', 'field'], arms)
        self.assertEqual([row['disposition'] for row in rows], ['resolved-conditional', 'resolved-conditional',
                         'rejected-unsupported-pointer-base', 'rejected-unsupported-pointer-base'])
        # Without the checker's rejection, or without an unsupported fallback, nothing is named.
        unchecked = coverage.pointer_dispositions(['nav', 'arr_elem', 'field'], arms, checker_rejects=False)
        self.assertEqual([row['disposition'] for row in unchecked],
                         ['resolved-conditional', coverage.FORBIDDEN, coverage.FORBIDDEN])
        silent = coverage.switch_arms(coverage.function_body('fn resolvePtr() void { switch (base) { .nav => {}, else => {}, } }', 'resolvePtr'), ['base'])
        self.assertEqual(coverage.pointer_dispositions(['field'], silent)[0]['disposition'], coverage.FORBIDDEN)

    def test_compat_version_branches_and_named_fallback_decoders(self):
        exporter = coverage.tokens('''fn isNewTyOp(tag: Tag) bool { return if (v14) false else tag == .new_ty; }
          fn writeInst() void { switch (tag) { else => {}, } switch (tag) {
            .asm_tag => if (Compat.v14) { try w.field("unsupported"); } else { try w.writeAsm(inst); },
            .guarded => { if (bad) { try w.field("unsupported"); } },
            else => if (!Compat.v14) { if (tag == .split_one) { one(); } else if (Compat.isNewTyOp(tag)) { ty(); } else { try w.field("unsupported"); } }
                    else if (tag == .old_shuffle) { old(); } else { try w.field("unsupported"); },
          } }''')
        decode = coverage.switch_arms(coverage.function_body(exporter, 'writeInst'), ['tag'], 1)
        def status(tag, minor):
            return coverage.exporter_status(tag, decode, minor, exporter)
        self.assertEqual(status('asm_tag', 14), 'explicit-arm-unsupported-marker')
        self.assertEqual(status('asm_tag', 16), 'explicit-arm')
        self.assertEqual(status('asm_tag', None), 'version-conditional-unresolved')
        self.assertEqual(status('guarded', 16), 'explicit-arm-conditional-unsupported')
        self.assertEqual(status('split_one', 15), 'fallback-named-decoder')
        self.assertEqual(status('new_ty', 16), 'fallback-named-decoder')
        self.assertEqual(status('old_shuffle', 14), 'fallback-named-decoder')
        self.assertEqual(status('old_shuffle', 16), 'fallback-unsupported-marker')
        # Every branch rejects an unnamed tag, so even an unknown version label agrees.
        self.assertEqual(status('brand_new', None), 'fallback-unsupported-marker')
        self.assertEqual(coverage.version_minor('0.15.2'), 15)
        self.assertIsNone(coverage.version_minor('synthetic'))

    def test_emission_dispatch_arms_and_erasure(self):
        emit = '''def emitScalar (fc : FCtx) :=
  match inst.op with
  | .arith op a b => (env, some "x")
  | .line _ => (env, none)
  | .«try» v _ | .dbg _ _ => (env, none)
  | _ => (env, some "-- unexpected")

def laneOp? : Op → Option Op
  | .notDispatched => none

mutual
partial def emitStmts (fc : FCtx) := match i.op with
      | .block body => ""
partial def emitTerminator (fc : FCtx) := match inst.op with
  | .ret v => ""
end
'''
        arms, erased = coverage.emission_arms(emit)
        self.assertEqual(arms, {'arith', 'line', 'try', 'dbg', 'block', 'ret'})
        self.assertEqual(erased, {'line', 'try', 'dbg'})

    def test_committed_inventories_name_every_disposition(self):
        for path in sorted((ROOT/'coverage').glob('*.json')):
            inventory = json.loads(path.read_text())
            self.assertEqual(coverage.disposition_problems(inventory), [], path.name)
            self.assertEqual(inventory['dispositions'], coverage.DISPOSITIONS, path.name)
            overridden = [row for category in coverage.UNIVERSES for row in inventory[category]
                          if row['derivation']['method'] != 'mechanical']
            self.assertTrue(all(row['derivation']['method'] == 'reviewed-override' and row['derivation']['reason']
                                for row in overridden), path.name)

    def test_committed_inventories_pass_l14_gate(self):
        for path in sorted((ROOT/'coverage').glob('*.json')):
            inventory = json.loads(path.read_text())
            self.assertEqual(coverage.l14_problems(inventory), [], path.name)
            for row in inventory['tags']:
                if row['disposition'] == 'emitted-unqualified':
                    self.assertTrue(all(coverage.compiler_fixture_path(p) for p in row['tests']['paths']), row['tag'])
                if row['disposition'].startswith('rejected-'):
                    self.assertIn(row['rejection']['reason'], row['guidance'])

    def test_l14_gate_fails_closed(self):
        inventory = json.loads((ROOT/'coverage/0.16.0.json').read_text())
        rows = {row['tag']: row for row in inventory['tags']}
        # A supported tag whose only fixture is hand-written or missing AIR has no witness.
        rows['add']['tests']['paths'] = ['tests/roadmap/global-init/air/0.16.0/x.json', 'tests/golden/missing.json']
        # An unfixtured tag needs a current request; a rejected tag needs the current reason.
        rows['sub_sat']['fixture_request'] = None
        rows['prefetch']['rejection']['reason'] = 'stale text'
        rows['add_optimized']['rejection'] = None
        # A reason recorded under the wrong translator definition is not current.
        rows['breakpoint']['rejection']['definition'] = 'runtimeTagReason?'
        problems = coverage.l14_problems(inventory)
        self.assertEqual(len(problems), 5, problems)
        for tag in ('add', 'sub_sat', 'prefetch', 'add_optimized', 'breakpoint'):
            self.assertTrue(any(f': {tag}:' in p for p in problems), tag)
        self.assertIsNone(coverage.fixture_request('no_such_tag', ''))
        with patch.dict(coverage.FIXTURE_REQUESTS, {'sub_sat': 'missingFunction'}):
            self.assertIsNone(coverage.fixture_request('sub_sat', (ROOT/coverage.FIXTURE_SOURCE).read_text()))
        self.assertFalse(coverage.compiler_fixture_path('tests/roadmap/undef-operands/air/0.16.0/a.json'))
        self.assertTrue(coverage.compiler_fixture_path('tests/roadmap/try-pointers/air/0.16.0/a.json'))

    def test_every_roadmap_air_directory_is_reviewed(self):
        self.assertEqual(coverage.unreviewed_air_roots(), [])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stray = root/'tests/roadmap/new-case/air/0.16.0/f.json'
            stray.parent.mkdir(parents=True)
            stray.write_text(json.dumps({'zig_version': '0.16.0', 'body': []}))
            (root/'tests/roadmap/new-case/other.json').write_text('{"schema": 1}')
            with patch.object(coverage, 'ROOT', root):
                self.assertEqual(coverage.unreviewed_air_roots(), ['tests/roadmap/new-case/air/0.16.0'])

    def test_disposition_problems_fail_closed(self):
        inventory = {'universe': {'air_tags': ['a', 'b'], 'types': [], 'intern_keys': [], 'pointer_bases': []},
                     'tags': [{'tag': 'a', 'disposition': 'emitted-unqualified'}], 'types': [], 'constants': [], 'pointer_bases': []}
        self.assertEqual(coverage.disposition_problems(inventory), ['tags: rows do not match the compiler air_tags universe'])
        inventory['tags'].append({'tag': 'b', 'disposition': 'invented-name'})
        self.assertEqual(len(coverage.disposition_problems(inventory)), 1)
        inventory['tags'][1]['disposition'] = coverage.FORBIDDEN
        self.assertEqual(len(coverage.disposition_problems(inventory)), 1)
        inventory['tags'][1]['disposition'] = 'rejected-unknown-tag'
        self.assertEqual(coverage.disposition_problems(inventory), [])

    def test_stale_override_is_forbidden(self):
        override = {'disposition': 'unreachable-at-export', 'replaces': 'rejected-exporter-unsupported', 'reason': 'reviewed'}
        with patch.dict(coverage.OVERRIDES['tags'], {'gpu_tag': override}):
            applied = coverage.apply_override('tags', {'tag': 'gpu_tag', 'disposition': 'rejected-exporter-unsupported'})
            self.assertEqual(applied['disposition'], 'unreachable-at-export')
            self.assertEqual(applied['derivation']['method'], 'reviewed-override')
            # The exporter started decoding the tag: the reviewed premise no longer holds.
            stale = coverage.apply_override('tags', {'tag': 'gpu_tag', 'disposition': 'emitted-unqualified'})
            self.assertEqual(stale['disposition'], coverage.FORBIDDEN)
            self.assertEqual(stale['derivation']['derived'], 'emitted-unqualified')

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
                'src/Air.zig': 'pub const Inst = struct { pub const Tag = enum(u8) { add, prefetch, }; };',
                'lib/std/builtin.zig': 'pub const Type = union(enum) { int: Int, @"struct": Struct, };',
                'src/InternPool.zig': 'pub const Key = union(enum) { int_type: IntType, int: Int, pub const Ptr = struct { pub const BaseAddr = union(enum) { nav: Nav, int: u64, }; }; };',
            }.items():
                path = source/relative; path.parent.mkdir(parents=True, exist_ok=True); path.write_text(data)
            universe, fingerprints = coverage.compiler_inventory(source)
            self.assertEqual(universe['air_tags'], ['add', 'prefetch'])
            self.assertEqual(universe['types'], ['int', 'struct'])
            self.assertEqual(universe['intern_keys'], ['int_type', 'int'])
            self.assertEqual(universe['pointer_bases'], ['nav', 'int'])
            self.assertEqual(len(fingerprints), 11)
            self.assertIsNone(fingerprints['lib/std/Io.zig'])
            report = coverage.generate('synthetic-no-goldens', source)
            self.assertEqual(len(report['tags']), 2)
            new = next(row for row in report['tags'] if row['tag'] == 'prefetch')
            # An unnamed tag reaches the real exporter's unsupported fallback in every version branch
            # and carries the translator's reviewed reason (L14).
            self.assertEqual(new['exporter']['status'], 'fallback-unsupported-marker')
            self.assertEqual(new['disposition'], 'rejected-exporter-unsupported')
            self.assertIn('@prefetch', new['rejection']['reason'])
            self.assertEqual(new['rejection']['definition'], 'exporterTagReason?')
            self.assertEqual(new['tests']['paths'], [])
            self.assertEqual(coverage.disposition_problems(report), [])
            self.assertEqual(coverage.l14_problems(report), [])
            self.assertTrue(all(row['proofs']['status'] == 'symbol-index-only-not-proof-coverage' for row in report['tags']))
            snapshot = source/'inventory.json'
            command = [sys.executable, str(ROOT/'scripts/coverage.py')]
            arguments = ['--version', 'synthetic-no-goldens', '--source', str(source), '--inventory', str(snapshot)]
            generated = subprocess.run(command + ['generate'] + arguments, capture_output=True, text=True)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            checked = subprocess.run(command + ['check'] + arguments, capture_output=True, text=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            # A row without a named disposition fails generate and an otherwise current check.
            forbidden = source/'forbidden.json'
            stale = {'add': {'disposition': 'unreachable-at-export', 'replaces': 'rejected-unknown-tag', 'reason': 'test'}}
            forbidden_arguments = ['--version', 'synthetic-no-goldens', '--source', str(source), '--inventory', str(forbidden)]
            with patch.dict(coverage.OVERRIDES['tags'], stale), patch('sys.stderr'), patch('sys.stdout'):
                for name in ('generate', 'check'):
                    with patch.object(sys, 'argv', ['coverage.py', name] + forbidden_arguments):
                        self.assertEqual(coverage.main(), 1, name)
            self.assertEqual(json.loads(forbidden.read_text())['tags'][0]['disposition'], coverage.FORBIDDEN)
            # A renamed AIR tag and payload-only changes both fail the fingerprint gate.
            (source/'src/Air.zig').write_text('pub const Tag = enum(u8) { add, renamed_tag, };')
            upgraded = coverage.generate('synthetic-next', source)
            delta = coverage.changes(report, upgraded)
            self.assertEqual(delta['universes']['air_tags']['added'], ['renamed_tag'])
            self.assertEqual(delta['universes']['air_tags']['removed'], ['prefetch'])
            # A new exporter-rejected tag without a reviewed translator reason is forbidden.
            renamed = next(row for row in upgraded['tags'] if row['tag'] == 'renamed_tag')
            self.assertEqual(renamed['disposition'], coverage.FORBIDDEN)
            self.assertTrue(delta['compiler_sources_changed'])
            stale = subprocess.run(command + ['check'] + arguments, capture_output=True, text=True)
            self.assertEqual(stale.returncode, 1, stale.stderr)
            self.assertIn('renamed_tag', stale.stdout)
            self.assertIn('Inventory stale', stale.stderr)
            missing = subprocess.run(command + ['check', '--version', 'synthetic', '--source', str(source/'missing'), '--inventory', str(snapshot)], capture_output=True, text=True)
            self.assertEqual(missing.returncode, 2, missing.stderr)
            # Zig 0.17 moved Type to lib/std/lang.zig; with neither file the inventory fails closed.
            (source/'lib/std/builtin.zig').rename(source/'lib/std/lang.zig')
            lang_universe, lang_fingerprints = coverage.compiler_inventory(source)
            self.assertEqual(lang_universe['types'], ['int', 'struct'])
            self.assertIn('lib/std/lang.zig', lang_fingerprints)
            self.assertNotIn('lib/std/builtin.zig', lang_fingerprints)
            (source/'lib/std/lang.zig').unlink()
            with self.assertRaises(OSError): coverage.compiler_inventory(source)
            (source/'lib/std/builtin.zig').write_text('pub const Type = union(enum) { int: Int, @"struct": Struct, };')
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
        sample = '''def stdModels : Array StdModel := #[
  threadModel "time.Timer.read" .timerRead #["callRC"],
  { symbol := "Thread.yield",
    kind := .rejected "unsupported" }]

def unrelated := "Thread.join"
'''
        entries = coverage.model_inventory(sample)
        self.assertEqual([(row['name'], row['disposition']) for row in entries], [
            ('time.Timer.read', 'recognized-model-boundary'),
            ('Thread.yield', 'translation-rejected')])
        self.assertTrue(all('source-only' in row['qualification'] for row in entries))
        current = coverage.model_inventory((ROOT/'Air2Lean/StdModels.lean').read_text())
        self.assertTrue(current)
        self.assertTrue(all('source-only' in row['qualification'] for row in current))


if __name__ == '__main__':
    unittest.main()
