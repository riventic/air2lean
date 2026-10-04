#!/usr/bin/env python3
"""Bounded offline filename, receipt, normalization and public dump regressions."""
import copy
import hashlib
import contextlib
import io
import json
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
CHECK = runpy.run_path(str(Path(__file__).with_name('check_dump.py')))
NORM = runpy.run_path(str(ROOT / 'scripts/normalize-air.py'))
HELPERS = runpy.run_path(str(ROOT / 'scripts/normalize-generated.py'))
CURRENT = json.loads((ROOT / 'tests/roadmap/profiles/current.json').read_text())


class Names(unittest.TestCase):
    def test_byte_boundary_and_full_digest(self):
        filename = CHECK['filename']
        self.assertEqual(filename('a'*250), 'a'*250+'.json')
        name = 'a'*251
        self.assertEqual(filename(name), CHECK['PREFIX']+hashlib.sha256(name.encode()).hexdigest()+'.json')
        self.assertLess(len(filename(name).encode()), 255)
        self.assertNotEqual(filename(name+'A'), filename(name+'B'))

    def test_unsafe_and_reserved_names_use_disjoint_namespace(self):
        for name in ('a/b', 'a\\b', 'a:b', 'a\x00b', 'naïve😀', '..', '-flag', '',
                     'CON', 'con.fun', 'LPT9.fun', '~air2lean-sha256-'+'a'*64):
            with self.subTest(name=name):
                self.assertTrue(CHECK['filename'](name).startswith(CHECK['PREFIX']))
        for name in ('basic.scale', 'a__anon_42', 'a-b', '_', 'COM10.fun'):
            self.assertEqual(CHECK['filename'](name), name+'.json')

    def test_public_fixture_contains_exact_boundary_and_long_identities(self):
        names = json.loads(Path(__file__).with_name('expected-names.json').read_text())
        self.assertEqual(len(names), 10)
        self.assertIn(408, [len(name.encode()) for name in names])
        self.assertIn(250, [len(name.encode()) for name in names])
        self.assertIn(251, [len(name.encode()) for name in names])
        self.assertEqual(sum(CHECK['filename'](x).startswith(CHECK['PREFIX']) for x in names), 7)
        source = Path(__file__).with_name('export_names.zig').read_text()
        for name in names[:5]:
            self.assertIn(name.removeprefix('export_names.'), source)

    def test_source_keeps_identity_and_checks_before_truncation(self):
        source = (ROOT / 'zig-patch/air-json/json.zig').read_text()
        self.assertIn('w.writeFunc(fqn,', source)
        self.assertIn('std.mem.startsWith(u8, fqn, prefix)', source)
        self.assertIn('std.crypto.hash.sha2.Sha256.hash(fqn, &digest, .{})', source)
        self.assertNotIn('name too long for a file', source)
        owned = source[source.index('fn openOwnedOutput'):source.index('pub fn dumpToDir')]
        self.assertLess(owned.index('std.mem.eql(u8, identity.string, fqn)'), owned.index('Compat.truncateFile'))
        self.assertIn('error.PathAlreadyExists', owned)
        self.assertIn('error.OutputIdentityCollision', owned)
        self.assertIn('error.ExistingOutputTooLarge', owned)
        self.assertLess(owned.index('Compat.statPath'), owned.index('Compat.openExistingFile'))
        self.assertIn('.exclusive = true', source)
        self.assertIn('.lock_nonblocking = true', source)
        self.assertIn('file.preadAll(bytes, 0)', source)
        self.assertIn('file.readPositionalAll(pt.zcu.comp.io, bytes, 0)', source)


class Normalization(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean-export-names-')
        self.root = Path(self.temp.name)
        self.air = self.root/'air'
        self.air.mkdir()
        self.out = self.root/'normalized'
        self.report = self.root/'report.json'
        self.gen = self.root/'Gen.lean'
        metadata = dict(profile=HELPERS['profile_for_air'](CURRENT), float_semantics='ieee', correspondence='model')
        self.gen.write_bytes(HELPERS['PREFIX']+json.dumps(metadata).encode()+b'\nimport ZigLean\n')

    def tearDown(self):
        self.temp.cleanup()

    def write(self, name, value=1):
        doc = copy.deepcopy(CURRENT)
        doc['name'] = name
        doc['body'][0]['observable'] = value
        path = self.air/CHECK['filename'](name)
        path.write_text(json.dumps(doc, ensure_ascii=False))
        return path

    def context(self):
        HELPERS['write_report'](self.gen, self.air, self.report)
        return NORM['ValidationContext'](self.report, True)

    def test_hashed_anonymous_names_converge_after_raw_validation(self):
        paths = [self.write('long'+'a'*260+f'__anon_{i}', i) for i in (1, 923)]
        context = self.context()
        entries = [context.file_entry(p) for p in paths]
        self.assertEqual(entries[0][0], entries[1][0])
        canonical = 'long'+'a'*260+'__anon_N'
        self.assertEqual(entries[0][0], CHECK['filename'](canonical))
        NORM['add_directory'](self.air, self.out, context)
        expected = {n.removesuffix('.json')+'.'+hashlib.sha1(data).hexdigest()[:12]+'.json':data for n,data in entries}
        self.assertEqual({p.name:p.read_bytes() for p in self.out.iterdir()}, expected)
        # The later single overlay removes every prior collision variant, retaining unrelated files.
        for p in paths: p.unlink()
        self.write('long'+'a'*260+'__anon_8', 8)
        (self.out/'unrelated.json').write_bytes(b'KEEP')
        NORM['add_directory'](self.air, self.out, self.context())
        self.assertEqual(set(p.name for p in self.out.iterdir()), {CHECK['filename'](canonical), 'unrelated.json'})
        self.assertEqual((self.out/'unrelated.json').read_bytes(), b'KEEP')

    def test_hash_mismatch_preserves_overlay_even_when_receipt_matches(self):
        path = self.write('long'+'a'*260)
        wrong = self.air/(CHECK['PREFIX']+'0'*64+'.json')
        path.rename(wrong)
        context = self.context()
        self.out.mkdir()
        sentinel = self.out/'previous.json'
        sentinel.write_bytes(b'KEEP')
        with self.assertRaisesRegex(ValueError, 'filename does not match'):
            NORM['add_directory'](self.air, self.out, context)
        self.assertEqual(sentinel.read_bytes(), b'KEEP')

    def test_raw_receipt_is_checked_before_identity_filename(self):
        path = self.write('long'+'a'*260)
        context = self.context()
        doc = json.loads(path.read_text()); doc['name'] = 'different'
        path.write_text(json.dumps(doc))
        with self.assertRaisesRegex(ValueError, 'does not match validated translation report'):
            context.file_entry(path)

    def test_short_filenames_and_observable_data_are_unchanged(self):
        path = self.write('basic.fun__anon_9')
        context = self.context()
        name,data = context.file_entry(path)
        self.assertEqual(name, 'basic.fun__anon_N.json')
        self.assertEqual(data, context.file(path))
        self.assertEqual(json.loads(data)['body'][0]['observable'], 1)

    def test_public_dump_checker_uses_full_json_name_and_rejects_duplicate_identity(self):
        names = json.loads(Path(__file__).with_name('expected-names.json').read_text())
        for name in names: self.write(name)
        self.assertEqual(set(CHECK['documents'](self.air)), set(names))
        first = self.air/CHECK['filename'](names[0])
        (self.air/'zzduplicate.json').write_bytes(first.read_bytes())
        with self.assertRaisesRegex(ValueError, 'duplicate full identity'):
            CHECK['documents'](self.air)

    def inspect(self, mode):
        with mock.patch('sys.argv', ['check_dump.py', str(self.air), '--mode', mode]), contextlib.redirect_stdout(io.StringIO()):
            CHECK['main']()

    def populate_public_dump(self):
        for name in json.loads(Path(__file__).with_name('expected-names.json').read_text()):
            self.write(name)

    def test_collision_inspector_requires_exact_bytes_and_all_siblings(self):
        self.populate_public_dump()
        self.inspect('seed-collision')
        self.inspect('check-collision')
        marker = json.loads((self.air/'.export-names-expectation').read_text())
        target = self.air/marker['file']
        target.write_text('{}')
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.inspect('check-collision')

    def test_reexport_inspector_rejects_preserved_old_document_then_accepts_replacement(self):
        self.populate_public_dump()
        self.inspect('seed-reexport')
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.inspect('check-reexport')
        marker = json.loads((self.air/'.export-names-expectation').read_text())
        self.write(marker['name'])
        self.inspect('check-reexport')


if __name__ == '__main__':
    unittest.main()
