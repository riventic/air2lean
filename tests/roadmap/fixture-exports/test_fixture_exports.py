#!/usr/bin/env python3
"""scripts/fixture-exports.py without a compiler: manifest validation, the lock check (each pin
detects its change), the per-file profile checks and the call-closure selection, on synthetic
fixtures; then `check` of every committed manifest."""
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('fixture_exports', ROOT / 'scripts/fixture-exports.py')
fx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fx)
VERSION = fx.versions()[0]
ARGS = ['-OReleaseSafe', '-fno-error-tracing', '-target', 'x86_64-linux', '-mcpu=baseline']


def document(name, calls=(), version=VERSION, **profile):
    base = {'build_mode': 'ReleaseSafe', 'error_tracing': False, 'target_triple': 'x86_64-linux.5.10-musl',
            'error_set_bits': 16}
    base.update(profile)
    body = [{'tag': 'call', 'func': c} for c in calls]
    return {'schema': 12, 'zig_version': version, 'name': name, 'profile': base, 'body': body}


class Synthetic(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix='fixture-exports-test.'))
        self.saved = fx.FIXTURES
        fx.FIXTURES = self.root
        self.here = self.root / 'demo'
        (self.here / 'air' / VERSION).mkdir(parents=True)
        (self.here / 'demo.zig').write_text('pub fn add(a: u32) u32 { return a; }\n')
        self.entry = {'out': 'air/{version}', 'source': 'demo.zig', 'filter': 'demo.', 'versions': [VERSION],
                      'args': list(ARGS)}
        self.write_manifest([self.entry])
        self.write_air('demo.add.json', document('demo.add'))
        self.lock()

    def tearDown(self):
        fx.FIXTURES = self.saved
        shutil.rmtree(self.root)

    def write_manifest(self, exports):
        (self.here / fx.MANIFEST).write_text(json.dumps({'exports': exports}))

    def write_air(self, name, doc):
        (self.here / 'air' / VERSION / name).write_text(json.dumps(doc))

    def lock(self):
        data = fx.manifest('demo')
        (self.here / fx.LOCK).write_text(json.dumps(fx.lock_of('demo', data, fx.outputs('demo', data))))

    def test_clean_fixture_passes(self):
        self.assertEqual(fx.check('demo'), [])

    def test_each_pin_detects_its_change(self):
        self.write_air('demo.add.json', document('demo.add', calls=['demo.add']))
        self.assertTrue(any('committed AIR differs' in p for p in fx.check('demo')))
        self.lock()
        (self.here / 'demo.zig').write_text('pub fn add(a: u32) u32 { return a + 0; }\n')
        self.assertTrue(any('a source changed' in p for p in fx.check('demo')))
        self.lock()
        saved = fx.compiler_identity
        fx.compiler_identity = lambda version: 'another exporter'
        try:
            self.assertTrue(any('exporter (zig-patch/) changed' in p for p in fx.check('demo')))
        finally:
            fx.compiler_identity = saved
        self.write_manifest([dict(self.entry, filter='demo.,mem.')])
        self.assertTrue(any('exports.json changed' in p for p in fx.check('demo')))

    def test_added_or_removed_file_is_detected(self):
        self.write_air('demo.extra.json', document('demo.add'))
        self.assertTrue(any('demo.extra.json' in p for p in fx.check('demo')))

    def test_a_file_must_be_its_versions_export(self):
        cases = [(document('demo.add', version='0.0.0'), 'zig_version'),
                 (document('demo.add', build_mode='ReleaseFast'), 'build_mode'),
                 (document('demo.add', error_tracing=True), 'error_tracing'),
                 (document('demo.add', target_triple='aarch64-linux-gnu'), 'target'),
                 (document('demo.add', error_set_bits=8), 'error_set_bits'),
                 (document('demo.sub'), 'not declared')]
        for doc, what in cases:
            with self.subTest(what):
                self.write_air('demo.add.json', doc)
                self.lock()
                self.assertTrue(any(what in p for p in fx.check('demo')), fx.check('demo'))

    def test_error_limit_sets_the_width(self):
        self.write_manifest([dict(self.entry, args=ARGS + ['--error-limit', '255'])])
        self.write_air('demo.add.json', document('demo.add', error_set_bits=8))
        self.lock()
        self.assertEqual(fx.check('demo'), [])

    def test_safe_is_the_017_spelling(self):
        self.write_air('demo.add.json', document('demo.add', build_mode='safe'))
        self.lock()
        self.assertEqual(fx.check('demo'), [])

    def test_manifest_rejects(self):
        bad = [{'exports': []},
               {'exports': [dict(self.entry, extra=1)]},
               {'exports': [dict(self.entry, out='air')]},
               {'exports': [dict(self.entry, out='../air/{version}')]},
               {'exports': [dict(self.entry, versions=['0.0.0'])]},
               {'exports': [dict(self.entry, source='missing.zig')]},
               {'exports': [dict(self.entry, args=ARGS + ['-fno-emit-bin'])]},
               {'exports': [dict(self.entry, command='run')]},
               {'exports': [dict(self.entry, closure=[])]},
               {'exports': [dict(self.entry, closure=['*'])]},
               {'exports': [dict(self.entry, stop=['debug.*'])]},
               {'exports': [dict(self.entry, source='../../../../etc/passwd')]},
               {'exports': [self.entry, dict(self.entry, out='air/{version}/inner')]},
               {'exports': [self.entry, dict(self.entry)]}]
        for data in bad:
            with self.subTest(data=data):
                (self.here / fx.MANIFEST).write_text(json.dumps(data))
                with self.assertRaises(fx.Error):
                    fx.manifest('demo')

    def test_closure_keeps_what_the_roots_reach(self):
        directory = self.root / 'closure'
        directory.mkdir()
        docs = {'demo.root': ['mem.copy'], 'mem.copy': ['mem.inner'], 'mem.inner': [],
                'debug.panicOnly': ['mem.unused'], 'mem.unused': []}
        for name, calls in docs.items():
            (directory / (name + '.json')).write_text(json.dumps(document(name, calls)))
        (directory / 'error-table.json').write_text(json.dumps({'errors': []}))
        fx.keep_closure(directory, ['demo.*'])
        self.assertEqual(sorted(p.stem for p in directory.glob('*.json')),
                         ['demo.root', 'error-table', 'mem.copy', 'mem.inner'])

    def test_exact_roots_and_stop(self):
        directory = self.root / 'closure'
        directory.mkdir()
        docs = {'demo.read': ['os.linux.read', 'debug.FullPanic(x).call'], 'demo.readAll': ['demo.read'],
                'os.linux.read': ['os.linux.syscall3'], 'os.linux.syscall3': [], 'debug.FullPanic(x).call': [],
                'demo.other': ['mem.unused'], 'mem.unused': []}
        for name, calls in docs.items():
            (directory / (name + '.json')).write_text(json.dumps(document(name, calls)))
        # `demo.read` is exact: `demo.readAll` is no root; the stopped functions and the wrapper
        # below the bound one are neither kept nor followed.
        fx.keep_closure(directory, ['demo.read'], ['os.linux.read', 'debug.FullPanic(*'])
        self.assertEqual(sorted(p.stem for p in directory.glob('*.json')), ['demo.read'])
        with self.assertRaises(fx.Error):
            fx.keep_closure(directory, ['demo.missing'])

    def test_escaped_callee_names(self):
        directory = self.root / 'closure'
        directory.mkdir()
        quoted = 'demo.f("a\\"b")'
        (directory / 'demo.root.json').write_text(json.dumps(document('demo.root', [quoted])))
        (directory / 'callee.json').write_text(json.dumps(document(quoted)))
        fx.keep_closure(directory, ['demo.root'])
        self.assertEqual(sorted(p.stem for p in directory.glob('*.json')), ['callee', 'demo.root'])

    def test_source_outside_the_fixture_is_pinned(self):
        shared = self.root / 'shared'
        shared.mkdir()
        (shared / 'lib.zig').write_text('pub fn add(a: u32) u32 { return a; }\n')
        (shared / 'dep.zig').write_text('pub const x = 1;\n')
        self.write_manifest([dict(self.entry, source='../shared/lib.zig')])
        self.assertEqual(sorted(fx.sources('demo', fx.manifest('demo'))),
                         ['../shared/dep.zig', '../shared/lib.zig', 'demo.zig'])


class Committed(unittest.TestCase):
    def test_every_manifest_checks(self):
        done = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/fixture-exports.py'), 'check'],
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)


if __name__ == '__main__':
    unittest.main()
