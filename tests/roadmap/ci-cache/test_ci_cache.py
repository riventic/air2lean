#!/usr/bin/env python3
"""scripts/ci-cache.py: per-version patched-compiler keys and the main-only prune plan. Offline."""
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location('ci_cache', ROOT / 'scripts/ci-cache.py')
cc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cc)


class ZigAirKey(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='air2lean ci-cache ')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        shutil.copytree(ROOT / 'zig-patch', self.root / 'zig-patch')

    def key(self, version='0.16.0', **kw):
        return cc.zig_air_key(self.root, version, environ={'RUNNER_OS': 'Linux', 'RUNNER_ARCH': 'X64'}, **kw)

    def edit(self, rel, old, new):
        path = self.root / rel
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def test_inputs_of_the_version_change_the_key(self):
        first = self.key()
        self.assertTrue(first.startswith('zig-air-Linux-X64-0.16.0-'))
        (self.root / 'zig-patch/0.16.0/hook.patch').write_text('changed\n')
        self.assertNotEqual(self.key(), first)

    def test_other_versions_pins_do_not(self):
        first = self.key()
        self.edit('zig-patch/versions.toml', 'llvm = "19"', 'llvm = "18"')  # 0.14.1's table
        (self.root / 'zig-patch/0.15.2/hook.patch').write_text('changed\n')
        self.assertEqual(self.key(), first)
        self.edit('zig-patch/versions.toml', 'llvm = "21"', 'llvm = "20"')  # 0.16.0's table
        self.assertNotEqual(self.key(), first)

    def test_host_pin_and_shared_sources_change_the_key(self):
        first = self.key()
        self.assertNotEqual(self.key(host_pin='aarch64-macos abc'), first)
        (self.root / 'zig-patch/air-json/json.zig').write_text('changed\n')
        self.assertNotEqual(self.key(), first)


class Prune(unittest.TestCase):
    def entry(self, id_, key, ref='refs/heads/main', created='2026-10-11T10:00:00Z'):
        return {'id': id_, 'key': key, 'ref': ref, 'created_at': created, 'size_in_bytes': 1}

    def test_keeps_only_the_newest_main_entry_per_prefix(self):
        entries = [
            self.entry(1, 'lake-root-' + 'a' * 64 + '-' + 'b' * 64, created='2026-10-11T09:00:00Z'),
            self.entry(2, 'lake-root-' + 'a' * 64 + '-' + 'c' * 64, created='2026-10-11T11:00:00Z'),
            self.entry(3, 'zig-air-Linux-X64-0.16.0-' + 'd' * 64),
            self.entry(4, 'zig-air-Linux-X64-0.17.0-' + 'd' * 64),
            self.entry(5, 'lake-root-' + 'a' * 64 + '-' + 'e' * 64, ref='refs/pull/9/merge',
                       created='2026-10-11T12:00:00Z'),
            self.entry(6, 'zig-diff-Linux-0.16.0-Debug-' + 'f' * 64, ref='refs/heads/gh-readonly-queue/main/pr-9'),
        ]
        self.assertEqual(sorted(e['id'] for e in cc.plan_prune(entries)), [1, 5, 6])
        self.assertEqual(cc.prefix('zig-diff-macOS-0.15.2-golden-' + 'f' * 64), 'zig-diff-macOS-0.15.2-golden')


if __name__ == '__main__':
    unittest.main()
