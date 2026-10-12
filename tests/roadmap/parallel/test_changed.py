#!/usr/bin/env python3
"""scripts/changed-examples.py and its use by scripts/example-selection.sh: a path selects its own
example, documentation none, anything else every example. Offline: no git history is needed."""
import importlib.util
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('changed', ROOT / 'scripts/changed-examples.py')
changed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(changed)
EXAMPLES = ['basic', 'floats', 'sync']


class Affected(unittest.TestCase):
    def test_paths(self):
        cases = [
            (['docs/build-cache.md', 'README.md'], []),
            (['examples/basic/basic.zig', 'tests/diff/basic/harness.zig'], ['basic']),
            (['tests/golden/0.16.0/floats/air/x.json', 'Proofs/Sync/Proofs.lean'], ['floats', 'sync']),
            (['tests/golden/floats/air/a.json'], ['floats']),
            (['tests/diff/common.zig'], EXAMPLES),
            (['tests/diff/Diff.lean'], EXAMPLES),
            (['examples/basic/basic.zig', 'scripts/check.sh'], EXAMPLES),
            (['examples/unknown/unknown.zig'], EXAMPLES),
            (['Proofs/Basic.lean'], EXAMPLES),
        ]
        for paths, expected in cases:
            with self.subTest(paths=paths):
                self.assertEqual(changed.affected(paths, EXAMPLES), expected)

    def test_a_rename_selects_the_source_example(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            def git(*a):
                return subprocess.run(['git', '-C', d, '-c', 'user.name=t', '-c', 'user.email=t@t', *a],
                                      check=True, capture_output=True, text=True).stdout
            git('init', '-q')
            (Path(d) / 'examples/basic').mkdir(parents=True)
            (Path(d) / 'examples/basic/basic.zig').write_text('pub fn f() void {}\n' * 20)
            git('add', '.')
            git('commit', '-qm', 'a')
            (Path(d) / 'examples/floats').mkdir()
            git('mv', 'examples/basic/basic.zig', 'examples/floats/floats.zig')
            old, root = changed.ROOT, changed.ROOT
            changed.ROOT = Path(d)
            try:
                paths = changed.changed_paths('HEAD')
            finally:
                changed.ROOT = old
            self.assertIn('examples/basic/basic.zig', paths)
            self.assertEqual(changed.affected(paths, EXAMPLES), ['basic', 'floats'])

    def test_default_selection_without_the_variable_is_unchanged(self):
        env = {k: v for k, v in os.environ.items() if k != 'AIR2LEAN_CHANGED_FROM'}
        script = f'source {ROOT}/scripts/example-selection.sh; air2lean_default_examples {ROOT} 0.16.0 x86_64'
        out = subprocess.run(['bash', '-c', script], env=env, capture_output=True, text=True, check=True).stdout
        self.assertIn('basic ', out)
        self.assertIn('asm ', out)
        # HEAD against itself: only uncommitted changes count; the selection is a subset.
        out2 = subprocess.run(['bash', '-c', script], env=dict(env, AIR2LEAN_CHANGED_FROM='HEAD'),
                              capture_output=True, text=True, check=True).stdout
        self.assertTrue(set(out2.split()) <= set(out.split()))


if __name__ == '__main__':
    unittest.main(verbosity=2)
