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
