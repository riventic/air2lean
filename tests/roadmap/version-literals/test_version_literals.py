#!/usr/bin/env python3
"""scripts/version-literals.py: the committed tree passes, and each kind of drift fails."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts' / 'version-literals.py'


def run(root):
    return subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(root)],
                          capture_output=True, text=True, timeout=60)


class VersionLiterals(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix='version-literals-'))
        shutil.copytree(ROOT / 'Air2Lean', self.tmp / 'Air2Lean')
        shutil.copy(ROOT / 'Air2Lean.lean', self.tmp)
        shutil.copy(ROOT / 'compatibility.json', self.tmp)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def write(self, rel, text):
        (self.tmp / rel).write_text(text, encoding='utf-8')

    def test_committed_tree_passes(self):
        result = run(self.tmp)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_version_comparison_outside_registry_fails(self):
        self.write('Air2Lean/Extra.lean',
                   'def old (v : String) : Bool := v == "0.16.0" || v == "0.17"\n')
        result = run(self.tmp)
        self.assertEqual(result.returncode, 1)
        self.assertIn('Air2Lean/Extra.lean:1: Zig version literal "0.16.0"', result.stderr)
        self.assertIn('Air2Lean/Extra.lean:1: Zig version literal "0.17"', result.stderr)

    def test_escaped_quote_char_does_not_hide_a_literal(self):
        self.write('Air2Lean/Extra.lean',
                   "def q : Char := '\\\"'\n"
                   'def old (v : String) : Bool := v == "0.17.0"\n')
        result = run(self.tmp)
        self.assertEqual(result.returncode, 1)
        self.assertIn('Air2Lean/Extra.lean:2: Zig version literal "0.17.0"', result.stderr)

    def test_comments_and_prose_are_not_keys(self):
        self.write('Air2Lean/Extra.lean',
                   '/-! Zig "0.17.0" in a module doc. /- nested "0.16.0" -/ -/\n'
                   '-- a comment: "0.15.2"\n'
                   'def msg : String := s!"Zig 0.17.0 renamed it \\\n  (since 0.17.0)"\n'
                   "def quote : Char := '\"'\n"
                   'def path : String := "air/0.16.0/x.json"\n')
        result = run(self.tmp)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_registry_must_match_compatibility(self):
        compat = json.loads((self.tmp / 'compatibility.json').read_text())
        compat['zig']['versions'] = compat['zig']['versions'][1:]
        self.write('compatibility.json', json.dumps(compat))
        result = run(self.tmp)
        self.assertEqual(result.returncode, 1)
        self.assertIn('differs from compatibility.json', result.stderr)

    def test_missing_registry_fails(self):
        (self.tmp / 'Air2Lean/Air/Dialect.lean').unlink()
        result = run(self.tmp)
        self.assertEqual(result.returncode, 1)
        self.assertIn('Air2Lean/Air/Dialect.lean: missing', result.stderr)


if __name__ == '__main__':
    unittest.main()
