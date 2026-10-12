#!/usr/bin/env python3
"""Negative tests of the weak-ordering check (scripts/weak-ordering.py check, Litmus.lean): an
outcome the model forbids, a missing or duplicated test line and an unknown test fail; an
observed load-buffering outcome is reported as a rejected shape, never as a match."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
OBSERVED = sorted((ROOT / 'tests/roadmap/weak-ordering/observed').glob('*.txt'))


def check(text):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'observed.txt'
        path.write_text(text, encoding='utf-8')
        done = subprocess.run([sys.executable, 'scripts/weak-ordering.py', 'check', str(path)],
                              cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        return done.returncode, done.stdout + done.stderr


def mutate(line_prefix, extra):
    base = OBSERVED[0].read_text(encoding='utf-8').splitlines()
    return ''.join((line + extra if line.startswith(line_prefix) else line) + '\n' for line in base)


class WeakOrdering(unittest.TestCase):
    def test_committed_observations_pass(self):
        done = subprocess.run([sys.executable, 'scripts/weak-ordering.py', 'check',
                               *map(str, OBSERVED)], cwd=ROOT)
        self.assertEqual(done.returncode, 0)

    def test_forbidden_outcomes_fail(self):
        for prefix, outcome in (('litmus mp release_acquire ', '10'), ('litmus corr relaxed ', '21'),
                                ('litmus wrc release_acquire ', '110')):
            code, out = check(mutate(prefix, f' {outcome}:1'))
            self.assertEqual(code, 1, prefix)
            self.assertIn('is not a model outcome', out)

    def test_load_buffering_is_a_rejected_shape(self):
        code, out = check(mutate('litmus lb relaxed ', ' 11:1'))
        self.assertEqual(code, 0)
        self.assertIn('rejected shape (not a match)', out)

    def test_missing_duplicate_and_unknown_lines_fail(self):
        base = OBSERVED[0].read_text(encoding='utf-8')
        lines = base.splitlines(keepends=True)
        missing = ''.join(l for l in lines if not l.startswith('litmus sb seq_cst '))
        self.assertIn('no line for sb seq_cst', check(missing)[1])
        dup = base + next(l for l in lines if l.startswith('litmus mp relaxed '))
        self.assertIn('more than one line for mp relaxed', check(dup)[1])
        self.assertIn('unknown test', check(base + 'litmus zz relaxed rounds 1 00:1\n')[1])


if __name__ == '__main__':
    unittest.main()
