#!/usr/bin/env python3
"""The shared RSS budget normalises units per platform and trips on a real allocation regression."""
import os
from pathlib import Path
import subprocess
import sys
import types
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import rss_budget  # noqa: E402

CHILD = '''
import sys
sys.path.insert(0, {here!r})
import rss_budget
start = rss_budget.baseline()
hold = bytearray({size})
for i in range(0, len(hold), 4096):
    hold[i] = 1  # touch every page so it is resident
rss_budget.enforce(start, 'child')
'''


class RssBudgetTests(unittest.TestCase):
    def run_child(self, size):
        return subprocess.run([sys.executable, '-c', CHILD.format(here=str(HERE), size=size)],
                              capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))

    def test_units_are_normalised_per_platform(self):
        real_usage, real_platform = rss_budget.resource.getrusage, sys.platform
        fake = lambda who: types.SimpleNamespace(ru_maxrss=40 * 1024)
        try:
            rss_budget.resource.getrusage = fake
            sys.platform = 'darwin'
            self.assertEqual(rss_budget.peak_rss_bytes(), 40 * 1024)  # bytes on macOS
            sys.platform = 'linux'
            self.assertEqual(rss_budget.peak_rss_bytes(), 40 * 1024 * 1024)  # KiB on Linux
        finally:
            rss_budget.resource.getrusage, sys.platform = real_usage, real_platform

    def test_baseline_is_a_plausible_bare_interpreter(self):
        self.assertTrue(4 * rss_budget.MIB < rss_budget.baseline() < 32 * rss_budget.MIB)

    def test_small_allocation_passes(self):
        result = self.run_child(4 * rss_budget.MIB)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_deliberately_large_allocation_trips_budget(self):
        result = self.run_child(rss_budget.GROWTH_BUDGET + 16 * rss_budget.MIB)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('RSS growth exceeded', result.stderr)


if __name__ == '__main__':
    unittest.main()
