#!/usr/bin/env python3
"""P08 end-to-end on the real atomics model: needs a built `schedules` executable.

Usage: test_e2e.py [path/to/schedules]  (default tests/diff/.lake/build/bin/schedules)
Runs the real search, bundle and replay CLI; the relaxed message-passing race must replay,
while release/acquire, fuel exhaustion, a node cap and a timeout are never counterexamples.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
BINARY = ROOT/'tests/diff/.lake/build/bin/schedules'
if __name__ == '__main__' and len(sys.argv) > 1 and not sys.argv[1].startswith('-'):
    BINARY = Path(sys.argv.pop(1)).resolve()


def cli(*argv):
    return subprocess.run([sys.executable, '-B', str(ROOT/'scripts/counterexample.py'), *argv, '--binary', str(BINARY)],
                          cwd=ROOT, capture_output=True, text=True, timeout=900)


@unittest.skipUnless(BINARY.is_file(), f'missing {BINARY}; run `(cd tests/diff && lake build schedules)`')
class EndToEnd(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.dir = Path(self.temp.name)

    def search(self, function, *extra):
        out = self.dir/f'{function}-{len(extra)}.json'
        result = cli('search', '--example', 'atomics', '--function', function, *extra, '--output', str(out))
        self.assertEqual(result.returncode, 0, result.stderr)
        return out, json.loads(out.read_text())

    def test_relaxed_message_passing_race_replays(self):
        out, data = self.search('mpRelaxed', '--node-cap', '64')
        self.assertEqual((data['classification'], data['observed']['kind'], data['replay']['status']),
                         ('counterexample', 'illegal', 'verified'))
        self.assertEqual(data['contract']['id'], 'no_illegal_behaviour')
        sites = {(s['function'], s['zig_line']) for s in data['location']['candidate_sites']}
        self.assertIn(('atomics.mpRelaxed', 43), sites); self.assertIn(('atomics.mpWriterRelaxed', 20), sites)
        result = cli('replay', '--bundle', str(out))
        self.assertEqual(result.returncode, 0, result.stderr); self.assertIn('status=verified', result.stdout)

    def test_limits_and_clean_trees_are_not_counterexamples(self):
        for function, extra, expected in [('mpRelAcq', (), ('no_failure', 'no_failing_execution_in_bounded_tree')),
                                          ('mpRelaxed', ('--fuel', '2'), ('unsolved', 'bounded_no_result')),
                                          ('mpRelaxed', ('--node-cap', '1'), ('unsolved', 'enumeration_truncated')),
                                          ('stackPush', ('--node-cap', '2000', '--timeout', '1'), ('unsolved', 'timeout'))]:
            with self.subTest(function=function, extra=extra):
                out, data = self.search(function, *extra)
                self.assertEqual((data['classification'], data['reason']), expected)
                self.assertFalse(data['is_program_bug_evidence'])
                self.assertNotEqual(cli('replay', '--bundle', str(out)).returncode, 0)


if __name__ == '__main__':
    unittest.main()
