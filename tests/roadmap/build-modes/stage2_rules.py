#!/usr/bin/env python3
"""T06: the stage2_x86_64 fail-closed rules (`CheckCtx.checkStage2Backend`) on real exports.

stage2-air/<version>/ holds the patched compilers' exports (`-fno-llvm -target x86_64-linux-gnu
-mcpu=baseline`) of reproducers/stage2-x86_64-divergences.zig's `modF16` (a float `@mod`) and
`setNib` (an `i4` read from a packed union). Each is rejected under its stage2_x86_64 profile
with the rule's message, and the same file with the profile's backend set to stage2_llvm is
accepted: the rule is keyed on the backend, not on the construct.

Usage: stage2_rules.py [AIR2LEAN_BINARY]  (default .lake/build/bin/air2lean)
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
AIR = ROOT / 'tests/roadmap/build-modes/stage2-air'
BINARY = ROOT / '.lake/build/bin/air2lean'
CASES = {'modF16': 'a float `@mod` is outside the stage2_x86_64 profile',
         'setNib': "a read of the signed 4-bit field 'signed' of packed union"}


def diagnose(doc):
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / 'f.json').write_text(json.dumps(doc), encoding='utf-8')
        done = subprocess.run([str(BINARY), '--diagnostics-json', tmp, '--allow-unqualified-build-mode'],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=60)
        return json.loads(done.stdout)


class Stage2Rules(unittest.TestCase):
    def test_versions_present(self):
        self.assertEqual(sorted(p.name for p in AIR.iterdir()), ['0.16.0', '0.17.0'])

    def test_rejected_on_stage2_accepted_on_llvm(self):
        for version in sorted(AIR.iterdir()):
            for name, message in CASES.items():
                with self.subTest(version=version.name, function=name):
                    doc = json.loads((version / f'stage2-x86_64-divergences.{name}.json').read_text())
                    self.assertEqual(doc['profile']['backend'], 'stage2_x86_64')
                    report = diagnose(doc)
                    self.assertEqual(report['status'], 'rejected', report)
                    self.assertTrue(any(message in d['message'] for d in report['diagnostics']), report)
                    doc['profile']['backend'] = 'stage2_llvm'
                    report = diagnose(doc)
                    self.assertEqual(report['status'], 'checked', report)


if __name__ == '__main__':
    if len(sys.argv) > 1:
        BINARY = Path(sys.argv.pop(1)).resolve()
    unittest.main()
