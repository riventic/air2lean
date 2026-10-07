#!/usr/bin/env python3
"""Offline regressions for scripts/vc-report.py (P02). No Lean, Lake or Zig is run."""
import json
from pathlib import Path
import runpy
import sys
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
VC = runpy.run_path(str(ROOT / 'scripts/vc-report.py'))
GOLDEN = json.loads((Path(__file__).parent / 'report.json').read_text())


def message(data, severity='information'):
    return {'severity': severity, 'data': data}


def logged(report):
    return message(VC['PREFIX'] + json.dumps(report))


class ReportTests(unittest.TestCase):
    def test_lean_errors_are_surfaced_and_reports_are_not_errors(self):
        messages = [message('unknown constant Basic.missing', 'error'),
                    logged({'function': 'Basic.f', 'status': 'extracted', 'program': 'ResultProgram'}),
                    message(VC['PREFIX'] + json.dumps({'function': 'Basic.g', 'status': 'refused',
                                                       'reason': 'no contract'}), 'error')]
        self.assertEqual(VC['lean_errors'](messages), ['unknown constant Basic.missing'])
        self.assertEqual([r['function'] for r in VC['reports'](messages)], ['Basic.f', 'Basic.g'])

    def test_open_obligations_are_counted_and_closed_ones_named(self):
        report = next(r for r in GOLDEN if r['function'] == 'Basic.tardiness' and r['status'] == 'obligations')
        lines = VC['describe'](report)
        self.assertEqual(lines[0], 'Basic.tardiness: 3 obligations (safety 1, result 2); 3 open')
        closed = dict(report, obligations=[dict(report['obligations'][0], closed_by='pts hypothesis')]
                      + report['obligations'][1:])
        self.assertEqual(VC['describe'](closed)[0],
                         'Basic.tardiness: 3 obligations (safety 1, result 2); 2 open')
        self.assertIn('(closed by pts hypothesis)', '\n'.join(VC['describe'](closed)))

    def test_loop_request_names_loop_and_instruction_without_an_invariant(self):
        report = next(r for r in GOLDEN if r['status'] == 'loop-request')
        lines = VC['describe'](report)
        self.assertIn('no invariant is guessed', lines[0])
        for request, line in zip(report['requests'], lines[1:]):
            self.assertIn(request['loop'], line)
            self.assertIn('invariant + variant required', line)

    def test_every_golden_report_is_described(self):
        for report in GOLDEN:
            self.assertTrue(VC['describe'](report)[0].startswith(report['function'] + ': '))


if __name__ == '__main__':
    unittest.main()
