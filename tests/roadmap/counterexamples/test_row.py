#!/usr/bin/env python3
"""P08 row replay: a sequential differential case of any shape, replayed by the production runners.

`Fakes` drives the replay with stand-in `zig` and `difftest` programs (request shapes, scratch
inputs, staleness, every failure mapping and the verdicts). `Real` runs the committed example
harnesses (`tests/diff/<ex>/harness.zig`) and the built Lean runner (`tests/diff/.lake/build/bin/difftest`)
on memory and slice functions; it is skipped without a stock `zig` and a built `difftest`.

    AIR2LEAN_ZIG=/path/to/zig python3 -I -B tests/roadmap/counterexamples/test_row.py
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('air2lean_counterexample', ROOT/'scripts/counterexample.py')
CX = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(CX)
ZIG = os.environ.get('AIR2LEAN_ZIG', shutil.which('zig') or 'zig')
DIFFTEST = ROOT/'tests/diff/.lake/build/bin/difftest'

FAKE_ZIG = '''#!{python}
import pathlib, sys
args = sys.argv[1:]
if args[0] == 'version': print('0.16.0'); sys.exit(0)
if {build_fails}: print('error: boom', file=sys.stderr); sys.exit(1)
out = pathlib.Path(next(a for a in args if a.startswith('-femit-bin='))[len('-femit-bin='):])
out.write_text(pathlib.Path(__file__).with_name('fake-harness.py').read_text()); out.chmod(0o755)
'''
# The fake harness and fake Lean runner write one output line per function that has a non-empty input.
FAKE_RUNNER = '''#!{python}
import pathlib
side, line = {side!r}, pathlib.Path({line_file!r}).read_text()
for path in pathlib.Path('tests/diff').glob('*/inputs/*.jsonl'):
    if path.read_text().strip():
        out = pathlib.Path('tests/diff/out') / side / path.parent.parent.name
        out.mkdir(parents=True, exist_ok=True)
        (out / path.name).write_text(line + '\\n')
'''


class Fakes(unittest.TestCase):
    NATIVE, MODEL = '{"ok":{"s":"x"},"bufs":[[1,2]]}', '{"ok":{"s":"x"},"bufs":[[1,2]]}'

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for path, text in [('tests/diff/demo/harness.zig', '// harness\n'), ('examples/demo/demo.zig', '// demo\n'),
                           ('tests/diff/common.zig', '// common\n'), ('tests/diff/demo/inputs/f.jsonl', '{"bufs":[[1,2]],"args":[]}\n[7]\n'),
                           ('tests/diff/demo/inputs/g.jsonl', '[1]\n')]:
            p = self.root/path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        self.tools = Path(self.temp.name + '-tools'); self.tools.mkdir(); self.addCleanup(shutil.rmtree, self.tools, True)
        self.lines = {'zig': self.NATIVE, 'lean': self.MODEL}
        self.write_tools()

    def write_tools(self, build_fails=False, lean_missing=False):
        zig = self.tools/'zig'
        zig.write_text(FAKE_ZIG.format(python=sys.executable, build_fails=build_fails)); zig.chmod(0o755)
        (self.tools/'fake-harness.py').write_text(
            FAKE_RUNNER.format(python=sys.executable, side='zig', line_file=str(self.tools/'zig-line')))
        (self.tools/'zig-line').write_text(self.lines['zig'])
        lean = self.tools/'difftest'
        lean.write_text(FAKE_RUNNER.format(python=sys.executable, side='lean', line_file=str(self.tools/'lean-line'))); lean.chmod(0o755)
        (self.tools/'lean-line').write_text(self.lines['lean'])
        self.zig, self.difftest = str(zig), (self.tools/'missing' if lean_missing else lean)

    def request(self, index=1):
        return CX.diff_row_request(self.root, 'demo', 'f', index, self.NATIVE, self.MODEL)

    def confirm(self, index=1):
        return CX.diff_row_confirm(self.root, CX.diff_row_block(self.request(index)), self.zig, self.difftest, 60)

    def test_request_shape_and_unsupported_examples(self):
        request = self.request()
        self.assertEqual((request['example'], request['function'], request['row']), ('demo', 'f', '{"bufs":[[1,2]],"args":[]}'))
        self.assertEqual(request['row_sha256'], hashlib.sha256((request['row'] + '\n').encode()).hexdigest())   # as input_sha256
        self.assertIsNone(CX.diff_row_request(self.root, 'nope', 'f', 1, '', ''))                # no harness
        self.assertIsNone(CX.diff_row_request(self.root, 'demo', 'missing', 1, '', ''))          # no inputs for the function
        self.assertIsNone(CX.diff_row_request(self.root, 'demo/../x', 'f', 1, '', ''))           # not an identifier
        with self.assertRaises(CX.Invalid): self.request(9)                                      # no such row

    def test_both_fresh_lines_must_equal_the_recorded_ones(self):
        outcome = self.confirm()
        self.assertEqual(outcome['status'], 'verified')
        self.assertEqual(outcome['observed'], dict(native_line=self.NATIVE, model_line=self.MODEL))
        for side in ('zig', 'lean'):
            with self.subTest(side=side):
                self.lines[side] = '{"ok":{"s":"y"}}'
                self.write_tools()
                self.assertEqual(self.confirm()['status'], 'not_reproduced')    # a model or host difference, never a bug
                self.lines[side] = self.NATIVE

    def test_runs_only_the_selected_row_of_the_selected_function(self):
        seen = self.tools/'seen'
        (self.tools/'fake-harness.py').write_text(
            FAKE_RUNNER.format(python=sys.executable, side='zig', line_file=str(self.tools/'zig-line'))
            + f"import json\npathlib.Path({str(seen)!r}).write_text(json.dumps({{p.name: p.read_text() for p in pathlib.Path('tests/diff/demo/inputs').glob('*.jsonl')}}))\n")
        self.confirm(2)
        self.assertEqual(json.loads(seen.read_text()), {'f.jsonl': '[7]\n', 'g.jsonl': ''})   # other functions run nothing

    def test_failures_map_to_setup_not_to_bugs(self):
        self.write_tools(build_fails=True)
        self.assertEqual(self.confirm()['status'], 'error')
        self.write_tools(lean_missing=True)
        outcome = self.confirm()
        self.assertEqual(outcome['status'], 'unavailable'); self.assertIn('difftest', outcome['detail'])
        self.write_tools()
        self.assertEqual(CX.diff_row_confirm(self.root, CX.diff_row_block(self.request()), '/nonexistent/zig', self.difftest, 60)['status'],
                         'unavailable')
        self.lines['zig'] = ''
        self.write_tools(); (self.tools/'fake-harness.py').write_text('#!/bin/sh\nexit 3\n')
        self.assertEqual(self.confirm()['status'], 'error')

    def test_stale_sources_or_rows_are_refused(self):
        block = CX.diff_row_block(self.request())
        (self.root/'examples/demo/demo.zig').write_text('// edited\n')
        self.assertEqual(CX.diff_row_confirm(self.root, block, self.zig, self.difftest, 60)['status'], 'error')
        (self.root/'examples/demo/demo.zig').write_text('// demo\n')
        self.assertEqual(CX.diff_row_confirm(self.root, block, self.zig, self.difftest, 60)['status'], 'verified')
        (self.root/'tests/diff/demo/inputs/f.jsonl').write_text('{"bufs":[[9]],"args":[]}\n[7]\n')
        outcome = CX.diff_row_confirm(self.root, block, self.zig, self.difftest, 60)
        self.assertEqual((outcome['status'], outcome['detail']), ('error', 'the input row changed'))

    def test_from_case_uses_the_row_replay_for_shapes_the_lean_goal_search_cannot_express(self):
        REPORT = CX.REPORT
        native, model = '{"ok":5,"bufs":[[2,1]]}', '{"ok":6,"bufs":[[2,1]]}'      # a value mismatch on a buffer function
        self.lines.update(zig=native, lean=model); self.write_tools()
        summary, lines = self.root/'report.json', {}
        for side, line in (('zig', native), ('lean', model)):
            p = self.root/'tests/diff/out'/side/'demo/f.jsonl'; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(line + '\n')
            lines[side] = hashlib.sha256((line + '\n').encode()).hexdigest()
        raw = '{"bufs":[[1,2]],"args":[]}\n'
        row = dict(schema=1, example='demo', function='f', input_index=1, input_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                   native_kind='value', model_kind='value', native_sha256=lines['zig'], model_sha256=lines['lean'],
                   status='mismatch', legacy_bucket='x')
        Path(str(summary) + '.jsonl').write_text(json.dumps(row) + '\n')
        summary.write_text(json.dumps(dict(schema=1, complete=True, qualified=False, runner_runtime_sources=REPORT.source_hashes(self.root))))
        unreplayed = CX.case_bundle(self.root, summary, 'demo', 'f', 1, zig=self.zig, difftest=self.difftest)
        self.assertEqual((unreplayed['classification'], unreplayed['replay']['kind'], unreplayed['replay']['status']),
                         ('candidate', 'diff_row', 'not_run'))
        replayed = CX.case_bundle(self.root, summary, 'demo', 'f', 1, replay=True, zig=self.zig, difftest=self.difftest)
        self.assertEqual((replayed['classification'], replayed['reason'], replayed['replay']['status']),
                         ('counterexample', 'replayed_failure', 'verified'))
        self.assertTrue(replayed['is_program_bug_evidence'])
        bundle = self.root/'bundle.json'
        REPORT.atomic_json(bundle, replayed)
        self.assertEqual(CX.replay_bundle(self.root, bundle, None, 60, self.zig, self.difftest), 0)
        # The host disagrees on a rerun (here the native side): unsolved, never a program bug.
        self.lines['zig'] = '{"ok":9,"bufs":[[2,1]]}'; self.write_tools()
        again = CX.case_bundle(self.root, summary, 'demo', 'f', 1, replay=True, zig=self.zig, difftest=self.difftest)
        self.assertEqual((again['classification'], again['reason']), ('unsolved', 'replay_not_reproduced'))
        self.assertFalse(again['is_program_bug_evidence'])
        REPORT.atomic_json(bundle, again)
        self.assertEqual(CX.replay_bundle(self.root, bundle, None, 60, self.zig, self.difftest), 1)

    def test_verdicts(self):
        self.assertEqual(CX.verdict(status='mismatch', replay='verified')[:2], ('counterexample', 'replayed_failure'))
        self.assertEqual(CX.verdict(status='mismatch', replay='not_reproduced')[:2], ('unsolved', 'replay_not_reproduced'))
        self.assertEqual(CX.verdict(status='mismatch', replay='unavailable')[:2], ('candidate', 'failure_not_replayed'))
        self.assertEqual(CX.verdict(status='mismatch', replay='error')[:2], ('setup_failure', 'replay_error'))


@unittest.skipUnless(DIFFTEST.is_file() and shutil.which(ZIG), 'needs a stock zig and `(cd tests/diff && lake build difftest)`')
class Real(unittest.TestCase):
    """The committed harnesses, on functions that use memory buffers (slices) and plain integers (basic)."""

    def setUp(self):
        version = subprocess.run([ZIG, 'version'], capture_output=True, text=True).stdout.strip()
        self.version = version

    def eligible(self, example):
        """The default example selection of scripts/example-selection.sh: `zig-versions` lists the Zig versions."""
        listed = ROOT/'examples'/example/'zig-versions'
        if listed.is_file() and self.version not in listed.read_text().split():
            self.skipTest(f'{example} is not built with Zig {self.version}')

    def lines(self, example, function, index):
        request = CX.diff_row_request(ROOT, example, function, index, '', '')
        status, detail, native, model = CX.run_row(ROOT, request, ZIG, DIFFTEST, 600)
        self.assertEqual(status, 'ok', detail)
        return native, model

    def check(self, example, function, index):
        native, model = self.lines(example, function, index)
        request = CX.diff_row_request(ROOT, example, function, index, native, model)
        block = CX.diff_row_block(request)
        outcome = CX.diff_row_confirm(ROOT, block, ZIG, DIFFTEST, 600)
        self.assertEqual(outcome['status'], 'verified', outcome)
        # The recorded model line is the part a forged or stale record would change.
        forged = CX.diff_row_block(dict(request, model_line='{"ok":"forged"}'))
        self.assertEqual(CX.diff_row_confirm(ROOT, forged, ZIG, DIFFTEST, 600)['status'], 'not_reproduced')
        return native, model

    def test_a_memory_function_with_buffers_replays(self):
        self.eligible('slices')
        native, model = self.check('slices', 'reverse', 1)
        self.assertIn('"bufs"', native)            # the shape the Lean goal search cannot express
        self.assertIn('"bufs"', model)

    def test_a_safety_panic_of_a_memory_function_replays(self):
        self.eligible('slices')
        native, model = self.check('slices', 'sumMid', 1)
        self.assertEqual(native, '{"fail":"integerOverflow"}')    # the harness's panic kind ...
        self.assertEqual(model, '{"fail":"Zig.Error.overflow"}')  # ... and the model's constructor

    def test_a_plain_integer_function_replays(self):
        self.eligible('basic')
        native, model = self.check('basic', 'absDiff', 3)
        self.assertEqual(CX.native_matches(native, model), True)


if __name__ == '__main__':
    unittest.main()
