#!/usr/bin/env python3
"""P08 Lean goal-failure counterexamples and Zig-free sequential replay.

Unit tests mock the Lean process. The end-to-end class translates a seeded loop (correct and
off-by-one AIR from loopsum.py) with the built `air2lean`, evaluates it with `lake env lean --run`
and needs no Zig; it is skipped when `.lake/build/bin/air2lean` is absent.
"""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import importlib.util
import loopsum

ROOT = loopsum.ROOT
SPEC = importlib.util.spec_from_file_location('air2lean_counterexample', ROOT/'scripts/counterexample.py')
CX = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(CX)
EVAL = CX.EVAL
AIR2LEAN = ROOT/'.lake/build/bin/air2lean'

FAKE_GEN = '''import ZigLean
namespace Fake
def flip (p0 : Bool) : Zig.Result (Bool) := do
  pure (!p0)
end Fake
'''
SPEC_TEXT = 'r = .ok (!p0)'


def fake_runner(*lines, sleep=0, code=0):
    body = f'import sys,time;time.sleep({sleep});print({chr(10).join(lines)!r});sys.exit({code})'
    return (sys.executable, '-c', body)


class Mocked(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.gen = self.root/'Gen.lean'; self.gen.write_text(FAKE_GEN)

    def goal(self, runner, **kw):
        return CX.goal_bundle(self.root, 'fake', 'flip', SPEC_TEXT, gen=self.gen, runner=runner, replay=False, **kw)

    def test_signature_and_unsupported_shapes(self):
        params, ret = EVAL.signature(FAKE_GEN, 'flip')
        self.assertEqual((params, ret), ([('p0', ('bool', 1))], ('bool', 1)))
        with self.assertRaises(EVAL.Unsupported): EVAL.signature('def g (p0 : Zig.Ptr) : Zig.MemM (Unit) := do\n', 'g')
        data = CX.goal_bundle(self.root, 'fake', 'missing', SPEC_TEXT, gen=self.gen, replay=False)
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'unsupported'))

    def test_exhausted_complete_domain_is_clean_and_bounded_search_is_unsolved(self):
        data = self.goal(fake_runner('S\t2\t0\t0\t0'))
        self.assertEqual((data['classification'], data['reason']), ('no_failure', 'exhaustive_domain_no_violation'))
        self.assertTrue(data['source']['exhaustive_domain'])
        big = self.root/'Big.lean'
        big.write_text(FAKE_GEN.replace('Bool', 'BitVec 32').replace('!p0', 'p0'))
        data = CX.goal_bundle(self.root, 'fake', 'flip', 'r = .ok p0', gen=big, runner=fake_runner('S\t4096\t0\t0\t0'), replay=False)
        self.assertEqual((data['classification'], data['reason'], data['is_program_bug_evidence']), ('unsolved', 'search_exhausted', False))

    def test_limits_are_unsolved_never_program_bugs(self):
        for runner, kw, expected in [(fake_runner(sleep=30), dict(timeout=1), ('unsolved', 'timeout')),
                                     (fake_runner('N\t0', 'S\t1\t0\t1\t0'), {}, ('unsolved', 'bounded_no_result')),
                                     (fake_runner('S\t0\t2\t0\t0'), {}, ('unsolved', 'no_input_satisfies_precondition')),
                                     (fake_runner('boom', code=1), {}, ('setup_failure', 'lean_error'))]:
            with self.subTest(expected=expected):
                data = self.goal(runner, **kw)
                self.assertEqual((data['classification'], data['reason']), expected)
                self.assertFalse(data['is_program_bug_evidence'])

    def test_timeout_kills_the_whole_process_group(self):
        pidfile = self.root/'child.pid'
        runner = ('sh', '-c', f'sleep 60 & echo $! > {pidfile}; wait')   # like `lake` forking `lean`
        out = EVAL.run(self.root, self.gen, '', timeout=2, runner=runner)
        self.assertEqual(out['status'], 'timeout')
        pid = int(pidfile.read_text())
        for _ in range(50):
            try: os.kill(pid, 0)
            except ProcessLookupError: break
            time.sleep(0.1)
        else:
            os.kill(pid, 9); self.fail('the evaluator child survived the timeout')

    def test_unreplayed_violation_is_only_a_candidate(self):
        data = self.goal(fake_runner('V\t1\t{"ok":1}', 'S\t2\t0\t0\t1'))
        self.assertEqual((data['classification'], data['reason']), ('candidate', 'failure_not_replayed'))
        self.assertFalse(data['is_program_bug_evidence'])
        self.assertEqual((data['input'], data['contract']['id'], data['replay']['kind']), ([True], 'postcondition', 'lean_sequential'))

    def test_replay_that_does_not_reproduce_is_unsolved(self):
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":1}', gen=self.gen, spec=SPEC_TEXT)
        for lines, status in [(('O\t0\t{"ok":0}',), 'not_reproduced'),            # spec now holds / other value
                              (('O\t0\t{"ok":1}', 'V\t0\t{"ok":1}'), 'verified')]:
            self.assertEqual(CX.lean_confirm(self.root, request, 30, fake_runner(*lines))['status'], status)
        self.gen.write_text(FAKE_GEN + '-- edited\n')
        self.assertEqual(CX.lean_confirm(self.root, request, 30, fake_runner())['status'], 'error')  # stale source

    def test_driver_reads_inputs_as_unsigned_values(self):
        rows, exhaustive = EVAL.inputs([('bv', 8)], 4096, 0)
        self.assertTrue(exhaustive); self.assertEqual(len(rows), 256); self.assertEqual(rows[0], (0,))
        rows, exhaustive = EVAL.inputs([('bv', 32), ('bv', 32)], 100, 7)
        self.assertFalse(exhaustive); self.assertLessEqual(len(rows), 100)
        self.assertEqual(EVAL.inputs([('bv', 32), ('bv', 32)], 100, 7), (rows, False))  # seeded, deterministic
        self.assertEqual(EVAL.to_signed(255, ('bv', 8), True), -1)


FAKE_ZIG = '''#!{python}
import pathlib, sys
args = sys.argv[1:]
if args[0] == 'version': print('0.16.0'); sys.exit(0)
if {build_fails}: print('error: boom', file=sys.stderr); sys.exit(1)
out = pathlib.Path(next(a for a in args if a.startswith('-femit-bin='))[len('-femit-bin='):])
out.write_text(pathlib.Path(__file__).with_name('fake-harness.py').read_text()); out.chmod(0o755)
'''
FAKE_HARNESS = '''#!{python}
import pathlib
line = pathlib.Path({line_file!r}).read_text()
target = pathlib.Path('tests/diff/out/zig/target'); target.mkdir(parents=True, exist_ok=True)
(target/'flip.jsonl').write_text(line + '\\n')
'''
NATIVE_SRC = 'export fn flip(a: bool) bool {\n    return !a;\n}\n'


class NativeReplay(unittest.TestCase):
    """The Zig-side replay with a fake `zig`: request shapes, comparison rules and failure mapping."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'tests/diff').mkdir(parents=True); (self.root/'tests/diff/common.zig').write_text('')
        self.gen = self.root/'Gen.lean'; self.gen.write_text(FAKE_GEN)
        self.src = self.root/'flip.zig'; self.src.write_text(NATIVE_SRC)

    def zig(self, line='{"ok":0}', build_fails=False):
        """A fake stock zig whose harness prints `line`; it replaces the previous fake."""
        path = self.root/'fake-zig'
        path.write_text(FAKE_ZIG.format(python=sys.executable, build_fails=build_fails)); path.chmod(0o755)
        (self.root/'fake-line').write_text(line)
        (self.root/'fake-harness.py').write_text(FAKE_HARNESS.format(python=sys.executable, line_file=str(self.root/'fake-line')))
        return str(path)

    def request(self, **kw):
        params, ret = EVAL.signature(FAKE_GEN, 'flip')
        return CX.native_request(self.root, kw.pop('source', self.src), 'flip', [True], params, ret, None)

    def test_request_shapes(self):
        request = self.request()
        self.assertEqual((request['decl'], request['params'], request['ret'], request['args']), ('export', ['bool'], 'bool', [True]))
        text = CX.harness_text(request)
        self.assertIn('extern fn flip(p0: bool) bool;', text); self.assertIn('items[0].bool', text)
        self.assertIn('common.forkCall(std.meta.ArgsTuple(@TypeOf(flip)), .{ a0 }, flip, false)', text)
        pub = self.root/'pub.zig'; pub.write_text('pub fn flip(a: bool) bool { return !a; }\n')
        self.assertNotIn('extern fn', CX.harness_text(self.request(source=pub)))
        for text in ('fn flip(a: bool) bool { return !a; }\n', 'pub fn flip(a: bool) bool {}\nexport fn flip(a: bool) bool {}\n'):
            (self.root/'bad.zig').write_text(text)
            self.assertIsNone(self.request(source=self.root/'bad.zig'))   # private or ambiguous
        params, ret = EVAL.signature(FAKE_GEN, 'flip')
        self.assertIsNone(CX.native_request(self.root, self.src, 'flip', [3], params, ret, None))   # wrong value type
        self.assertIsNone(CX.native_request(self.root, self.src, 'flip', [], params, ret, None))    # wrong arity

    def test_comparison_follows_the_differential_rules(self):
        for native, model, same in [('{"ok":3}', '{"ok":3}', True), ('{"ok":"3"}', '{"ok":3}', True), ('{"ok":3}', '{"ok":4}', False),
                                    ('{"fail":"integerOverflow"}', '{"fail":"Zig.Error.overflow"}', True),
                                    ('{"fail":"integerOverflow"}', '{"fail":"Zig.Error.outOfBounds"}', False),
                                    ('{"fail":"unknown"}', '{"fail":"Zig.Error.overflow"}', False), ('{"ok":3}', 'not json', False)]:
            self.assertEqual(CX.native_matches(native, model), same, (native, model))

    def test_native_outcome_decides_the_replay(self):
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
        info = CX.with_native(self.root, CX.lean_block(request), self.src, 'fake', 'flip', [True], gen=self.gen)
        lean = fake_runner('O\t0\t{"ok":0}', 'V\t0\t{"ok":0}')
        for zig, status, native in [(dict(line='{"ok":0}'), 'verified', 'verified'),
                                    (dict(line='{"ok":1}'), 'not_reproduced', 'not_reproduced'),   # native disagrees: not a program bug
                                    (dict(build_fails=True), 'error', 'error'),
                                    (None, 'error', 'unavailable')]:
            with self.subTest(native=native):
                outcome = CX.confirm(self.root, info, 30, self.zig(**zig) if zig else '/nonexistent/zig', lean)
                self.assertEqual((outcome['status'], outcome['zig_native']['status']), (status, native))
        # A Lean replay that does not reproduce never reaches the native program.
        outcome = CX.confirm(self.root, info, 30, self.zig(), fake_runner('O\t0\t{"ok":1}'))
        self.assertEqual((outcome['status'], outcome['zig_native']['status']), ('not_reproduced', 'not_run'))
        self.src.write_text(NATIVE_SRC + '// edited\n')
        self.assertEqual(CX.confirm(self.root, info, 30, self.zig(), lean)['zig_native']['status'], 'error')   # stale Zig source

    def test_disagreeing_native_run_leaves_the_violation_unsolved(self):
        for line, expected in [('{"ok":0}', ('counterexample', 'replayed_failure')), ('{"ok":1}', ('unsolved', 'replay_not_reproduced')),
                               ('', ('setup_failure', 'replay_error'))]:
            with self.subTest(line=line):
                request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
                info = CX.with_native(self.root, CX.lean_block(request), self.src, 'fake', 'flip', [True], gen=self.gen)
                info.update(CX.confirm(self.root, info, 30, self.zig(line, build_fails=line == ''),
                                       fake_runner('O\t0\t{"ok":0}', 'V\t0\t{"ok":0}')))
                judgement = CX.verdict(goal='violated', replay=info['status'])
                self.assertEqual(judgement[:2], expected)

    def test_unsupported_zig_source_is_an_input_error(self):
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
        with self.assertRaises(CX.Invalid):
            CX.with_native(self.root, CX.lean_block(request), self.root/'missing.zig', 'fake', 'flip', [True], gen=self.gen)


@unittest.skipUnless(AIR2LEAN.is_file(), 'needs `lake build air2lean ZigLean`')
class SeededLoop(unittest.TestCase):
    SPEC = 'r = .ok (BitVec.ofNat 32 (p0.toNat * (p0.toNat - 1) / 2))'
    PRE = 'p0.toNat < 1000'

    @classmethod
    def translate(cls, buggy):
        directory = Path(cls.temp.name)/('bad' if buggy else 'good')
        air = loopsum.write(directory/'air', buggy)
        result = subprocess.run([str(AIR2LEAN), str(air), '-o', str(directory/'Gen.lean'), '--namespace', 'Loops', '--prefix', 'loops.', '--profile', 'legacy-abi64-le'],
                                capture_output=True, text=True, cwd=ROOT)
        assert result.returncode == 0, result.stderr
        return directory

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.good, cls.bad = cls.translate(False), cls.translate(True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def search(self, variant, out=None, **kw):
        return CX.goal_bundle(ROOT, 'loops', 'sumUpTo', self.SPEC, self.PRE, gen=variant/'Gen.lean', air_dir=variant/'air',
                              max_inputs=512, timeout=600, **kw)

    def test_correct_loop_has_no_counterexample(self):
        data = self.search(self.good)
        self.assertNotEqual(data['classification'], 'counterexample')
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'search_exhausted'))  # 2^32 inputs: bounded only
        self.assertFalse(data['is_program_bug_evidence'])
        self.assertGreater(data['source']['checked'], 0)

    def test_off_by_one_loop_yields_a_replayed_counterexample_and_a_source_span(self):
        data = self.search(self.bad)
        self.assertEqual((data['classification'], data['reason']), ('counterexample', 'replayed_failure'))
        self.assertEqual((data['input'], data['replay']['status'], data['contract']['id']), ([1], 'verified', 'postcondition'))
        self.assertEqual(data['observed']['line'], '{"ok":"1"}'.replace('"1"', '1'))
        self.assertTrue(data['is_program_bug_evidence'] and not data['qualified'])
        loc = data['location']
        self.assertEqual((loc['function'], loc['localization'], loc['source_map']), ('loops.sumUpTo', 'function_only', 'exact_statement'))
        self.assertEqual(loc['functions'][0]['source_span'], dict(file='loops.zig', module='root', line=loopsum.DECL_LINE, column=None))
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp)/'bundle.json'; path.write_text(json.dumps(data))
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(CX.replay_bundle(ROOT, path, None, 600), 0)
            self.assertIn('status=verified', out.getvalue())
            # An edit to the generated Lean makes the bundle stale, never a silent pass.
            edited = self.bad/'Gen.lean'; original = edited.read_text()
            try:
                edited.write_text(original + '\n-- edited\n')
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(CX.replay_bundle(ROOT, path, None, 600), 3)
            finally:
                edited.write_text(original)

    def test_committed_example_replays_sequentially_without_zig(self):
        """A differential-style row of the committed basic.scale is confirmed by Lean evaluation alone."""
        for args, line, status in [([3, 4], '{"ok":12}', 'verified'),
                                   ([4294967295, 2], '{"fail":"Zig.Error.overflow"}', 'verified'),
                                   ([3, 4], '{"ok":13}', 'not_reproduced')]:
            request = CX.lean_request(ROOT, 'basic', 'scale', args, line)
            self.assertIsNotNone(request)
            self.assertEqual(CX.lean_confirm(ROOT, request, 600)['status'], status, (args, line))
        self.assertIsNone(CX.lean_request(ROOT, 'basic', 'sum', [[1, 2]], '{"ok":"3"}'))  # slice parameter: unsupported

    def test_cli_headline_and_bundle_file(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)/'goal.json'
            result = subprocess.run([sys.executable, '-B', str(ROOT/'scripts/counterexample.py'), 'goal-search', '--example', 'loops',
                                     '--function', 'sumUpTo', '--spec', self.SPEC, '--pre', self.PRE, '--gen', str(self.bad/'Gen.lean'),
                                     '--air-dir', str(self.bad/'air'), '--max-inputs', '256', '--output', str(out)],
                                    capture_output=True, text=True, cwd=ROOT, timeout=900)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('classification=counterexample', result.stdout)
            self.assertEqual(json.loads(out.read_text())['input'], [1])


if __name__ == '__main__':
    unittest.main()
