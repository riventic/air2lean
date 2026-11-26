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


def fake_runner(*lines, sleep=0, code=0, given=None):
    """A stand-in Lean process. `given`: the lines for a driver that decides the postcondition on a recorded
    (native) outcome instead of calling the function."""
    model, recorded = chr(10).join(lines), chr(10).join(given if given is not None else lines)
    body = (f'import sys,time;time.sleep({sleep});text=open(sys.argv[1]).read() if len(sys.argv) > 1 else "";'
            f'print({recorded!r} if "some given" in text else {model!r});sys.exit({code})')
    return (sys.executable, '-c', body)


# Every value kind, by hand: the generated declarations and the AIR type table they are resolved against.
KINDS_GEN = '''import ZigLean
namespace K
structure P where
  x : BitVec 8
  «at» : Option (BitVec 16)
  deriving Repr, Inhabited, DecidableEq

inductive C where
  | lo
  | hi
  deriving Repr, Inhabited, DecidableEq

def C.toBits : C → BitVec 8
  | .lo => (-(1 : BitVec 8))
  | .hi => (5 : BitVec 8)

def C.ofInt? (v : Int) : Option C :=
  if v = -1 then Option.some .lo else if v = 5 then Option.some .hi else Option.none

structure N where
  bits : BitVec 8
  deriving Repr, Inhabited, DecidableEq

def N.toBits (e : N) : BitVec 8 := e.bits

def N.ofInt? (v : Int) : Option N :=
  if 0 ≤ v ∧ v ≤ 255 then Option.some ⟨BitVec.ofInt 8 v⟩ else Option.none

inductive U where
  | one (v : P)
  | none_
  | undef_one (v : P) (written : List String)
  deriving Repr, Inhabited, DecidableEq

structure Raw where
  bytes : Vector Zig.Byte 4
  deriving Repr, Inhabited, DecidableEq

def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

def f (p0 : P) (p1 : C) (p2 : Array (U)) (p3 : N) : Zig.MemM (Except Zig.ErrName (Option (P))) := do
  pure (.ok none)

def g (p0 : Zig.Slice) : Zig.MemM (Unit) := do
  pure ()

def h (p0 : Raw) : Zig.Result (Zig.F32) := do
  pure default

def c [Zig.Os.HasEnv] (p0 : Bool) : Zig.ConcM Tgt (Unit) := do
  pure ()

def w (p0 : Bool) : Zig.Result (BitVec 64) := do
  pure 0

def s (p0 : Array (BitVec 8)) : Zig.Result (Array (BitVec 8)) := do
  pure p0
end K
'''
KINDS_TYPES = [
    dict(k='int', signed=False, bits=8),                                                    # 0
    dict(k='int', signed=True, bits=16),                                                    # 1
    dict(k='optional', child=1),                                                            # 2
    dict(k='struct', name='k.P', layout='auto', fields=[dict(name='x', ty=0), dict(name='at', ty=2)]),   # 3
    dict(k='int', signed=True, bits=8),                                                     # 4
    dict(k='enum', name='k.C', tag=4, exhaustive=True, fields=[dict(name='lo', value='-1'), dict(name='hi', value='5')]),  # 5
    dict(k='enum', name='k.N', tag=0, exhaustive=False, fields=[dict(name='zero', value='0')]),           # 6
    dict(k='void'),                                                                         # 7
    dict(k='enum', name='tag', tag=0, exhaustive=True, fields=[dict(name='one', value='0'), dict(name='none_', value='1')]),  # 8
    dict(k='union', name='k.U', layout='auto', tag=8, fields=[dict(name='one', ty=3), dict(name='none_', ty=7)]),  # 9
    dict(k='ptr', size='slice', const=True, child=9, sentinel=False),                       # 10
    dict(k='optional', child=3),                                                            # 11
    dict(k='error_set', errors=['Bad', 'Worse']),                                           # 12
    dict(k='error_union', error=12, payload=11),                                            # 13
    dict(k='ptr', size='slice', const=False, child=0, sentinel=False),                      # 14
    dict(k='union', name='k.Raw', layout='extern', fields=[dict(name='int', ty=0)]),        # 15
    dict(k='float', bits=32),                                                               # 16
    dict(k='bool'),                                                                         # 17
    dict(k='int', signed=False, bits=64),                                                   # 18
    dict(k='ptr', size='slice', const=True, child=0, sentinel=False),                       # 19
]


def kinds_air(params, ret):
    return dict(params=params, ret=ret, types=KINDS_TYPES)


class Kinds(unittest.TestCase):
    """The type model of scripts/lean-eval.py, without Lean: resolution, the value codecs and the diagnostics."""

    def setUp(self):
        self.sig = EVAL.signature(KINDS_GEN, 'f', kinds_air([3, 5, 10, 6], 13))
        self.p, self.c, self.us, self.n = self.sig.types

    def test_one_resolution_for_every_kind_and_nesting(self):
        sig = self.sig
        self.assertEqual([t.lean for t in sig.types], ['K.P', 'K.C', 'Array (K.U)', 'K.N'])
        self.assertEqual(sig.ret.lean, 'Except Zig.ErrName (Option (K.P))')
        self.assertTrue(sig.memory and sig.typed and not sig.wide)
        self.assertEqual(self.p.fields[1][:2], ('at', '«at»'))                      # the Zig name and the Lean name
        self.assertEqual(self.p.fields[1][2], EVAL.Opt(EVAL.Int(16, True)))         # signedness comes from the AIR
        self.assertEqual((self.c.named, self.c.exhaustive, self.n.exhaustive), ((('lo', -1), ('hi', 5)), True, False))
        self.assertEqual(self.us.child.undef, ('undef_one',))
        self.assertTrue(EVAL.signature(KINDS_GEN, 'w', kinds_air([17], 18)).wide)   # a 64-bit result is quoted, as the harness does

    def test_unsupported_types_are_rejected_with_the_reason(self):
        for function, air, reason in [
                ('g', kinds_air([14], 7), 'a pointer or a mutable slice is a place in memory'),
                ('h', kinds_air([15], 16), 'does not line up with the AIR union'),
                ('c', kinds_air([17], 7), 'environment or instance argument'),
                ('s', kinds_air([19], 19), 'a slice result is a place in memory'),
                ('f', None, 'no AIR type'),                                          # a named type is never guessed
                ('f', kinds_air([3, 5, 10], 13), 'parameters do not line up'),
                ('f', kinds_air([3, 6, 10, 6], 13), 'does not line up with the AIR enum'),   # exhaustive form, non-exhaustive AIR
                ('f', kinds_air([3, 5, 14, 6], 13), 'not a read-only slice'),
                ('f', kinds_air([0, 5, 10, 6], 13), 'does not line up with the AIR int'),
                ('missing', None, 'not a generated function')]:
            with self.subTest(function=function, reason=reason):
                with self.assertRaises(EVAL.Unsupported) as caught: EVAL.signature(KINDS_GEN, function, air)
                self.assertIn(reason, str(caught.exception))
        twice = [dict(k='optional', child=2), *KINDS_TYPES[1:]]                      # ??i16: `null` is ambiguous
        gen = KINDS_GEN.replace('def w (p0 : Bool)', 'def w (p0 : Option (Option (BitVec 16)))')
        with self.assertRaises(EVAL.Unsupported) as caught: EVAL.signature(gen, 'w', dict(params=[0], ret=18, types=twice))
        self.assertIn('ambiguous', str(caught.exception))
        # Without an AIR type table only the scalar kinds resolve, integers as unsigned.
        legacy = EVAL.signature(FAKE_GEN.replace('Bool', 'BitVec 8'), 'flip')
        self.assertEqual((legacy.types, legacy.ret, legacy.typed), ([EVAL.Int(8, False)], EVAL.Int(8, False), False))

    def test_values_rows_literals_and_native_results_follow_the_kind(self):
        point = {'x': 7, 'at': -2}
        args = self.sig.parse_args([point, 5, [{'one': {'x': 1, 'at': None}}, {'none_': None}], 9])
        self.assertEqual(args[0], point)
        self.assertEqual([t.flat(v) for t, v in zip(self.sig.types, args)],
                         [[7, 1, 65534], [5], [2, 0, 1, 0, 1], [9]])                 # struct fields, tag, length + items, tag bits
        self.assertEqual(self.c.flat(-1), [255])
        self.assertEqual([t.zig(v) for t, v in zip(self.sig.types, args)],
                         ['.{ .@"x" = 7, .@"at" = -2 }', '.@"hi"',
                          '&.{ .{ .@"one" = .{ .@"x" = 1, .@"at" = null } }, .{ .@"none_" = {} } }', '@enumFromInt(9)'])
        ret = self.sig.ret
        self.assertEqual([ret.flat(ret.parse(j)) for j in ({'err': 'Worse'}, None, point)], [[2], [0, 0], [0, 1, 7, 1, 65534]])
        self.assertEqual(ret.zig({'err': 'Bad'}), 'error.@"Bad"')
        for kind, bad in [(self.p, {'x': 7}), (self.p, {'at': 1, 'x': 7}), (self.p, {'x': 256, 'at': None}), (self.c, 0), (self.c, '5'),
                          (self.us, {'one': None}), (self.us, [{'two': None}]), (ret, {'err': 'Other'}), (self.n, 256), (EVAL.Bool(), 2)]:
            with self.subTest(bad=bad):
                with self.assertRaises(EVAL.Mismatch): kind.parse(bad)
        with self.assertRaises(EVAL.Mismatch): self.sig.parse_args([point])           # one value per parameter
        self.assertEqual(EVAL.Int(64, False).parse('18446744073709551615', wide=True), 2 ** 64 - 1)
        with self.assertRaises(EVAL.Unsupported): self.p.extern()                      # no C-ABI spelling: `pub fn` only
        self.assertEqual((EVAL.Int(8, True).extern(), EVAL.Bool().extern()), ('i8', 'bool'))

    def test_domains_are_exhaustive_only_when_finite(self):
        self.assertEqual((self.c.size(), list(self.c.values())), (2, [-1, 5]))
        self.assertEqual(self.n.size(), 256)
        self.assertEqual((self.p.size(), self.us.size(), self.sig.ret.size()), (256 * 65537, None, 2 + 1 + 256 * 65537))
        rows, exhaustive = EVAL.inputs([self.c, EVAL.Opt(EVAL.Bool())], 100, 0)
        self.assertTrue(exhaustive); self.assertEqual(len(rows), 6); self.assertEqual(rows[0], (-1, None))
        rows, exhaustive = EVAL.inputs(self.sig.types, 200, 3)
        self.assertFalse(exhaustive); self.assertLessEqual(len(rows), 200)
        self.assertEqual(EVAL.inputs(self.sig.types, 200, 3), (rows, False))           # seeded, deterministic
        self.assertEqual(rows, sorted(rows, key=lambda row: EVAL.row_key(self.sig.types, row)))   # smallest first
        self.assertIn([], [row[2] for row in rows])                                    # the empty slice is a boundary value
        for row in rows: self.sig.parse_args(list(row))                                # every candidate is a value of its kind

    def test_the_driver_has_one_decoder_and_renderer_per_kind(self):
        rows = [tuple(self.sig.parse_args([{'x': 7, 'at': -2}, 5, [{'none_': None}], 9]))]
        text = EVAL.driver('K', self.sig, rows, spec='r = r', given=[('ok', {'err': 'Bad'})])
        self.assertIn('"0,7,1,65534,5,1,1,9,0,1"', text)                              # index, the arguments, then the given outcome
        self.assertEqual(text.count('Option ((K.P) × List Nat)'), 1)                   # P is a parameter, a union payload and the result
        self.assertIn('K.C.ofInt? (Zig.val true (BitVec.ofNat 8 a))', text)
        emit = EVAL.Emit(); self.us.child.renderer(emit, False)
        self.assertIn('| K.U.undef_one .. => "{\\"undefined_payload\\":null}"', emit.text[-1])   # no Zig value: never equals a native result
        self.assertIn('some given', text); self.assertNotIn('K.f p0', text)            # the function is not called
        called = EVAL.driver('K', self.sig, rows)
        self.assertIn('(((K.f p0 p1 p2 p3).run (K.mem0 .fresh)).run).map (·.map (·.1))', called)

    def test_shrinking_reaches_a_locally_minimal_violation(self):
        def search(types, row, violates, **kw):
            def evaluate(candidates):
                hit = next((k for k, c in enumerate(candidates) if violates(*c)), None)
                return dict(status='ok', lines=[] if hit is None else [['V', str(hit), f'line {candidates[hit]}']])
            return CX.minimize(kw.get('evaluate', evaluate), types, row, 'first')
        u8, i8 = EVAL.Int(8, False), EVAL.Int(8, True)
        row, line, info = search([u8], (255,), lambda x: x >= 100)
        self.assertEqual((row, line, info['status']), ((100,), 'line (100,)', 'locally_minimal'))
        self.assertLess(info['rounds'], 16)                                            # powers of two, not one step per round
        self.assertEqual(search([i8], (-77,), lambda x: x <= -3)[0], (-3,))            # toward zero from either side
        self.assertEqual(search([self.p], ({'x': 90, 'at': 300},), lambda p: p['at'] is not None)[0], ({'x': 0, 'at': 0},))
        self.assertEqual(search([self.us, u8], ([{'none_': None}, {'one': {'x': 9, 'at': None}}, {'none_': None}], 4),
                                lambda us, n: any('one' in u and u['one']['x'] >= 3 for u in us))[0], ([{'one': {'x': 3, 'at': None}}], 0))
        self.assertEqual(search([self.sig.ret], ({'x': 5, 'at': 1},), lambda r: r is not None)[0], ({'x': 0, 'at': None},))
        row, line, info = search([u8], (255,), lambda x: True)
        self.assertEqual((row, info['status'], info['rounds']), ((0,), 'locally_minimal', 1))
        # An evaluation that fails stops the shrinking: the violation reached so far stands.
        row, line, info = search([u8], (255,), None, evaluate=lambda candidates: dict(status='timeout', lines=[]))
        self.assertEqual((row, line, info['status'], info['rounds_with_progress']), ((255,), 'first', 'stopped_timeout', 0))
        row, line, info = search([u8], (255,), None, evaluate=lambda candidates: dict(status='ok', lines=[['V', '99', 'x']]))
        self.assertEqual((row, info['status']), ((255,), 'stopped_error'))


class Mocked(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.gen = self.root/'Gen.lean'; self.gen.write_text(FAKE_GEN)

    def goal(self, runner, **kw):
        return CX.goal_bundle(self.root, 'fake', 'flip', SPEC_TEXT, gen=self.gen, runner=runner, replay=False, **kw)

    def test_signature_and_unsupported_shapes(self):
        sig = EVAL.signature(FAKE_GEN, 'flip')
        self.assertEqual((sig.params, sig.ret, sig.memory), ((('p0', EVAL.Bool()),), EVAL.Bool(), False))
        with self.assertRaises(EVAL.Unsupported):
            EVAL.signature('namespace G\ndef mem0 (σ : Zig.Placement) : Zig.Mem := m\ndef g (p0 : Zig.Ptr) : Zig.MemM (Unit) := do\n', 'g')
        data = CX.goal_bundle(self.root, 'fake', 'missing', SPEC_TEXT, gen=self.gen, replay=False)
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'unsupported'))
        self.assertIn('not a generated function', data['source']['detail'])            # the reason is reported, never a guess
        kinds = self.root/'Kinds.lean'; kinds.write_text(KINDS_GEN)
        data = CX.goal_bundle(self.root, 'k', 'g', 'True', gen=kinds, replay=False)
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'unsupported'))
        self.assertIn('Zig.Slice', data['source']['detail'])

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
        u8, u32 = EVAL.Int(8, False), EVAL.Int(32, False)
        rows, exhaustive = EVAL.inputs([u8], 4096, 0)
        self.assertTrue(exhaustive); self.assertEqual(len(rows), 256); self.assertEqual(rows[0], (0,))
        rows, exhaustive = EVAL.inputs([u32, u32], 100, 7)
        self.assertFalse(exhaustive); self.assertLessEqual(len(rows), 100)
        self.assertEqual(EVAL.inputs([u32, u32], 100, 7), (rows, False))  # seeded, deterministic
        self.assertEqual((EVAL.Int(8, True).of_bits(255), EVAL.Int(8, True).flat(-1)), (-1, [255]))

    def test_a_sampled_violation_is_shrunk_and_an_exhaustive_one_is_the_smallest(self):
        big = self.root/'Big.lean'
        big.write_text(FAKE_GEN.replace('Bool', 'BitVec 32').replace('!p0', 'p0'))
        # A sampled domain: the violation goes through the shrinking (`Kinds` drives it; here row 0 has nothing below it).
        data = CX.goal_bundle(self.root, 'fake', 'flip', 'r = .ok p0', gen=big, runner=fake_runner('V\t0\t{"ok":1}', 'S\t1\t0\t0\t1'),
                              replay=False, max_inputs=64)
        self.assertEqual((data['classification'], data['input'], data['input_index']), ('candidate', [0], 0))
        self.assertEqual(data['source']['minimization'], dict(status='locally_minimal', rounds=0, rounds_with_progress=0))
        data = self.goal(fake_runner('V\t1\t{"ok":1}', 'S\t2\t0\t0\t1'))
        self.assertEqual(data['source']['minimization'], dict(status='smallest_of_domain', rounds=0))


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
        return CX.native_request(self.root, kw.pop('source', self.src), 'flip')

    def test_request_shapes(self):
        request, sig = self.request(), EVAL.signature(FAKE_GEN, 'flip')
        self.assertEqual((request['decl'], request['function']), ('export', 'flip'))
        text = CX.harness_text(request, sig, [True])
        self.assertIn('extern fn flip(p0: bool) bool;', text)
        self.assertIn('const Args = std.meta.ArgsTuple(@TypeOf(flip));\nconst args: Args = .{ true };', text)
        self.assertIn('common.forkCall(Args, args, flip, false)', text)
        pub = self.root/'pub.zig'; pub.write_text('pub fn flip(a: bool) bool { return !a; }\n')
        self.assertNotIn('extern fn', CX.harness_text(self.request(source=pub), sig, [True]))
        for text in ('fn flip(a: bool) bool { return !a; }\n', 'pub fn flip(a: bool) bool {}\nexport fn flip(a: bool) bool {}\n'):
            (self.root/'bad.zig').write_text(text)
            with self.assertRaises(EVAL.Unsupported): self.request(source=self.root/'bad.zig')   # private or ambiguous
        for raw in ([3], []):                                                         # wrong value kind, wrong arity
            with self.assertRaises(EVAL.Unsupported): CX.lean_request(self.root, 'fake', 'flip', raw, '{"ok":0}', gen=self.gen)

    def test_values_of_every_kind_are_zig_literals_typed_by_the_function(self):
        sig = EVAL.signature(KINDS_GEN, 'f', kinds_air([3, 5, 10, 6], 13))
        args = sig.parse_args([{'x': 7, 'at': None}, -1, [], 9])
        pub = self.root/'pub.zig'; pub.write_text('pub fn f() void {}\n')
        text = CX.harness_text(CX.native_request(self.root, pub, 'f'), sig, args)
        self.assertIn('const Args = std.meta.ArgsTuple(@TypeOf(target.f));\n'
                      'const args: Args = .{ .{ .@"x" = 7, .@"at" = null }, .@"lo", &.{  }, @enumFromInt(9) };', text)
        exported = self.root/'exp.zig'; exported.write_text('export fn f() void {}\n')
        with self.assertRaises(EVAL.Unsupported) as caught: CX.harness_text(CX.native_request(self.root, exported, 'f'), sig, args)
        self.assertIn('declare the function `pub`', str(caught.exception))             # a struct has no C-ABI spelling here

    def test_the_postcondition_is_decided_on_the_native_outcome(self):
        """The differential outcome agrees, but only a native outcome that itself violates the postcondition reproduces."""
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
        info = CX.with_native(self.root, CX.lean_block(request), self.src, 'flip')
        model = ('O\t0\t{"ok":0}', 'V\t0\t{"ok":0}')
        for given, status, post in [(('O\t0\t{"ok":0}', 'V\t0\t{"ok":0}'), 'verified', 'violated'),
                                    (('O\t0\t{"ok":0}',), 'not_reproduced', 'holds'),
                                    ((), 'error', 'error')]:
            with self.subTest(post=post):
                outcome = CX.confirm(self.root, info, 30, self.zig('{"ok":0}'), fake_runner(*model, given=given))
                self.assertEqual((outcome['status'], outcome['zig_native']['postcondition']['status']), (status, post))
        # A native result that is no value of the result type, or a failure without a model outcome, decides nothing.
        for line, detail in [('{"ok":7}', 'no value of the result type'), ('{"fail":"unknown"}', 'no outcome of the model'),
                             ('{"ok":0,"bufs":[]}', 'no outcome of the model')]:
            post = CX.native_postcondition(self.root, request, line, 30, fake_runner(*model))
            self.assertEqual(post['status'], 'undecided'); self.assertIn(detail, post['detail'])
        # A native panic is the model's error constructor of its kind.
        driver = self.root/'driver.txt'
        capture = (sys.executable, '-c', f'import sys,shutil;shutil.copy(sys.argv[1], {str(driver)!r});print("O\\t0\\t{{}}\\nV\\t0\\t{{}}")')
        self.assertEqual(CX.native_postcondition(self.root, request, '{"fail":"integerOverflow"}', 30, capture)['status'], 'violated')
        self.assertIn(f'"0,1,{1 + EVAL.ERRORS.index("overflow")}"', driver.read_text())
        # Without a stated postcondition the differential outcome alone decides, as before.
        plain = CX.with_native(self.root, CX.lean_block(CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen)),
                               self.src, 'flip')
        outcome = CX.confirm(self.root, plain, 30, self.zig('{"ok":0}'), fake_runner('O\t0\t{"ok":0}'))
        self.assertEqual(outcome['status'], 'verified'); self.assertNotIn('postcondition', outcome['zig_native'])

    def test_comparison_follows_the_differential_rules(self):
        for native, model, same in [('{"ok":3}', '{"ok":3}', True), ('{"ok":"3"}', '{"ok":3}', True), ('{"ok":3}', '{"ok":4}', False),
                                    ('{"fail":"integerOverflow"}', '{"fail":"Zig.Error.overflow"}', True),
                                    ('{"fail":"integerOverflow"}', '{"fail":"Zig.Error.outOfBounds"}', False),
                                    ('{"fail":"unknown"}', '{"fail":"Zig.Error.overflow"}', False), ('{"ok":3}', 'not json', False)]:
            self.assertEqual(CX.native_matches(native, model), same, (native, model))

    def test_native_outcome_decides_the_replay(self):
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
        info = CX.with_native(self.root, CX.lean_block(request), self.src, 'flip')
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
                info = CX.with_native(self.root, CX.lean_block(request), self.src, 'flip')
                info.update(CX.confirm(self.root, info, 30, self.zig(line, build_fails=line == ''),
                                       fake_runner('O\t0\t{"ok":0}', 'V\t0\t{"ok":0}')))
                judgement = CX.verdict(goal='violated', replay=info['status'])
                self.assertEqual(judgement[:2], expected)

    def test_unsupported_zig_source_is_an_input_error(self):
        request = CX.lean_request(self.root, 'fake', 'flip', [True], '{"ok":0}', gen=self.gen, spec=SPEC_TEXT)
        with self.assertRaises(CX.Invalid):
            CX.with_native(self.root, CX.lean_block(request), self.root/'missing.zig', 'flip')


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
            self.assertEqual(CX.lean_confirm(ROOT, request, 600)['status'], status, (args, line))
        with self.assertRaises(EVAL.Unsupported): CX.lean_request(ROOT, 'slices', 'reverse', [[1, 2]], '{"ok":null}')  # a slice it writes: memory

    def test_committed_rows_of_other_value_kinds_replay_and_decide_a_postcondition(self):
        """Rows in the differential input format of committed examples: the kinds come from the golden AIR."""
        rect = {'rect': {'w': 3, 'h': 4}}
        for example, function, args, line, spec, violated in [
                ('basic', 'sum', [[1, 2]], '{"ok":"3"}', 'r = .ok (p0.foldl (· + ·.setWidth 64) 0)', False),          # slice
                ('variants', 'area', [rect], '{"ok":"12"}', 'r = .ok 12#64', False),                                  # union of a struct
                ('variants', 'area', [rect], '{"ok":"12"}', 'r = .ok 13#64', True),
                ('variants', 'next', [2], '{"ok":1}', 'r = .ok p0', True),                                          # enum
                ('variants', 'isUrgent', [-1], '{"ok":0}', 'r = .ok (p0 == Prio.high)', False),                       # signed tag values
                ('variants', 'severity', [7], '{"ok":2}', 'r = .ok 2#8', False),                                      # non-exhaustive enum
                ('options', 'find', [[5, 6], 6], '{"ok":"1"}', 'r = .ok (some 1#64)', False),                         # optional result
                ('options', 'find', [[5, 6], 7], '{"ok":null}', 'r.toBool = true ∧ r ≠ .ok none', True),
                ('errors', 'parseDigit', [47], '{"ok":{"err":"NotDigit"}}', 'r = .ok (.error "NotDigit")', False),    # error union
                ('basic', 'weightedTardiness', [{'duration': 5, 'due': 3, 'weight': 2}, 10], None, 'r.toBool = true', False)]:  # struct
            with self.subTest(function=function, spec=spec):
                if line is None:
                    line = CX.lean_evaluate(ROOT, CX.lean_request(ROOT, example, function, args, ''), 600)['observed']['line']
                request = CX.lean_request(ROOT, example, function, args, line, spec=spec)
                request['expected']['violation'] = violated
                self.assertEqual(request['signedness'], 'air')
                outcome = CX.lean_confirm(ROOT, request, 600)
                self.assertEqual((outcome['status'], outcome['violated']), ('verified', violated), outcome)

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


ZIG_AIR, ZIG_NATIVE = os.environ.get('AIR2LEAN_ZIG_AIR'), os.environ.get('AIR2LEAN_ZIG_NATIVE')
FIXTURE = HERE/'native'
ADVANCE_SPEC = ('r = .ok (match p0.len with | none => .error "Zero" | some n => if n = 0 then .error "Zero" else '
                'if p0.at.x.toNat + n.toNat > 255 then .error "TooBig" else .ok { p0 with «at» := { p0.at with x := p0.at.x + n } })')
# Per value kind: the function with the seeded bug (its twin is `<name>Ok`), the contract of native/shapes.zig as
# a postcondition, the smallest violating input, and whether the twin's domain is small enough to be exhausted.
SHAPES = {
    'mirror': ('r = .ok { x := p0.y, y := p0.x }', [{'x': 0, 'y': 1}], False),                                   # struct
    'half': ('r = .ok (if p0.toNat % 2 = 1 then none else some (p0 / 2))', [1], True),                            # optional result
    'orSeven': ('r = .ok (p0.getD 7)', [None], True),                                                             # optional parameter
    'pred': ('r = .ok (if p0 = 0 then .error "Zero" else if p0.toNat > 100 then .error "TooBig" else .ok (p0 - 1))', [101], True),
    'next': ('r = .ok (match p0 with | .red => .green | .green => .blue | .blue => .red)', [2], True),            # enum
    'above': ('r = .ok (BitVec.ofInt 16 ((Level.toBits p0).toInt + 1))', [5], True),                              # signed tag values
    'count': ('r = .ok (BitVec.ofNat 32 (p0.toList.filter (· == p1)).length)', [[0], 0], False),                  # slice
    'extent': ('r = .ok (match p0 with | .circle c => BitVec.ofNat 16 (3 * c.toNat) '
               '| .rect q => BitVec.ofNat 16 (q.x.toNat + q.y.toNat) | _ => 0)', [{'rect': {'x': 0, 'y': 1}}], False),   # tagged union
    'advance': (ADVANCE_SPEC, [{'at': {'x': 0, 'y': 0}, 'len': 1, 'tint': 1}], False),                            # nested, memory monad
}


@unittest.skipUnless(ZIG_AIR and ZIG_NATIVE and AIR2LEAN.is_file(), 'needs AIR2LEAN_ZIG_AIR, AIR2LEAN_ZIG_NATIVE and a built air2lean')
class Shapes(unittest.TestCase):
    """native/shapes.zig end to end: exported by the patched compiler, translated, searched, minimized, and
    replayed by the generated Lean and by the native program, which must itself violate the postcondition."""

    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(); cls.dir = Path(cls.temp.name)
        subprocess.run(['bash', str(FIXTURE/'export.sh'), ZIG_AIR, str(cls.dir/'air'), 'shapes.zig'], check=True, capture_output=True,
                       text=True, timeout=600)
        (cls.air,) = (cls.dir/'air').iterdir()
        result = subprocess.run([str(AIR2LEAN), str(cls.air), '-o', str(cls.dir/'Gen.lean'), '--namespace', 'Shapes', '--prefix', 'shapes.'],
                                capture_output=True, text=True, cwd=ROOT)
        assert result.returncode == 0, result.stderr

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def search(self, function, spec, source=FIXTURE/'shapes.zig', **kw):
        return CX.goal_bundle(ROOT, 'shapes', function, spec, gen=self.dir/'Gen.lean', air_dir=self.air, max_inputs=512, timeout=600,
                              zig_source=source, zig=ZIG_NATIVE, **kw)

    def test_each_seeded_bug_yields_a_minimal_counterexample_that_the_native_program_reproduces(self):
        for function, (spec, smallest, _) in SHAPES.items():
            with self.subTest(function=function):
                data = self.search(function, spec)
                self.assertEqual((data['classification'], data['reason'], data['contract']['id']),
                                 ('counterexample', 'replayed_failure', 'postcondition'), data['replay'])
                self.assertEqual(data['input'], smallest)
                self.assertIn(data['source']['minimization']['status'], ('locally_minimal', 'smallest_of_domain'))
                native = data['replay']['zig_native']
                self.assertEqual((data['replay']['status'], native['status'], native['postcondition']['status']),
                                 ('verified', 'verified', 'violated'))
                self.assertEqual(native['observed']['line'], data['observed']['line'])    # the same value, rendered by both sides
                self.assertTrue(data['is_program_bug_evidence'])
                # Minimal: no input one shrink step below the reported one violates the postcondition.
                sig = CX.read_signature(self.dir/'Gen.lean', function, self.air/f'shapes.{function}.json')[1]
                below = EVAL.shrinks(sig.types, tuple(smallest))
                if below:
                    out = EVAL.run(ROOT, self.dir/'Gen.lean', EVAL.driver('Shapes', sig, below, spec=spec), timeout=600)
                    self.assertEqual((out['status'], [l for l in out['lines'] if l[0] == 'V']), ('ok', []))

    def test_no_correct_twin_is_reported(self):
        for function, (spec, _, finite) in SHAPES.items():
            with self.subTest(function=function):
                data = self.search(function + 'Ok', spec)
                expected = ('no_failure', 'exhaustive_domain_no_violation') if finite else ('unsolved', 'search_exhausted')
                self.assertEqual((data['classification'], data['reason']), expected, data['source'])
                self.assertFalse(data['is_program_bug_evidence'])
                self.assertGreater(data['source']['checked'], 0)

    def test_stored_bundle_replays_both_sides_and_the_native_postcondition(self):
        out = self.dir/'advance.json'
        argv = [sys.executable, '-B', str(ROOT/'scripts/counterexample.py')]
        result = subprocess.run([*argv, 'goal-search', '--example', 'shapes', '--function', 'advance', '--spec', ADVANCE_SPEC,
                                 '--gen', str(self.dir/'Gen.lean'), '--air-dir', str(self.air), '--max-inputs', '512', '--timeout', '600',
                                 '--zig-source', str(FIXTURE/'shapes.zig'), '--native-zig', ZIG_NATIVE, '--output', str(out)],
                                capture_output=True, text=True, cwd=ROOT, timeout=900)
        self.assertEqual(result.returncode, 0, result.stderr); self.assertIn('classification=counterexample', result.stdout)
        replay = lambda path: subprocess.run([*argv, 'replay', '--bundle', str(path), '--timeout', '600', '--native-zig', ZIG_NATIVE],
                                             capture_output=True, text=True, cwd=ROOT, timeout=900)
        result = replay(out)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('zig_native=verified', result.stdout); self.assertIn('native_postcondition=violated', result.stdout)
        # The AIR type table is part of the request: a changed one is stale, never re-read as other types.
        data = json.loads(out.read_text())
        data['replay']['request']['air_sha256'] = '0' * 64
        (self.dir/'stale.json').write_text(json.dumps(data))
        self.assertEqual(replay(self.dir/'stale.json').returncode, 3)

    def test_native_program_without_the_bug_never_confirms_the_violation(self):
        fixed = self.dir/'fixed'; fixed.mkdir()
        (fixed/'shapes.zig').write_text((FIXTURE/'shapes.zig').read_text().replace('.{ .x = p.y, .y = p.y }', '.{ .x = p.y, .y = p.x }', 1))
        data = self.search('mirror', SHAPES['mirror'][0], source=fixed/'shapes.zig')
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'replay_not_reproduced'))
        self.assertEqual(data['replay']['zig_native']['status'], 'not_reproduced')
        self.assertFalse(data['is_program_bug_evidence'])

    def test_a_slice_the_function_writes_is_rejected_with_the_reason(self):
        data = self.search('zero', 'True')
        self.assertEqual((data['classification'], data['reason']), ('unsolved', 'unsupported'))
        self.assertIn('a pointer or a mutable slice is a place in memory', data['source']['detail'])


if __name__ == '__main__':
    unittest.main()
