#!/usr/bin/env python3
"""P08 counterexample bundles on synthetic receipts/reports; the model process is mocked."""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('air2lean_counterexample', ROOT/'scripts/counterexample.py')
CX = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(CX)
CLI, REPORT = CX.CLI, CX.REPORT

ZIG = '''const std = @import("std");

fn writer(p: *u32) void {
    p.* = 1;
}

pub fn run() !u32 {
    var x: u32 = 0;
    const h = try std.Thread.spawn(.{}, writer, .{&x});
    const r = x;
    h.join();
    return r;
}
'''
PANIC = "debug.FullPanic((function 'defaultPanic')).integerOverflow"
AIR = {
    'demo.run': [dict(id=0, tag='dbg_stmt', line=2), dict(id=1, tag='alloc'), dict(id=2, tag='store_safe'),
                 dict(id=3, tag='dbg_stmt', line=3), dict(id=4, tag='call', callee=dict(func='Thread.spawn__anon_1', comptime_fn='demo.writer', noreturn=False)),
                 dict(id=5, tag='dbg_stmt', line=4), dict(id=6, tag='load'),
                 dict(id=7, tag='dbg_stmt', line=5), dict(id=8, tag='call', callee=dict(func='Thread.join', noreturn=False)),
                 dict(id=9, tag='cond_br', then=[dict(id=10, tag='call', callee=dict(func=PANIC, noreturn=True))], **{'else': [dict(id=11, tag='add_safe')]}),
                 dict(id=12, tag='dbg_inline_block', body=[dict(id=13, tag='dbg_stmt', line=99), dict(id=14, tag='atomic_load')]),
                 dict(id=15, tag='ret_safe')],
    'demo.writer': [dict(id=0, tag='dbg_stmt', line=2), dict(id=1, tag='store_safe')],
}


def obs(kind, line):
    return dict(schema=1, kind=kind, legacy_line=line)


ILLEGAL = obs('illegal', '{"fail":"Zig.Error.illegal"}')
VALUE = obs('value', '{"ok":0}')
TIMEOUT = CLI.Timeout('schedule command timed out')


class Bundles(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for path, text in [('tests/diff/demo/inputs/run.jsonl', '[]\n'), ('ZigLean/Basic.lean', '-- runtime\n'),
                           ('examples/demo/demo.zig', ZIG)]:
            p = self.root/path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        air = self.root/'tests/golden/demo/air'; air.mkdir(parents=True)
        for name, body in AIR.items(): (air/f'{name}.json').write_text(json.dumps(dict(schema=11, name=name, body=body)))
        self.out = self.root/'bundle.json'

    # Mocked model process: `executions` is a list of (prefix, options, observation, complete).
    def responder(self, executions, *, truncated=False, replay=None):
        def respond(_, request, __):
            if request['mode'] == 'replay':
                if isinstance(replay, Exception): raise replay
                # The model always runs the requested prefix; `replay` swaps only its observation.
                chosen = next(e for e in executions if e[0] == request['prefix'])
                rows = [(chosen[0], chosen[1], replay or chosen[2], True)]
            else:
                rows = executions
            entries = [dict(prefix=p, options=o, choice_count=len(o) + (not c), trace_complete=c, observation=ob) for p, o, ob, c in rows]
            outcomes = []
            for e in entries:
                if e['observation'] not in outcomes: outcomes.append(e['observation'])
            cut = request['mode'] == 'enumerate' and truncated
            prefix_cut = any(not e['trace_complete'] for e in entries)
            return dict(schema=1, qualified=False, mode=request['mode'], fuel=request['fuel'], node_cap=request['node_cap'],
                        prefix_cap=request['prefix_cap'], runs=len(entries), truncated=cut or prefix_cut, node_cap_reached=cut,
                        prefix_cap_reached=prefix_cut, exploration_complete=request['mode'] == 'enumerate' and not (cut or prefix_cut),
                        saw_no_result=any(e['observation']['kind'] == 'bounded_no_result' for e in entries), executions=entries, outcomes=outcomes)
        return respond

    def run_cli(self, argv, respond=None):
        args = CX.parser().parse_args(argv)
        with patch.object(CLI, 'invoke', side_effect=respond) as invoke, contextlib.redirect_stdout(io.StringIO()) as out:
            code = CX.execute(args, self.root)
        self.last_stdout = out.getvalue()
        return code, invoke

    def search(self, respond, *extra):
        code, invoke = self.run_cli(['search', '--example', 'demo', '--function', 'run', '--fuel', '50', '--node-cap', '8',
                                     '--output', str(self.out), *extra], respond)
        self.assertEqual(code, 0)
        return json.loads(self.out.read_text()), invoke

    RACE = [([0, 0], [2, 2], VALUE, True), ([1, 0], [2, 2], ILLEGAL, True)]

    # Positive controls.

    def test_replayed_race_is_a_counterexample_with_inputs_prefix_contract_and_sites(self):
        data, invoke = self.search(self.responder(self.RACE))
        self.assertEqual(invoke.call_count, 2)
        self.assertEqual((data['classification'], data['reason']), ('counterexample', 'replayed_failure'))
        self.assertTrue(data['is_program_bug_evidence']); self.assertFalse(data['qualified'])
        self.assertEqual(data['input'], []); self.assertEqual(data['input_sha256'], hashlib.sha256(b'[]\n').hexdigest())
        self.assertEqual(data['schedule']['prefix'], [1, 0]); self.assertEqual(data['schedule']['execution_index'], 1)
        self.assertEqual(data['contract']['id'], 'no_illegal_behaviour')
        self.assertEqual(data['replay']['status'], 'verified'); self.assertNotIn('expected', data['replay']['request'])
        self.assertEqual(data['replay']['command'][-4:-2], ['--bundle', str(self.out)])
        loc = data['location']
        self.assertEqual(loc['function'], 'demo.run'); self.assertEqual(loc['source_map'], 'unavailable')
        self.assertEqual([f['name'] for f in loc['functions']], ['demo.run', 'demo.writer'])
        sites = {(s['function'], s['air_id']): s for s in loc['candidate_sites']}
        self.assertEqual(sites[('demo.run', 6)]['zig_line'], 10)       # const r = x;
        self.assertEqual(sites[('demo.writer', 1)]['zig_line'], 4)     # p.* = 1;
        inline = sites[('demo.run', 14)]
        self.assertTrue(inline['inlined']); self.assertEqual(inline['dbg_line'], 5)  # call-site line, not the inlined 99
        self.assertIn('classification=counterexample', self.last_stdout)

    def test_panic_and_deadlock_sites_follow_the_model_constructor(self):
        panic = obs('model_panic', '{"fail":"Zig.Error.overflow"}')
        data, _ = self.search(self.responder([([0], [1], panic, True)]))
        self.assertEqual(data['contract']['id'], 'no_safety_panic')
        self.assertEqual({s['air_id'] for s in data['location']['candidate_sites']}, {10, 11})
        data, _ = self.search(self.responder([([0], [1], obs('deadlock', '{"fail":"Zig.Error.deadlock"}'), True)]))
        self.assertEqual([s['air_id'] for s in data['location']['candidate_sites']], [8])
        self.assertEqual(data['classification'], 'counterexample')

    def test_bundle_replay_command_exit_statuses(self):
        self.search(self.responder(self.RACE))
        replay = ['replay', '--bundle', str(self.out)]
        self.assertEqual(self.run_cli(replay, self.responder(self.RACE))[0], 0)
        self.assertEqual(self.run_cli(replay, self.responder(self.RACE, replay=VALUE))[0], 1)
        self.assertEqual(self.run_cli(replay, self.responder(self.RACE, replay=TIMEOUT))[0], 2)
        (self.root/'ZigLean/Basic.lean').write_text('-- changed\n')
        code, invoke = self.run_cli(replay)
        self.assertEqual(code, 3); invoke.assert_not_called()

    def test_unreplayed_failure_is_only_a_candidate(self):
        data, invoke = self.search(self.responder(self.RACE), '--no-replay')
        self.assertEqual(invoke.call_count, 1)
        self.assertEqual((data['classification'], data['replay']['status']), ('candidate', 'not_run'))
        self.assertFalse(data['is_program_bug_evidence'])
        receipt = self.out.with_name('bundle.receipt.json')
        code, _ = self.run_cli(['from-receipt', '--receipt', str(receipt), '--execution-index', '1', '--replay', '--output', str(self.out)],
                               self.responder(self.RACE))
        self.assertEqual(code, 0); self.assertEqual(json.loads(self.out.read_text())['classification'], 'counterexample')

    def test_clean_complete_tree_has_no_failure(self):
        data, invoke = self.search(self.responder([self.RACE[0]]))
        self.assertEqual((data['classification'], data['observed']), ('no_failure', None)); self.assertEqual(invoke.call_count, 1)
        self.assertNotIn('request', data['replay'])
        self.assertEqual(self.run_cli(['replay', '--bundle', str(self.out)])[0], 3)

    # Negative controls: automation limits are never counterexamples.

    def assert_unsolved(self, data, reason):
        self.assertEqual((data['classification'], data['reason']), ('unsolved', reason))
        self.assertFalse(data['is_program_bug_evidence'])

    def test_search_timeout_is_unsolved(self):
        def timeout(*_): raise TIMEOUT
        data, _ = self.search(timeout)
        self.assert_unsolved(data, 'timeout'); self.assertIsNone(data['contract'])
        code, _ = self.run_cli(['replay', '--bundle', str(self.out)])
        self.assertEqual(code, 2)

    def test_replay_timeout_of_an_observed_failure_is_unsolved(self):
        data, _ = self.search(self.responder(self.RACE, replay=TIMEOUT))
        self.assert_unsolved(data, 'replay_timeout'); self.assertEqual(data['replay']['status'], 'timeout')

    def test_unreproduced_replay_is_unsolved(self):
        data, _ = self.search(self.responder(self.RACE, replay=VALUE))
        self.assert_unsolved(data, 'replay_not_reproduced')

    def test_truncated_or_no_result_enumeration_without_failure_is_unsolved(self):
        data, _ = self.search(self.responder([self.RACE[0]], truncated=True))
        self.assert_unsolved(data, 'enumeration_truncated')
        data, _ = self.search(self.responder([self.RACE[0], ([1], [2], obs('bounded_no_result', '{"diverge":true}'), True)]))
        self.assert_unsolved(data, 'bounded_no_result')

    def test_prefix_capped_failure_cannot_be_replayed(self):
        data, invoke = self.search(self.responder([([1], [2], ILLEGAL, False)]))
        self.assert_unsolved(data, 'prefix_cap'); self.assertEqual(invoke.call_count, 1)

    def test_replay_process_error_is_setup_not_bug(self):
        data, _ = self.search(self.responder(self.RACE, replay=REPORT.Invalid('schedule rejected: unknown function')))
        self.assertEqual(data['classification'], 'setup_failure'); self.assertFalse(data['is_program_bug_evidence'])

    def test_verdict_table_never_calls_an_automation_limit_a_bug(self):
        for reason in sorted(CX.UNSOLVED_REASONS):
            for replay in ('verified', None):
                self.assertEqual(CX.verdict(automation=reason, replay=replay)[0], 'unsolved')
        for kind in ('search_cap', 'bounded_no_result', 'unspecified'):
            self.assertEqual(CX.verdict(kind=kind, replay='verified')[0], 'unsolved')
        for status in ('search_cap', 'bounded_no_result', 'unspecified_exclusion', 'host_difference'):
            self.assertEqual(CX.verdict(status=status, replay='verified')[0], 'unsolved')
        for status in ('input_failure', 'native_harness_failure'):
            self.assertEqual(CX.verdict(status=status, replay='verified')[0], 'setup_failure')
        for status in ('value_match', 'error_return_match', 'panic_match'):
            self.assertEqual(CX.verdict(status=status, replay='verified')[0], 'no_failure')
        self.assertEqual(CX.verdict(status='mismatch', replay='verified')[:2], ('counterexample', 'replayed_failure'))
        self.assertEqual(CX.verdict(kind='illegal')[0], 'candidate')
        tree = dict(truncated=False, saw_no_result=False)
        self.assertEqual(CX.verdict(tree=tree)[0], 'no_failure')
        self.assertEqual(CX.verdict(tree=dict(tree, truncated=True))[:2], ('unsolved', 'enumeration_truncated'))
        self.assertEqual(CX.verdict(tree=dict(tree, saw_no_result=True))[:2], ('unsolved', 'bounded_no_result'))
        with self.assertRaises(REPORT.Invalid): CX.verdict(automation='crashed')
        with self.assertRaises(REPORT.Invalid): CX.verdict(status='skipped')

    # Differential cases.

    def write_case(self, status, native, model, nkind, mkind, schedule=None):
        summary = self.root/'report.json'
        lines = {}
        for side, line in (('zig', native), ('lean', model)):
            p = self.root/'tests/diff/out'/side/'demo/run.jsonl'; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(line+'\n')
            lines[side] = hashlib.sha256((line+'\n').encode()).hexdigest()
        row = dict(schema=1, example='demo', function='run', input_index=1, input_sha256=hashlib.sha256(b'[]\n').hexdigest(),
                   native_kind=nkind, model_kind=mkind, native_sha256=lines['zig'], model_sha256=lines['lean'], status=status, legacy_bucket='x')
        if schedule: row['schedule'] = schedule
        Path(str(summary)+'.jsonl').write_text(json.dumps(dict(schema=1, status='skipped', example='other'))+'\n'+json.dumps(row)+'\n')
        summary.write_text(json.dumps(dict(schema=1, complete=True, qualified=False, runner_runtime_sources=REPORT.source_hashes(self.root))))
        return ['from-case', '--summary', str(summary), '--example', 'demo', '--function', 'run', '--output', str(self.out)]

    def test_sequential_mismatch_keeps_both_sides_and_stays_a_candidate(self):
        argv = self.write_case('mismatch', '{"ok":1}', '{"ok":2}', 'value', 'value')
        code, invoke = self.run_cli(argv + ['--replay'])
        data = json.loads(self.out.read_text())
        self.assertEqual(code, 0); invoke.assert_not_called()
        self.assertEqual((data['classification'], data['contract']['id']), ('candidate', 'native_correspondence'))
        self.assertEqual((data['native']['line'], data['observed']['line']), ('{"ok":1}', '{"ok":2}'))
        self.assertEqual(data['location']['localization'], 'function_only')
        self.assertIn('AIR2LEAN_EXAMPLES=demo', data['replay']['command'])

    def test_capped_case_is_unsolved_and_stale_case_rejected(self):
        cap = dict(prefix=[0], options=[2], runs=4, fuel=50, cap=4, status='capped', saw_no_result=False)
        argv = self.write_case('search_cap', '{"ok":1}', '{"fail":"Zig.Error.capped"}', 'value', 'search_cap', cap)
        self.run_cli(argv)
        self.assert_unsolved(json.loads(self.out.read_text()), 'search_cap')
        (self.root/'tests/diff/out/lean/demo/run.jsonl').write_text('{"ok":3}\n')
        with self.assertRaisesRegex(REPORT.Invalid, 'stale'): self.run_cli(argv)

    def test_witness_case_replays_padded_prefix(self):
        witness = dict(prefix=[1], options=[2, 2], runs=2, fuel=50, cap=8, status='witness', saw_no_result=False)
        argv = self.write_case('illegal_exclusion', '{"ok":0}', ILLEGAL['legacy_line'], 'value', 'illegal', witness)
        _, invoke = self.run_cli(argv + ['--replay'], self.responder(self.RACE))
        self.assertEqual(invoke.call_args.args[1]['prefix'], [1, 0])
        data = json.loads(self.out.read_text())
        self.assertEqual((data['classification'], data['contract']['id']), ('counterexample', 'no_illegal_behaviour'))
        (self.root/'ZigLean/Basic.lean').write_text('-- changed\n')
        with self.assertRaisesRegex(REPORT.Invalid, 'stale'): self.run_cli(argv + ['--replay'], self.responder(self.RACE))

    def test_real_atomics_air_localizes_the_relaxed_message_passing_race(self):
        loc = CX.localize(ROOT, 'atomics', 'mpRelaxed', 'illegal', None)
        lines = {(s['function'], s['tag'], s['zig_line']) for s in loc['candidate_sites']}
        self.assertIn(('atomics.mpRelaxed', 'load', 43), lines)              # reader: `... data else 0`
        self.assertIn(('atomics.mpWriterRelaxed', 'store_safe', 20), lines)  # writer: `c.data.* = 42`
        self.assertTrue(all(s['zig_file'] in (None, 'examples/atomics/atomics.zig') for s in loc['candidate_sites']))


if __name__ == '__main__':
    unittest.main()
