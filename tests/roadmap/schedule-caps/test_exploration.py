#!/usr/bin/env python3
"""Q03 schedule-coverage accounting on synthetic reports and receipts; no compiler or model process."""
import contextlib
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
SPEC = importlib.util.spec_from_file_location('diff_report', ROOT/'scripts/diff-report.py')
REPORT = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(REPORT)
SPEC = importlib.util.spec_from_file_location('schedule_cli', ROOT/'scripts/schedules.py')
CLI = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(CLI)
K = REPORT.Kind

class Exploration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name); self.summary = self.root/'summary.json'
        (self.root/'examples/basic').mkdir(parents=True)
        p = self.root/'ZigLean/Basic.lean'; p.parent.mkdir(); p.write_text('-- runtime\n')

    def seed(self, cases, fn='foo'):
        """cases: [(native, model, native kind, model kind, search)]."""
        dirs = {n: self.root/'tests/diff'/n for n in ('basic/inputs', 'out/zig/basic', 'out/lean/basic')}
        for d in dirs.values(): d.mkdir(parents=True, exist_ok=True)
        (dirs['basic/inputs']/f'{fn}.jsonl').write_text(''.join(f'[{i}]\n' for i in range(len(cases))))
        for side, pos in (('zig', 0), ('lean', 1)):
            out = dirs['out/'+side+'/basic']/f'{fn}.jsonl'; rows = []; metas = []
            for case in cases:
                value, kind = case[pos], case[2+pos]
                rows.append(json.dumps(value, separators=(',', ':'))+'\n')
                meta = {'schema': 1, 'kind': kind.value, 'legacy': value}
                if side == 'lean' and case[4]: meta['search'] = case[4]
                metas.append(json.dumps(meta)+'\n')
            out.write_text(''.join(rows)); Path(str(out)+'.outcomes').write_text(''.join(metas))

    def search(self, status, runs=3, cap=3, saw=False):
        return dict(prefix=[0], options=[2], runs=runs, fuel=50, cap=cap, status=status, saw_no_result=saw)

    def compare(self, receipts=()):
        code = REPORT.compare(self.root, ['basic'], '0.16.0', 'Linux-x86_64', self.summary, list(map(str, receipts)))
        return code, json.loads(self.summary.read_text())

    def scope(self, data, fn='foo'):
        return next(s for s in data['schedule_exploration']['scopes'] if s['function'] == fn)

    def receipt(self, name, *, mode='enumerate', truncated=False, fn='foo'):
        """Write a schedules.py receipt through the real CLI with a mocked model process."""
        output = self.root/name
        def respond(_, request, __):
            obs = dict(schema=1, kind='value', legacy_line='{"ok":1}')
            full = dict(prefix=request.get('prefix', [0]), options=[2], choice_count=1, trace_complete=True, observation=obs)
            executions = [full]
            if request['mode'] == 'enumerate' and not truncated:
                executions.append(dict(full, prefix=[1]))
            if truncated:
                executions.append(dict(prefix=[1], options=[2], choice_count=2, trace_complete=False, observation=obs))
            return dict(schema=1, qualified=False, mode=request['mode'], fuel=request['fuel'], node_cap=request['node_cap'],
                        prefix_cap=request['prefix_cap'], runs=len(executions), truncated=truncated, node_cap_reached=False,
                        prefix_cap_reached=truncated, exploration_complete=request['mode'] == 'enumerate' and not truncated,
                        saw_no_result=False, executions=executions, outcomes=[obs])
        args = CLI.parser().parse_args(['enumerate', '--example', 'basic', '--function', fn, '--fuel', '50',
                                        '--node-cap', '8', '--prefix-cap', '1', '--output', str(output)])
        with patch.object(CLI, 'invoke', side_effect=respond): CLI.execute(args, self.root)
        if mode == 'replay':
            enum = output; output = self.root/('replay-'+name)
            args = CLI.parser().parse_args(['replay', '--receipt', str(enum), '--output', str(output)])
            with patch.object(CLI, 'invoke', side_effect=respond): CLI.execute(args, self.root)
        return output

    # Positive controls.

    def test_witness_matches_count_as_bounded_correspondence_only(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('witness', runs=2)),
                   ({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, None)])
        code, data = self.compare()
        self.assertEqual(code, 0); self.assertEqual(data['exact_matches'], 2)
        x = data['schedule_exploration']; o = x['observed_matching']
        self.assertEqual((o['searched_cases'], o['unsearched_cases'], o['schedules_explored']), (1, 1, 2))
        self.assertEqual(o['status_counts'], dict(witness=1, exhausted=0, bounded=0, capped=0))
        self.assertEqual((o['fuel'], o['cap'], o['replayable_witnesses']), ([50], [3], 1))
        self.assertEqual(x['bounded_enumeration']['receipts'], 0)
        self.assertEqual((x['correspondence_scopes'], x['capped_scopes']), (1, 0))
        scope = self.scope(data)
        self.assertTrue(scope['counts_as_correspondence']); self.assertFalse(scope['qualified'])
        self.assertFalse(x['qualified']); self.assertFalse(data['qualified'])
        self.assertEqual(scope['blockers'], ['proof_applicability_not_evaluated'])

    def test_reduction_is_declared_absent_and_unproved(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, None)])
        reduction = self.compare()[1]['schedule_exploration']['reduction']
        self.assertEqual((reduction['technique'], reduction['soundness']), ('none', 'not_proved'))

    def test_enumeration_counters_are_separate_from_observed_matching(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('witness', runs=1))])
        receipt = self.receipt('enum.json')
        code, data = self.compare([receipt])
        x = data['schedule_exploration']; e = x['bounded_enumeration']; o = x['observed_matching']
        self.assertEqual(code, 0)
        self.assertEqual((o['searched_cases'], o['schedules_explored']), (1, 1))
        self.assertEqual((e['receipts'], e['schedules_explored'], e['complete'], e['truncated'], e['replay_seeds']), (1, 2, 1, 0, 2))
        self.assertEqual((e['fuel'], e['node_cap'], e['prefix_cap']), ([50], [8], [1]))
        row = x['enumeration_receipts'][0]
        self.assertEqual((row['input_index'], row['replay_seed_indices'], row['exploration_complete']), (1, [0, 1], True))
        self.assertTrue(self.scope(data)['counts_as_correspondence'])
        self.assertEqual(data['exact_matches'], 1)

    def test_replay_receipts_are_not_enumeration_coverage(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, None)])
        e = self.compare([self.receipt('enum.json', mode='replay')])[1]['schedule_exploration']['bounded_enumeration']
        self.assertEqual((e['receipts'], e['replays'], e['schedules_explored']), (0, 1, 0))

    def test_cli_headline_states_schedules_and_limits(self):
        self.seed([({'ok': 1}, {'fail': 'Zig.Error.capped'}, K.VALUE, K.SEARCH_CAP, self.search('capped'))])
        (self.root/'tests/diff/basic/capped.txt').write_text('foo 1\n')
        receipt = self.receipt('enum.json', truncated=True)
        out = io.StringIO()
        argv = ['diff-report.py', 'compare', '--summary', str(self.summary), '--root', str(self.root),
                '--examples', 'basic', '--schedule-receipts', str(receipt)]
        with patch.object(sys, 'argv', argv), contextlib.redirect_stdout(out): code = REPORT.main()
        self.assertEqual(code, 0)
        line = out.getvalue().strip()
        for part in ('SCHEDULES:', 'runs=3', 'capped=1', 'fuel=[50]', 'cap=[3]', 'receipts=1', 'truncated=1',
                     'node_cap=[8]', 'prefix_cap=[1]', 'replay_seeds=1', 'correspondence_scopes=0', 'capped_scopes=1',
                     'reduction=none', 'qualified=false'):
            self.assertIn(part, line)

    # Negative controls: caps can never be demonstrated correspondence.

    def test_capped_value_match_lands_in_cap_bucket(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('capped'))])
        code, data = self.compare()
        self.assertEqual(code, 1)
        self.assertEqual(data['counts'], {'search_cap': 1}); self.assertEqual(data['exact_matches'], 0)
        self.assertEqual(data['legacy_counts'], {'capped': 1}); self.assertEqual(data['mutation_eligible'], 0)
        x = data['schedule_exploration']; scope = self.scope(data)
        self.assertEqual(x['capped_cases'], [dict(example='basic', function='foo', input_index=1, status='search_cap', runs=3, cap=3, fuel=50)])
        self.assertTrue(scope['capped']); self.assertFalse(scope['counts_as_correspondence']); self.assertFalse(scope['qualified'])
        self.assertIn('search_cap', scope['blockers'])
        self.assertEqual((x['correspondence_scopes'], x['capped_scopes']), (0, 1))

    def test_capped_panic_match_lands_in_cap_bucket(self):
        self.seed([({'fail': 'integerOverflow'}, {'fail': 'Zig.Error.overflow'}, K.NATIVE_PANIC, K.MODEL_PANIC, self.search('capped'))])
        data = self.compare()[1]
        self.assertEqual(data['counts'], {'search_cap': 1}); self.assertEqual(data['legacy_counts'], {'capped': 1})
        self.assertFalse(self.scope(data)['counts_as_correspondence'])

    def test_one_capped_case_disqualifies_otherwise_matching_scope(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('witness', runs=1)),
                   ({'ok': 1}, {'fail': 'Zig.Error.illegal'}, K.VALUE, K.ILLEGAL, self.search('capped'))])
        data = self.compare()[1]
        self.assertEqual(data['counts'], {'value_match': 1, 'illegal_exclusion': 1})
        scope = self.scope(data)
        self.assertTrue(scope['capped']); self.assertFalse(scope['counts_as_correspondence'])
        self.assertEqual(data['schedule_exploration']['capped_cases'][0]['status'], 'illegal_exclusion')

    def test_truncated_enumeration_disqualifies_matching_scope(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('witness', runs=1))])
        code, data = self.compare([self.receipt('enum.json', truncated=True)])
        self.assertEqual(code, 0); self.assertEqual(data['exact_matches'], 1)
        scope = self.scope(data); e = data['schedule_exploration']['bounded_enumeration']
        self.assertEqual((e['truncated'], e['complete'], e['prefix_cap_reached'], e['replay_seeds']), (1, 0, 1, 1))
        self.assertTrue(scope['capped']); self.assertFalse(scope['counts_as_correspondence'])
        self.assertIn('enumeration_truncated', scope['blockers'])
        self.assertEqual(data['schedule_exploration']['correspondence_scopes'], 0)

    def test_bounded_no_result_blocks_correspondence_but_is_not_cap(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, self.search('witness', runs=2, saw=True))])
        scope = self.scope(self.compare()[1])
        self.assertFalse(scope['capped']); self.assertFalse(scope['counts_as_correspondence'])
        self.assertIn('bounded_no_result', scope['blockers'])

    def test_capped_status_must_consume_its_run_cap(self):
        self.seed([({'ok': 1}, {'fail': 'Zig.Error.capped'}, K.VALUE, K.SEARCH_CAP, self.search('capped', runs=2, cap=3))])
        with self.assertRaisesRegex(REPORT.Invalid, 'run cap'): self.compare()

    def test_stale_foreign_or_inconsistent_receipts_are_rejected(self):
        self.seed([({'ok': 1}, {'ok': 1}, K.VALUE, K.VALUE, None)])
        receipt = self.receipt('enum.json'); original = receipt.read_text()
        data = json.loads(original)
        for mutate, error in [(lambda d: d['result'].update(exploration_complete=False), 'exploration flag'),
                              (lambda d: d['result'].update(truncated=True), 'cap flags'),
                              (lambda d: d['request'].update(example='other'), 'selected examples'),
                              (lambda d: d.update(qualified=True), 'unsupported receipt'),
                              (lambda d: d.update(input_sha256='0'*64), 'stale input')]:
            changed = json.loads(original); mutate(changed); receipt.write_text(json.dumps(changed))
            with self.assertRaisesRegex(REPORT.Invalid, error): self.compare([receipt])
        receipt.write_text(original)
        (self.root/'ZigLean/Basic.lean').write_text('-- changed\n')
        with self.assertRaisesRegex(REPORT.Invalid, 'stale runner'): self.compare([receipt])
        with self.assertRaisesRegex(REPORT.Invalid, 'receipt list'): self.compare([receipt, receipt])
        self.assertEqual(data['qualified'], False)

if __name__ == '__main__': unittest.main()
