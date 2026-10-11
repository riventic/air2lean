#!/usr/bin/env python3
"""W3 model-inclusion checker regressions on synthetic work directories. No Zig, Lean or Lake."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('inclusion', HERE / 'inclusion.py')
inclusion = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(inclusion)

KNOWN = {'divergence': 'D-X', 'reason': 'fixture', 'link': 'docs/std-models.md#caller-supplied-allocator-and-io'}


def write(path: Path, rows) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(''.join(r + '\n' for r in rows))


class Inclusion(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.work = Path(temp.name)

    def test_policy_inputs_cover_each_line_once_per_policy(self):
        src, dst = self.work / 'src', self.work / 'dst'
        for name in inclusion.LISTS:
            write(src / f'{name}.jsonl', ['{"bufs":[],"args":[3,7]}', '{"bufs":[[1]],"args":[null,8]}'])
        inclusion.policy_inputs(src, dst)
        out = [json.loads(line) for line in inclusion.lines(dst / 'evens.jsonl')]
        width = len(inclusion.policies())
        self.assertEqual(len(out), 2 * width)
        self.assertEqual([o['args'][0] for o in out[:width]], inclusion.policies())
        self.assertEqual([o['args'][1:] for o in out[width:]], [[8]] * width)
        self.assertEqual(out[0]['args'][0], None)

    def lists_fixture(self, native_line):
        width = len(inclusion.policies())
        model = ['{"ok":5,"bufs":["01"],"live":0}'] + ['{"ok":{"err":"OutOfMemory"},"bufs":["01"],"live":0}'] * (width - 1)
        for name in inclusion.LISTS:
            write(self.work / f'model-lists/tests/diff/out/lean/lists/{name}.jsonl', model)
            for kind in inclusion.ALLOCATORS:
                write(self.work / f'native-{kind}/tests/diff/out/zig/lists/{name}.jsonl', [native_line])

    def test_lists_inclusion_ignores_live_count(self):
        self.lists_fixture('{"ok":5,"bufs":["01"]}')
        rows = inclusion.lists_rows(self.work)
        self.assertEqual({r['status'] for r in rows}, {'pass'})
        self.lists_fixture('{"ok":{"err":"OutOfMemory"},"bufs":["01"]}')
        self.assertEqual({r['status'] for r in inclusion.lists_rows(self.work)}, {'pass'})

    def test_lists_value_outside_model_fails(self):
        self.lists_fixture('{"ok":6,"bufs":["01"]}')
        rows = inclusion.lists_rows(self.work)
        self.assertEqual({r['status'] for r in rows}, {'fail'})
        self.assertEqual(rows[0]['outside_model'], ['{"bufs":["01"],"ok":6}'])
        # A changed input buffer is an observation too.
        self.lists_fixture('{"ok":5,"bufs":["02"]}')
        self.assertEqual({r['status'] for r in inclusion.lists_rows(self.work)}, {'fail'})

    def test_cap_limited_input_is_unevaluated_not_included(self):
        width = len(inclusion.policies())
        oom = '{"ok":{"err":"OutOfMemory"},"bufs":[],"live":0}'
        for name in inclusion.LISTS:
            write(self.work / f'model-lists/tests/diff/out/lean/lists/{name}.jsonl', [oom] * width)
            for kind in inclusion.ALLOCATORS:
                write(self.work / f'native-{kind}/tests/diff/out/zig/lists/{name}.jsonl', ['{"ok":"7","bufs":[]}'])
        rows = inclusion.lists_rows(self.work)
        self.assertEqual({(r['status'], r['included'], r.get('unevaluated')) for r in rows}, {('pass', 0, 1)})

    def test_native_panic_maps_to_model_constructor(self):
        ctors = inclusion.panic_ctors()
        self.assertEqual(inclusion.canonical('{"fail":"integerOverflow"}', ctors),
                         inclusion.canonical('{"fail":"Zig.Error.overflow"}', ctors))
        self.assertNotEqual(inclusion.canonical('{"fail":"unknown"}', ctors),
                            inclusion.canonical('{"fail":"Zig.Error.panic"}', ctors))

    def io_fixture(self, native, model):
        for kind in inclusion.IOS:
            base = self.work / f'io-{kind}'
            raw = {f'{ex}.{n}': native for ex, names in inclusion.IO_FUNCTIONS.items() for n in names}
            raw.update({f'io_probe.{n}': native for n in inclusion.IO_PROBES})
            base.mkdir(parents=True, exist_ok=True)
            (base / 'native.json').write_text(json.dumps(raw))
            for ex, names in inclusion.IO_FUNCTIONS.items():
                for name in names:
                    write(base / f'tests/diff/out/lean/{ex}/{name}.jsonl', model)

    def test_io_hang_needs_a_model_deadlock(self):
        self.io_fixture([inclusion.HANG], [inclusion.DEADLOCK])
        self.assertEqual({r['status'] for r in inclusion.io_rows(self.work)}, {'pass'})
        self.io_fixture([inclusion.HANG], ['{"ok":5}'])
        self.assertEqual({r['status'] for r in inclusion.io_rows(self.work)}, {'fail'})
        # A data race admits any value, but not a hang; a capped search is no evidence.
        self.io_fixture(['{"ok":5}'], [inclusion.ILLEGAL])
        self.assertEqual({r['status'] for r in inclusion.io_rows(self.work)}, {'pass'})
        self.io_fixture([inclusion.HANG], [inclusion.ILLEGAL])
        self.assertEqual({r['status'] for r in inclusion.io_rows(self.work)}, {'fail'})
        self.io_fixture(['{"ok":5}'], [inclusion.CAPPED])
        rows = inclusion.io_rows(self.work)
        self.assertEqual({r['status'] for r in rows}, {'fail'})
        self.assertEqual(rows[0]['note'], 'capped schedule search')

    def test_probe_outcomes_strip_policy_labels(self):
        write(self.work / 'probe-model.txt', ['aliasProbe[default]=0', 'aliasProbe[fail0]=error.OutOfMemory',
                                              'cancelProbe=error:Zig.Error.deadlock'])
        found = inclusion.probe_outcomes(self.work / 'probe-model.txt')
        self.assertEqual(found['aliasProbe'], {'0', 'error.OutOfMemory'})
        self.assertEqual(found['cancelProbe'], {'error:Zig.Error.deadlock'})

    def test_judge(self):
        rows = [inclusion.row('a/new', ['1'], [False]), inclusion.row('a/known', ['2'], [False]),
                inclusion.row('a/fixed', ['3'], [True]), inclusion.row('a/ok', ['4'], [True])]
        problems = inclusion.judge(rows, {'a/known': KNOWN, 'a/fixed': KNOWN, 'a/gone': KNOWN})
        self.assertEqual(len(problems), 3, problems)
        self.assertTrue(any(p.startswith('a/new: NEW divergence') for p in problems))
        self.assertTrue(any(p.startswith('a/fixed: known divergence D-X no longer diverges') for p in problems))
        self.assertTrue(any(p.startswith('a/gone: known divergence names no checked row') for p in problems))
        self.assertEqual(rows[1]['status'], 'xfail')
        self.assertEqual(rows[1]['link'], KNOWN['link'])
        self.assertEqual(rows[3]['status'], 'pass')

    def test_expected_entries_need_reason_and_existing_link(self):
        path = self.work / 'expected.json'
        for entry in [dict(KNOWN, reason=''), {'divergence': 'D-X', 'link': KNOWN['link']},
                      dict(KNOWN, link='docs/missing.md#x')]:
            path.write_text(json.dumps({'schema': 'air2lean-model-inclusion-expected/1',
                                        'known_divergences': {'r': entry}}))
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                inclusion.load_expected(path)

    def test_committed_expectations_and_evidence(self):
        self.assertEqual(inclusion.validate(), 0)


if __name__ == '__main__':
    unittest.main()
