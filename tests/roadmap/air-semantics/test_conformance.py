"""conformance.py's comparison on fabricated outcomes (V01 stage 7): the causal controls.

    python3 -B tests/roadmap/air-semantics/test_conformance.py

No Lean and no Zig: `compare` gets interpreter records and a differential output directory
written here. An agreement of the three sides is counted by its kind; each single change of one
side (a value, a buffer byte, a panic kind, a returned error, a stuck run, an interpreter
`.illegal` on an input that is not pinned) is a disagreement or a stuck case, never an
agreement; and a differential summary of another Zig version or host is refused.
"""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


conformance = load(HERE / 'conformance.py', 'conformance')
dr = conformance.load_script('diff-report')

HOST, VERSION = 'Linux-x86_64', '0.17.1'
# (input line, native line, native kind, model line, model kind): one case of each agreement kind.
CASES = [
    ('[1,2]', '{"ok":3}', 'value', '{"ok":3}', 'value'),
    ('[250,9]', '{"fail":"integerOverflow"}', 'native_panic', '{"fail":"Zig.Error.overflow"}', 'model_panic'),
    ('[0,0]', '{"ok":{"err":"Zero"}}', 'error_return', '{"ok":{"err":"Zero"}}', 'error_return'),
    ('{"bufs":[[1,2]],"args":[]}', '{"ok":null,"bufs":["0102"]}', 'value', '{"ok":null,"bufs":["01??"]}', 'value'),
]


class Compare(unittest.TestCase):
    def run_compare(self, sem, *, version=VERSION, cases=CASES, pins=''):
        """`compare` on `cases` with the interpreter outcomes `sem` ((line, kind) per case)."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inputs = root / 'tests/diff/ex/inputs'
            inputs.mkdir(parents=True)
            (inputs / 'f.jsonl').write_text(''.join(c[0] + '\n' for c in cases))
            (root / 'tests/diff/ex/unspecified.txt').write_text(pins)
            out = root / 'out'
            for side, line, kind in (('zig', 1, 2), ('lean', 3, 4)):
                directory = out / side / 'ex'
                directory.mkdir(parents=True)
                (directory / 'f.jsonl').write_text(''.join(c[line] + '\n' for c in cases))
                (directory / 'f.jsonl.outcomes').write_text(''.join(
                    json.dumps({'schema': 1, 'kind': c[kind], 'legacy_line': c[line]}) + '\n' for c in cases))
            (out / 'report.json').write_text(json.dumps(
                {'complete': True, 'profile': {'host': HOST, 'zig_version': version}}))
            records = {('ex', 'f'): {'status': 'run', 'outcomes': [{'line': l, 'kind': k} for l, k in sem]}}
            saved, conformance.ROOT = conformance.ROOT, root
            try:
                return conformance.compare(dr, VERSION, records, [('ex', 'f')], out, out / 'report.json',
                                           HOST, io.StringIO())
            finally:
                conformance.ROOT = saved

    def agreeing(self):
        return [(c[3], c[4]) for c in CASES]

    def test_agreement_is_counted_by_kind(self):
        agreed, disagreements, stuck = self.run_compare(self.agreeing())
        self.assertEqual((disagreements, dict(stuck)), ([], {}))
        self.assertEqual(dict(agreed), {'value_match': 2, 'panic_match': 1, 'error_return_match': 1})

    def test_each_single_change_is_a_disagreement(self):
        changes = {
            0: ('{"ok":4}', 'value'),                                    # another value
            1: ('{"fail":"Zig.Error.outOfBounds"}', 'model_panic'),      # another panic kind
            2: ('{"ok":{"err":"Other"}}', 'error_return'),               # another returned error
            3: ('{"ok":null,"bufs":["0103"]}', 'value'),                 # another buffer byte
        }
        for index, change in changes.items():
            sem = self.agreeing()
            sem[index] = change
            agreed, disagreements, stuck = self.run_compare(sem)
            self.assertEqual([d['input_line'] for d in disagreements], [index + 1], change)
            self.assertEqual(sum(agreed.values()), len(CASES) - 1)
        # The interpreter fully defines a byte that the model leaves half undefined: both match the
        # native bytes, but the two Lean sides differ.
        sem = self.agreeing()
        sem[3] = ('{"ok":null,"bufs":["0102"]}', 'value')
        _, disagreements, _ = self.run_compare(sem)
        self.assertEqual([(d['interpreter_vs_model'], d['interpreter_vs_native']) for d in disagreements],
                         [('differs', 'value_match')])

    def test_a_panic_against_a_value_and_a_value_against_a_panic(self):
        sem = self.agreeing()
        sem[0] = ('{"fail":"Zig.Error.overflow"}', 'model_panic')
        sem[1] = ('{"ok":3}', 'value')
        _, disagreements, _ = self.run_compare(sem)
        self.assertEqual([d['input_line'] for d in disagreements], [1, 2])

    def test_a_stuck_run_is_never_an_agreement(self):
        sem = self.agreeing()
        sem[2] = ('{"stuck":true}', 'stuck')
        agreed, disagreements, stuck = self.run_compare(sem)
        self.assertEqual((disagreements, dict(stuck)), ([], {('ex', 'f'): 1}))
        self.assertEqual(sum(agreed.values()), len(CASES) - 1)

    def test_illegal_agrees_only_on_a_pinned_input(self):
        case = ('[7]', '{"ok":1}', 'value', '{"fail":"Zig.Error.illegal"}', 'illegal')
        sem = [('{"fail":"Zig.Error.illegal"}', 'illegal')]
        _, disagreements, _ = self.run_compare(sem, cases=[case])
        self.assertEqual(len(disagreements), 1)
        sha = hashlib.sha256(b'[7]\n').hexdigest()
        agreed, disagreements, _ = self.run_compare(sem, cases=[case], pins=f'f {sha} 1 a pinned illegal input\n')
        self.assertEqual((dict(agreed), disagreements), ({'illegal_exclusion': 1}, []))
        # On the pinned input the interpreter must be illegal too: the native value is no match.
        _, disagreements, _ = self.run_compare([('{"ok":1}', 'value')], cases=[case],
                                               pins=f'f {sha} 1 a pinned illegal input\n')
        self.assertEqual(len(disagreements), 1)

    def test_another_differential_run_is_refused(self):
        with self.assertRaises(SystemExit):
            self.run_compare(self.agreeing(), version='0.16.0')

    def test_reason_table_counts_shared_instructions_once(self):
        reason = lambda where, text, n: {'where': where, 'reason': text, 'insts': n}
        records = {
            ('ex', 'f'): {'status': 'skip', 'reasons': [reason('ex.h', 'shift: integer shifts (not staged)', 2)]},
            ('ex', 'g'): {'status': 'skip', 'reasons': [reason('ex.h', 'shift: integer shifts (not staged)', 2),
                                                         reason('ex.g', 'load: struct values (stage 4)', 1)]},
            ('ex', 'k'): {'status': 'run', 'outcomes': []},
        }
        table = conformance.reason_table(records)
        self.assertEqual(table['shift: integer shifts (not staged)'], [2, 1, 2])
        self.assertEqual(table['load: struct values (stage 4)'], [1, 0, 1])
        self.assertEqual(conformance.stage_of('load: struct values (stage 4)'), 'stage 4')
        self.assertEqual(conformance.stage_of('call: a function outside the program (an external, stage 6)'),
                         'stage 6')
        self.assertEqual(conformance.stage_of('harness: an input field other than bufs and args'), 'harness')


if __name__ == '__main__':
    unittest.main()
