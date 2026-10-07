#!/usr/bin/env python3
"""Q02 mutation-map checker and Python mutant runner regressions, with negative controls.

No Lean, Lake or Zig: the checker reads committed text; the runner tests run only the
float-semantics label tests in memory.
"""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


mm = load('mutation_map', 'scripts/mutation-map.py')
runner = load('q02_mutants', 'tests/roadmap/mutation-map/mutants.py')

ROADMAP = '''# Roadmap
| ID | Requirement | Status | Bounded status and remaining scope |
|---|---|---|---|
| T01 | Profiles | complete | done |
| L02 | Bit operations | partial | more |
'''
MUTATE = 'echo "== mutation (a) one"\necho "== mutation (b) two"\n'
PY_MUTANTS = "MUTANTS = {\n    'pm': (\n    ),\n}\n"
GEN = "MUTANTS = {'swap': 1, \"drop\": 2}\n"


def mutant(name, category, path='tests/x/mutations.py', **extra):
    return dict(name=name, path=path, category=category, **extra)


def scratch_map():
    neg = {'path': 'tests/x/test_neg.py', 'anchor': 'def test_neg'}
    return {'schema': mm.SCHEMA, 'requirements': {
        'T01': {'categories': ['profile-selection'], 'negative_tests': [neg],
                'mutants': [mutant('pm', 'profile-selection', mm.PY_MUTANTS),
                            mutant('a', 'forwarding', mm.MUTATE_SH)]},
        'L02': {'categories': ['layout'], 'negative_tests': [],
                'mutants': [mutant('b', 'layout', mm.MUTATE_SH), mutant('swap', 'operand-order'),
                            mutant('drop', 'failure-cleanup'),
                            mutant('inline', 'invariant-transfer', 'tests/x/check.sh', anchor='capture2 capture1')]}}}


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


class Scratch(unittest.TestCase):
    """A private repository holding exactly the files the checker reads."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='air2lean-mutation-map-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        write(self.root / 'ROADMAP.md', ROADMAP)
        write(self.root / mm.MUTATE_SH, MUTATE)
        write(self.root / mm.SHARDS, 'a\nb\n')
        write(self.root / mm.PY_MUTANTS, PY_MUTANTS)
        write(self.root / 'tests/x/mutations.py', GEN)
        write(self.root / 'tests/x/check.sh', 'worker capture0 capture2 capture1\n')
        write(self.root / 'tests/x/test_neg.py', 'def test_neg(self): pass\n')
        self.data = scratch_map()

    def problems(self, data=None):
        return mm.analyze(self.root, self.data if data is None else data)['problems']

    def assertProblem(self, needle, data=None):
        problems = self.problems(data)
        self.assertTrue(any(needle in p for p in problems), problems)


class Committed(unittest.TestCase):
    def test_committed_map_passes(self):
        report = mm.analyze(ROOT)
        self.assertEqual(report['problems'], [])
        for category in mm.CATEGORIES:
            self.assertTrue(report['categories'][category], category)

    def test_committed_map_names_every_register_id_once(self):
        data = json.loads((ROOT / mm.MAP).read_text())
        self.assertEqual(list(data['requirements']), [rid for rid, _ in mm.register(ROOT)])

    def test_cli_exit_codes(self):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            self.assertEqual(mm.main(['check']), 0)
            self.assertEqual(mm.main(['check', '--root', str(ROOT / 'tests')]), 2)
        self.assertIn('mutation map ok', out.getvalue())


class Map(Scratch):
    def test_positive_control(self):
        report = mm.analyze(self.root, self.data)
        self.assertEqual(report['problems'], [])
        self.assertEqual(report['gaps'], [{'id': 'L02', 'status': 'partial', 'lacks': ['negative tests']}])

    def test_complete_row_without_mutant_fails(self):
        self.data['requirements']['T01']['mutants'] = []
        self.data['requirements']['L02']['mutants'] += [mutant('pm', 'profile-selection', mm.PY_MUTANTS),
                                                        mutant('a', 'forwarding', mm.MUTATE_SH)]
        self.assertEqual(self.problems(), ['T01: complete row lacks designated mutants; mutants for profile-selection'])

    def test_complete_row_without_negative_test_fails(self):
        self.data['requirements']['T01']['negative_tests'] = []
        self.assertEqual(self.problems(), ['T01: complete row lacks negative tests'])

    def test_declared_category_gap_fails_only_complete_rows(self):
        self.data['requirements']['T01']['categories'].append('layout')
        self.assertEqual(self.problems(), ['T01: complete row lacks mutants for layout'])
        self.data['requirements']['T01']['categories'].pop()
        self.data['requirements']['L02']['categories'].append('forwarding')
        report = mm.analyze(self.root, self.data)
        self.assertEqual(report['problems'], [])
        self.assertEqual(report['gaps'][0]['lacks'], ['negative tests', 'mutants for forwarding'])

    def test_register_classification_comes_from_roadmap(self):
        write(self.root / 'ROADMAP.md', ROADMAP.replace('| L02 | Bit operations | partial |', '| L02 | Bit operations | complete |'))
        self.assertEqual(self.problems(), ['L02: complete row lacks negative tests'])

    def test_missing_test_file_or_anchor_fails(self):
        self.data['requirements']['T01']['negative_tests'] = [{'path': 'tests/x/test_gone.py', 'anchor': 'def test_neg'}]
        self.assertProblem('missing file tests/x/test_gone.py')
        self.data['requirements']['T01']['negative_tests'] = [{'path': 'tests/x/test_neg.py', 'anchor': 'def test_other'}]
        self.assertProblem("anchor 'def test_other' not in tests/x/test_neg.py")
        self.data['requirements']['T01']['negative_tests'] = [{'path': 'tests/x/test_neg.py'}]
        self.assertProblem('needs exactly a path and a nonempty anchor')

    def test_missing_mutant_fails(self):
        cases = [
            (mutant('c', 'forwarding', mm.MUTATE_SH), 'has no sharded mutation (c)'),
            (mutant('nope', 'forwarding', mm.PY_MUTANTS), 'has no mutant nope'),
            (mutant('absent', 'forwarding'), "no mutant named 'absent'"),
            (mutant('inline', 'forwarding', 'tests/x/check.sh', anchor='capture1 capture2 capture0'), 'anchor'),
            (mutant('x', 'forwarding', 'tests/x/missing.py'), 'missing file tests/x/missing.py'),
        ]
        for extra, needle in cases:
            data = copy.deepcopy(self.data)
            data['requirements']['L02']['mutants'].append(extra)
            self.assertProblem(needle, data)

    def test_unsharded_mutate_sh_label_fails(self):
        write(self.root / mm.SHARDS, 'a\n')
        self.assertProblem('has no sharded mutation (b)')

    def test_unmapped_mutation_fails(self):
        write(self.root / mm.MUTATE_SH, MUTATE + 'echo "== mutation (c) three"\n')
        write(self.root / mm.SHARDS, 'a\nb\nc\n')
        self.assertEqual(self.problems(), [f'{mm.MUTATE_SH}: mutation c is mapped to no register ID'])
        write(self.root / mm.PY_MUTANTS, PY_MUTANTS.replace("}\n", "    'qm': (\n    ),\n}\n"))
        self.assertProblem(f'{mm.PY_MUTANTS}: mutation qm is mapped to no register ID')

    def test_category_without_any_mutant_fails(self):
        self.data['requirements']['L02']['mutants'][1]['category'] = 'other'
        self.assertEqual(self.problems(), ['category operand-order: no designated mutant in the map'])

    def test_register_id_mismatch_fails(self):
        entry = self.data['requirements'].pop('L02')
        self.assertProblem(f'L02: register ID missing from {mm.MAP}')
        self.data['requirements']['L02'] = entry
        self.data['requirements']['Z99'] = {'categories': [], 'negative_tests': [], 'mutants': []}
        self.assertProblem('Z99: not a ROADMAP.md register ID')

    def test_malformed_entries_fail(self):
        cases = [
            (lambda r: r['L02']['mutants'].append(mutant('swap', 'renaming')), "unknown category 'renaming'"),
            (lambda r: r['L02']['mutants'].append(mutant('swap', 'layout')), 'duplicate mutant swap'),
            (lambda r: r['L02']['mutants'].append(mutant('swap', 'layout', '../x/mutations.py')), 'repository-relative'),
            (lambda r: r['L02']['mutants'].append(mutant('swap', 'layout', '/etc/passwd')), 'repository-relative'),
            (lambda r: r['L02']['mutants'].append({'name': 'swap', 'path': 'tests/x/mutations.py'}), 'needs name, path, category'),
            (lambda r: r['L02']['categories'].append('renaming'), 'categories must be distinct names'),
            (lambda r: r['L02'].update(status='complete'), 'entry must be an object'),
        ]
        for change, needle in cases:
            data = copy.deepcopy(self.data)
            change(data['requirements'])
            self.assertProblem(needle, data)
        self.assertProblem('expected schema', {'schema': 'other', 'requirements': {}})


FLOAT_TEST = 'tests/roadmap/float-semantics/test_labels.py'
FLOAT_KILL = ('SourceTests.test_compiler_rt_label_needs_compiler_rt_translation',)
ARGS_RETURN = "            return tokens[i + 1]\n"


def float_mutant(replacement, anchor=ARGS_RETURN):
    return {'probe': ('scripts/float-semantics.py', anchor, replacement, FLOAT_TEST, 'fs', FLOAT_KILL)}


class Runner(unittest.TestCase):
    def test_real_mutant_is_killed_by_a_named_failure(self):
        killed = runner.run_mutant('float-args-selection-ignored')
        self.assertEqual([k.rsplit('.', 1)[-1] for k in killed], ['test_compiler_rt_label_needs_compiler_rt_translation'])

    def test_crashing_mutant_is_not_a_kill(self):
        with self.assertRaisesRegex(AssertionError, 'errors only'):
            runner.run_mutant('probe', float_mutant("            raise RuntimeError('crash')\n"))

    def test_equivalent_mutant_survives(self):
        with self.assertRaisesRegex(AssertionError, 'no failing test'):
            runner.run_mutant('probe', float_mutant("            return tokens[i+1]\n"))

    def test_missing_or_ambiguous_anchor_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'exactly once'):
            runner.run_mutant('probe', float_mutant('x', anchor='no such source text'))
        with self.assertRaisesRegex(ValueError, 'exactly once'):
            runner.run_mutant('probe', float_mutant('x', anchor='return'))

    def test_failing_control_is_rejected(self):
        mutants = float_mutant("            return 'ieee'\n")
        script, anchor, replacement, test, binding, _ = mutants['probe']
        mutants['probe'] = (script, anchor, replacement, test, binding, ('SourceTests.test_no_such_test',))
        with self.assertRaisesRegex(AssertionError, 'control does not pass'):
            runner.run_mutant('probe', mutants)

    def test_every_mutant_targets_one_anchor_and_existing_tests(self):
        for name, (script, anchor, _, test, binding, kills) in runner.MUTANTS.items():
            self.assertEqual((ROOT / script).read_text().count(anchor), 1, name)
            module = runner.load_test_module(test)
            self.assertTrue(hasattr(module, binding), name)
            for kill in kills:
                cls, method = kill.split('.')
                self.assertTrue(hasattr(getattr(module, cls), method), (name, kill))


if __name__ == '__main__':
    unittest.main()
