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
import re
import subprocess
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
        write(self.root / 'examples/ex/ex.zig', '')
        write(self.root / 'Proofs/Mod/Thm.lean', '')
        self.data = scratch_map()
        self.record()

    def record(self, **changes):
        """Write the kill ledger for the scratch mutate.sh: a is killed by a diff, b by a proof build."""
        blocks = mm.mutation_blocks(self.root)
        by = {'a': {'kind': 'diff', 'target': 'ex'}, 'b': {'kind': 'proof', 'target': 'Proofs.Mod.Thm'}}
        mutants = {n: {'killed_by': by[n], 'block_sha256': blocks[n],
                       'target_sha256': mm.target_sha256(self.root, by[n]['kind'], by[n]['target'])}
                   for n in blocks if n in by}
        mutants.update(changes)
        write(self.root / mm.KILLS, json.dumps({'schema': mm.KILLS_SCHEMA, 'mutants': mutants}))

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


class Kills(Scratch):
    def test_positive_control(self):
        self.assertEqual(self.problems(), [])

    def test_designated_mutant_without_recorded_kill_fails(self):
        ledger = json.loads((self.root / mm.KILLS).read_text())
        del ledger['mutants']['a']
        write(self.root / mm.KILLS, json.dumps(ledger))
        self.assertEqual(self.problems(), [f'{mm.KILLS}: a: designated mutant has no recorded kill'])
        (self.root / mm.KILLS).unlink()
        self.assertProblem(f'{mm.KILLS}: expected schema')

    def test_killer_must_exist_and_be_well_formed(self):
        blocks = mm.mutation_blocks(self.root)
        for by, needle in (({'kind': 'diff', 'target': 'gone'}, "regression 'gone' does not exist"),
                           ({'kind': 'proof', 'target': 'Proofs.Mod.Gone'}, 'does not exist'),
                           ({'kind': 'diff', 'target': '../ex'}, 'does not exist'),
                           ({'kind': 'survived', 'target': 'ex'}, 'needs killed_by'),
                           ({'kind': 'diff'}, 'needs killed_by')):
            self.record(a={'killed_by': by, 'block_sha256': blocks['a'], 'target_sha256': ''})
            self.assertProblem(needle)
        self.record(a={'killed_by': {'kind': 'diff', 'target': 'ex'}, 'block_sha256': blocks['a']})
        self.assertProblem('a: needs killed_by {kind: diff|proof, target}, block_sha256 and target_sha256')

    def test_kill_is_bound_to_the_inputs_of_its_regression(self):
        """H3 (docs/architecture-audit/claims.md): a kill recorded before its regression changed
        (an example's inputs, a proof module or a `Proofs` module it imports) is stale."""
        write(self.root / 'Proofs/Mod/Lemma.lean', '')
        write(self.root / 'Proofs/Mod/Thm.lean', 'import ZigLean\nimport Proofs.Mod.Lemma\n')
        self.record()
        self.assertEqual(mm.target_files(self.root, 'proof', 'Proofs.Mod.Thm'),
                         ['Proofs/Mod/Lemma.lean', 'Proofs/Mod/Thm.lean'])
        stale = 'kill recorded against other inputs of {} regression {}; rerun the mutation and `kills record`'
        for path, name, kind, target in (('tests/diff/ex/inputs/f.jsonl', 'a', 'diff', 'ex'),
                                         ('Proofs/Mod/Lemma.lean', 'b', 'proof', 'Proofs.Mod.Thm')):
            write(self.root / path, 'changed\n')
            self.assertEqual(self.problems(), [f'{mm.KILLS}: {name}: ' + stale.format(kind, target)])
            self.assertEqual(self.run_kills('verify', f'{name} killed {kind} {target}\n')[0], 1)
            self.assertEqual(self.run_kills('record', f'{name} killed {kind} {target}\n'), (0, ''))
            self.assertEqual(self.problems(), [])

    def test_kill_of_a_changed_mutation_is_stale(self):
        write(self.root / mm.MUTATE_SH, MUTATE.replace('one', 'one, edited'))
        self.assertEqual(self.problems(), [f'{mm.KILLS}: a: kill recorded for a different version of the mutation; '
                                           'rerun it and `kills record`'])

    def test_ledger_entry_for_a_removed_mutation_fails(self):
        self.record(gone={'killed_by': {'kind': 'diff', 'target': 'ex'}, 'block_sha256': 'x'})
        self.assertProblem('kill recorded for gone')

    def run_kills(self, command, lines):
        write(self.root / 'kill.log', lines)
        err = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
            code = mm.main(['kills', command, '--root', str(self.root), '--log', str(self.root / 'kill.log')])
        return code, err.getvalue()

    def test_record_refuses_a_survivor_and_verify_fails_on_it(self):
        before = (self.root / mm.KILLS).read_text()
        for command in ('record', 'verify'):
            code, err = self.run_kills(command, 'a survived diff ex\nb killed proof Proofs.Mod.Thm\n')
            self.assertEqual(code, 1)
            self.assertIn('a: survived', err)
        self.assertEqual((self.root / mm.KILLS).read_text(), before)

    def test_verify_requires_the_recorded_killer(self):
        self.assertEqual(self.run_kills('verify', 'a killed diff ex\nb killed proof Proofs.Mod.Thm\n'), (0, ''))
        code, err = self.run_kills('verify', 'a killed proof Proofs.Mod.Thm\n')
        self.assertEqual(code, 1)
        self.assertIn('a: killed by proof Proofs.Mod.Thm, ledger records', err)
        self.assertEqual(self.run_kills('verify', 'zz killed diff ex\n')[0], 1)

    def test_record_merges_kills_and_check_then_passes(self):
        (self.root / mm.KILLS).unlink()
        self.assertEqual(self.run_kills('record', 'a killed diff ex\n'), (0, ''))
        self.assertProblem('b: designated mutant has no recorded kill')
        self.assertEqual(self.run_kills('record', 'b killed proof Proofs.Mod.Thm\n'), (0, ''))
        self.assertEqual(self.problems(), [])

    def test_unrecorded_entry_is_a_listed_gap_until_a_kill_is_recorded(self):
        blocks = mm.mutation_blocks(self.root)
        self.record(a={'unrecorded': 'x86_64 only', 'block_sha256': blocks['a']})
        report = mm.analyze(self.root, self.data)
        self.assertEqual((report['problems'], report['kill_gaps']), ([], ['a: x86_64 only']))
        self.assertEqual(self.run_kills('verify', 'a killed diff ex\n'), (0, ''))
        self.assertEqual(self.run_kills('record', 'a killed diff ex\n'), (0, ''))
        self.assertEqual(mm.analyze(self.root, self.data)['kill_gaps'], [])
        self.record(a={'unrecorded': 'x86_64 only', 'block_sha256': 'stale'})
        self.assertProblem('unrecorded entry is for a different version')

    def test_malformed_log_is_an_input_error(self):
        err = io.StringIO()
        write(self.root / 'kill.log', 'a maybe diff ex\n')
        with contextlib.redirect_stderr(err):
            self.assertEqual(mm.main(['kills', 'verify', '--root', str(self.root), '--log', str(self.root / 'kill.log')]), 2)


class NoOpMutation(unittest.TestCase):
    """mutate.sh aborts, instead of reporting a result, when a mutation changed no source."""

    PAIRS = (('gen_file', 'gen_backup'), ('options_gen', 'options_backup'), ('variants_gen', 'variants_backup'),
             ('layout_gen', 'layout_backup'), ('slices_gen', 'slices_backup'), ('basic_lean', 'basic_backup'),
             ('lemmas_lean', 'lemmas_backup'), ('round_lean', 'round_backup'), ('mem_lean', 'mem_backup'),
             ('enc_lean', 'enc_backup'), ('alloc_lean', 'alloc_backup'), ('asm_zig', 'asm_backup'),
             ('vec_lean', 'vec_backup'), ('thread_lean', 'thread_backup'), ('sched_lean', 'sched_backup'),
             ('conc_lean', 'conc_backup'))

    def run_helper(self, changed):
        text = (ROOT / mm.MUTATE_SH).read_text()
        body = text[text.index('require_mutated() {'):]
        body = body[:body.index('\n}\n') + 3]
        with tempfile.TemporaryDirectory(prefix='air2lean-noop-') as tmp:
            lines = []
            for source, backup in self.PAIRS:
                write(Path(tmp) / source, 'changed\n' if source == changed else 'same\n')
                write(Path(tmp) / backup, 'same\n')
                lines += [f'{source}={tmp}/{source}', f'{backup}={tmp}/{backup}']
            script = '\n'.join(lines) + '\n' + body + '\nrequire_mutated "mutation (z)"\necho reached\n'
            return subprocess.run(['bash', '-c', script], capture_output=True, text=True)

    def test_unchanged_sources_abort(self):
        result = self.run_helper(None)
        self.assertEqual(result.returncode, 1)
        self.assertIn('mutation (z): the mutation changed no source file', result.stderr)
        self.assertNotIn('reached', result.stdout)

    def test_a_changed_source_continues(self):
        for source, _ in self.PAIRS:
            result = self.run_helper(source)
            self.assertEqual((result.returncode, result.stdout.strip()), (0, 'reached'), source)

    def test_every_reporting_path_requires_a_mutation(self):
        text = (ROOT / mm.MUTATE_SH).read_text()
        for function in ('proof_report', 'run_and_report'):
            body = text[text.index(f'\n{function}() {{'):]
            self.assertIn('require_mutated "$1"', body[:body.index('\n}\n')], function)

    def test_pairs_match_the_backups_mutate_sh_makes(self):
        text = (ROOT / mm.MUTATE_SH).read_text()
        self.assertEqual(set(self.PAIRS), set(re.findall(r'^cp "\$(\w+)" "\$(\w+_backup)"$', text, re.M)))


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
        self.record()
        self.assertEqual(self.problems(), [f'{mm.MUTATE_SH}: mutation c is mapped to no register ID'])
        # However the key is written: the unmapped gate reads the dictionary literal.
        write(self.root / mm.PY_MUTANTS, PY_MUTANTS.replace("}\n", '    "qm":\n        (),\n}\n'))
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
            (lambda r: r['L02'].update(mutants=5), 'entry must be an object'),
            (lambda r: r['L02'].update(categories='layout'), 'entry must be an object'),
            (lambda r: r['L02']['mutants'].append(mutant('swap', 'layout', ['tests/x/mutations.py'])), 'needs name, path, category'),
            (lambda r: r['L02']['mutants'].append(mutant('swap', ['layout'])), 'needs name, path, category'),
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
