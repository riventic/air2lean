#!/usr/bin/env python3
"""Q04 per-version/target accounting and legacy-claim regressions.

No Zig, Lake or Lean process: one test drives the real diff-report producer on a mocked
native/model output tree, one re-checks the committed CI tables, the rest use hand-built
summaries and negative controls.
"""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('air2lean_accounting', ROOT/'scripts/accounting.py')
ACC = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(ACC)
EXAMPLES = sorted(p.name for p in (ROOT/'examples').iterdir() if p.is_dir())
IN_QUALIFICATION = {'0.17.0'}
CLAIMED = {  # README's default selections (x86_64); the committed-tree test pins them to CI.
    '0.17.0': [e for e in EXAMPLES if e != 'threadsync'],  # in qualification; full CI job
    '0.16.0': [e for e in EXAMPLES if e != 'threadsync'],
    '0.15.2': [e for e in EXAMPLES if e not in ('iogroup', 'sync')],
}


def summary(version='0.16.0', host='Linux-x86_64', counts=None, examples=None, **extra):
    counts = counts if counts is not None else {
        'value_match': 70, 'error_return_match': 5, 'panic_match': 10, 'host_difference': 3,
        'illegal_exclusion': 4, 'unspecified_exclusion': 2, 'search_cap': 1, 'bounded_no_result': 1}
    examples = examples if examples is not None else CLAIMED.get(version, ['basic'])
    exact = sum(counts.get(s, 0) for s in ('value_match', 'error_return_match', 'panic_match'))
    data = {'schema': 1, 'complete': True, 'qualified': False,
            'profile': {'zig_version': version, 'host': host},
            'case_count': sum(counts.values()), 'counts': counts, 'exact_matches': exact,
            'setup_failures': counts.get('input_failure', 0) + counts.get('native_harness_failure', 0),
            'skipped_examples': len(EXAMPLES) - len(examples), 'skipped_functions': 3,
            'proof_applicability': 'not_evaluated_by_differential_runner',
            'proof_exclusions': [{'example': e, 'reason': 'proof_applicability_not_evaluated', 'sources': []}
                                 for e in examples]}
    data.update(extra)
    return data


def run(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = ACC.main(list(map(str, args)))
    return code, out.getvalue() + err.getvalue()


class Temp(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean accounting ')
        self.addCleanup(self.temp.cleanup)
        self.dir = Path(self.temp.name)

    def put(self, name, data):
        path = self.dir/name
        path.write_text(json.dumps(data))
        return path

    def assertFails(self, needle, *args, code=1):
        status, output = run(*args)
        self.assertEqual(status, code, output)
        self.assertIn(needle, output)
        return output


class Publish(Temp):
    def test_columns_cover_every_comparison_status(self):
        self.assertEqual({s for s in ACC.S if s != ACC.S.SKIPPED}, set(ACC.COLUMN))
        self.assertEqual(set(ACC.COLUMN.values()), set(ACC.PARTITION))

    def test_headline_is_exact_matches_only(self):
        a = self.put('a.json', summary())
        b = self.put('b.json', summary('0.15.2', counts={'value_match': 20, 'illegal_exclusion': 5}))
        out = self.dir/'table.json'
        code, text = run('publish', '--summary', a, '--summary', b, '--json', out, '--markdown', self.dir/'t.md')
        self.assertEqual(code, 0, text)
        table = json.loads(out.read_text())
        rows = {r['version']: r for r in table['rows']}
        self.assertEqual(rows['0.16.0']['exact_matches'], 85)
        self.assertEqual((rows['0.16.0']['host_differences'], rows['0.16.0']['illegal'],
                          rows['0.16.0']['unspecified'], rows['0.16.0']['capped_searches'],
                          rows['0.16.0']['bounded_no_result']), (3, 4, 2, 1, 1))
        self.assertEqual(table['headline']['successful_comparisons'], 105)
        self.assertEqual(table['totals']['cases'], 121)
        self.assertEqual(rows['0.16.0']['proof_exclusions'], len(CLAIMED['0.16.0']))
        self.assertIn('**105**', (self.dir/'t.md').read_text())
        code, text = run('check', '--json', out, '--summary', a, '--summary', b)
        self.assertEqual(code, 0, text)

    def test_real_producer_summary(self):
        """diff-report.py's own summary (mocked native/model rows) feeds the publisher."""
        root = self.dir/'tree'
        (root/'examples/basic').mkdir(parents=True)
        (root/'ZigLean').mkdir(); (root/'ZigLean/Basic.lean').write_text('-- runtime\n')
        diff = root/'tests/diff'
        (diff/'basic/inputs').mkdir(parents=True)
        (diff/'basic/host.txt').write_text('foo\n')
        (diff/'basic/unspecified.txt').write_text('foo 1\n')
        rows = [({'ok': 1}, {'ok': 1}, 'value', 'value'),
                ({'ok': 1}, {'ok': 2}, 'value', 'value'),  # declared host-dependent
                ({'ok': 3}, {'fail': 'Zig.Error.illegal'}, 'value', 'illegal')]
        (diff/'basic/inputs/foo.jsonl').write_text(''.join(f'[{i}]\n' for i in range(len(rows))))
        for side, pos in (('zig', 0), ('lean', 1)):
            out = diff/'out'/side/'basic'; out.mkdir(parents=True)
            (out/'foo.jsonl').write_text(''.join(json.dumps(r[pos])+'\n' for r in rows))
            (out/'foo.jsonl.outcomes').write_text(''.join(
                json.dumps({'schema': 1, 'kind': r[2+pos], 'legacy': r[pos]})+'\n' for r in rows))
        path = self.dir/'report.json'
        ACC.REPORT.compare(root, ['basic'], '0.16.0', 'Darwin-arm64', path)
        row = ACC.summary_row(path)
        self.assertEqual((row['cases'], row['exact_matches'], row['host_differences'], row['illegal']), (3, 1, 1, 1))
        self.assertEqual((row['version'], row['target'], row['selected_examples']), ('0.16.0', 'Darwin-arm64', ['basic']))

    # ---- negative controls -------------------------------------------------------------------

    def test_inflated_producer_headline_fails(self):
        bad = summary(); bad['exact_matches'] += bad['counts']['host_difference']
        self.assertFails('is not the exact-match status total', 'publish', '--summary',
                         self.put('s.json', bad), '--json', self.dir/'t.json')
        self.assertFalse((self.dir/'t.json').exists())

    def test_inconsistent_case_count_fails(self):
        self.assertFails('case_count is', 'publish', '--summary',
                         self.put('s.json', summary(case_count=1)), '--json', self.dir/'t.json')

    def test_unknown_status_fails(self):
        bad = summary(); bad['counts']['approximate_match'] = 1; bad['case_count'] += 1
        self.assertFails('unknown comparison status', 'publish', '--summary',
                         self.put('s.json', bad), '--json', self.dir/'t.json')

    def test_incomplete_or_qualified_or_proof_claims_fail(self):
        for extra, needle in (({'complete': False}, 'incomplete run'),
                              ({'qualified': True}, 'qualified=false'),
                              ({'proof_applicability': 'evaluated'}, 'unsupported proof_applicability'),
                              ({'proof_exclusions': []}, 'proof_exclusions must name'),
                              ({'setup_failures': 2}, 'setup_failures disagrees')):
            with self.subTest(extra=extra):
                self.assertFails(needle, 'publish', '--summary', self.put('s.json', summary(**extra)),
                                 '--json', self.dir/'t.json')

    def test_duplicate_version_target_fails(self):
        a, b = self.put('a.json', summary()), self.put('b.json', summary(counts={'value_match': 1}))
        self.assertFails('two summaries for Zig 0.16.0 on Linux-x86_64', 'publish',
                         '--summary', a, '--summary', b, '--json', self.dir/'t.json')


class Check(Temp):
    def setUp(self):
        super().setUp()
        self.summary = self.put('s.json', summary())
        self.table = ACC.publish([self.summary])

    def check(self, table):
        return run('check', '--json', self.put('t.json', table), '--summary', self.summary)

    def test_headline_including_exclusions_fails(self):
        bad = copy.deepcopy(self.table)
        bad['headline']['successful_comparisons'] += bad['totals']['host_differences'] + bad['totals']['illegal']
        code, output = self.check(bad)
        self.assertEqual(code, 1, output)
        self.assertIn('is not the exact-match total', output)

    def test_exclusion_moved_into_exact_column_fails(self):
        for column in ('host_differences', 'illegal', 'unspecified', 'capped_searches'):
            with self.subTest(column=column):
                bad = copy.deepcopy(self.table)
                for scope in (bad['rows'][0], bad['totals']):
                    scope['exact_matches'] += scope[column]; scope[column] = 0
                bad['headline']['successful_comparisons'] = bad['totals']['exact_matches']
                code, output = self.check(bad)
                self.assertEqual(code, 1, output)
                self.assertIn('differs from the table regenerated', output)

    def test_skipped_counted_as_cases_fails(self):
        bad = copy.deepcopy(self.table)
        for scope in (bad['rows'][0], bad['totals']):
            scope['exact_matches'] += scope['skipped_functions']
        bad['headline']['successful_comparisons'] = bad['totals']['exact_matches']
        code, output = self.check(bad)
        self.assertEqual(code, 1, output)
        self.assertIn('do not partition', output)

    def test_totals_must_be_row_sums(self):
        bad = copy.deepcopy(self.table); bad['totals']['proof_exclusions'] = 0
        code, output = self.check(bad)
        self.assertEqual(code, 1, output)
        self.assertIn('total proof_exclusions is not the sum', output)

    def test_check_needs_its_summaries(self):
        self.assertFails('needs the --summary', 'check', '--json', self.put('t.json', self.table))


class Published(unittest.TestCase):
    """Each committed table (assurance/accounting/<sha>.json) regenerates from the CI summaries
    committed beside it (assurance/accounting/<sha>/), real producer output from that run."""

    def test_committed_tables_check(self):
        tables = sorted((ROOT/'assurance/accounting').glob('*.json'))
        self.assertTrue(tables)
        for table in tables:
            with self.subTest(table=table.name):
                summaries = sorted(table.with_suffix('').glob('*.json'))
                self.assertTrue(summaries)
                code, output = run('check', '--json', table,
                                   *(a for path in summaries for a in ('--summary', path)))
                self.assertEqual(code, 0, output)
                versions = {r['version'] for r in json.loads(table.read_text())['rows']}
                # A table records one CI run: a version still in qualification (0.17.0) may postdate it.
                self.assertLessEqual(set(CLAIMED) - IN_QUALIFICATION, versions)


class Claims(Temp):
    def setUp(self):
        super().setUp()
        self.root = self.dir/'repo'
        for rel in ('README.md', '.github/workflows/ci.yml'):
            (self.root/rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/rel, self.root/rel)
        for name in EXAMPLES:
            (self.root/'examples'/name).mkdir(parents=True)

    def edit(self, rel, old, new):
        path = self.root/rel
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def claims(self, *summaries, require=False):
        args = ['claims', '--root', self.root]
        for i, data in enumerate(summaries):
            args += ['--summary', self.put(f's{i}.json', data)]
        return run(*args, *(['--require-full-versions'] if require else []))

    def assertClaim(self, needle, *summaries, require=False):
        code, output = self.claims(*summaries, require=require)
        self.assertEqual(code, 1, output)
        self.assertIn(needle, output)

    def test_committed_claims_hold(self):
        code, output = run('claims', '--root', ROOT)
        self.assertEqual(code, 0, output)
        _, supported, rows = ACC.readme_claims(ROOT)
        for version, examples in CLAIMED.items():
            self.assertEqual(rows[version]['examples'], examples)
        self.assertIn('restricted job', rows['0.14.1']['ci'])

    def test_full_matrix_summaries_hold(self):
        code, output = self.claims(summary('0.17.0'), summary('0.16.0'), summary('0.15.2'),
                                   summary('0.16.0', 'Darwin-arm64',
                                           examples=[e for e in CLAIMED['0.16.0'] if e != 'asm']),
                                   require=True)
        self.assertEqual(code, 0, output)

    def test_missing_full_version_summary_fails(self):
        self.assertClaim('no differential summary for README full-diff Zig 0.15.2',
                         summary('0.16.0'), require=True)

    def test_restricted_version_summary_contradicts_claim(self):
        self.assertClaim('README claims no diff harness', summary('0.14.1', examples=['basic']))

    def test_focused_selection_does_not_evidence_claim(self):
        self.assertClaim('ran examples', summary('0.15.2', examples=['atomics', 'threads']))

    def test_unsupported_version_summary_fails(self):
        self.assertClaim('not a README-supported version', summary('0.13.0'))

    def test_restricted_example_list_mismatch(self):
        self.edit('README.md', '| 0.14.1 | restricted job (translation and proofs; no diff harness) | `basic`,',
                  '| 0.14.1 | restricted job (translation and proofs; no diff harness) | `basic`, `slices`,')
        self.assertClaim('restricted examples')

    def test_full_claim_without_ci_job(self):
        self.edit('.github/workflows/ci.yml', '- zig: "0.15.2"\n            examples: ""\n            full: true',
                  '- zig: "0.15.2"\n            examples: ""\n            full: false')
        self.assertClaim('README claims a full Zig 0.15.2 job')

    def test_supported_version_absent_from_ci(self):
        self.edit('README.md', 'Supported: Zig **0.17.0** (in qualification),', 'Supported: Zig **0.13.0**, **0.17.0** (in qualification),')
        self.assertClaim('CI matrix runs')

    def test_restricted_prose_contradicting_row(self):
        self.edit('README.md', "The 0.14.1 row uses CI's restricted examples", "The 0.15.2 row uses CI's restricted examples")
        self.assertClaim('skips the differential harness; its version row disagrees')

    def test_readme_headline_including_exclusions_fails(self):
        self.edit('README.md', '85,987 exact matches', '86,484 exact matches')
        self.assertClaim('exact matches must exclude every excluded case')


if __name__ == '__main__':
    unittest.main()
