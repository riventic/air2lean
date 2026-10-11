#!/usr/bin/env python3
"""Q08 release-record and review-ledger regressions on tiny fixture repositories. No builds."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
FIXTURES = Path(__file__).resolve().parent / 'fixtures'
spec = importlib.util.spec_from_file_location('release_record', ROOT / 'scripts/release-record.py')
rr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rr)

WORKFLOW = """name: CI
on:
  push:
    branches: [main]
jobs:
  test:
    runs-on: ubuntu-24.04
    strategy:
      fail-fast: false
      matrix:
        include:
          - zig: "0.16.0"
            examples: ""
            full: true
            mutate: false
          - zig: "0.16.0"
            examples: ""
            full: false
            mutate: true
            shard: 1
    steps:
      - name: Checkout
        uses: actions/checkout@0000000000000000000000000000000000000000 # v0
      - name: Unit
        run: echo unit
      # Substituted by scripts/local-ci.sh; not a gate.
      - name: Install elan
        run: |
          echo setup
      - name: Full only
        if: ${{ matrix.full && !matrix.mutate }}
        env:
          MODE: full
        run: |
          set -euo pipefail
          echo "$MODE"
      - name: Mutation check
        if: matrix.mutate
        run: echo mutate
"""
FULL = 'test (0.16.0, true, false)'
MUTATE = 'test (0.16.0, false, true, 1)'
FULL_ROW = {'zig': '0.16.0', 'examples': '', 'full': True, 'mutate': False}
COMPAT = {'zig': {'default': '0.16.0'}, 'translation': {'target': 'x86_64-linux'}}


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE).stdout.decode().strip()


class Repo(unittest.TestCase):
    workflow = WORKFLOW

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name).resolve()
        self.repo = self.base / 'repo'
        self.repo.mkdir()
        git(self.repo, 'init', '-q')
        git(self.repo, 'config', 'user.email', 'test@example.invalid')
        git(self.repo, 'config', 'user.name', 'test')
        git(self.repo, 'config', 'commit.gpgsign', 'false')
        self.write('reviewed.txt', 'reviewed\n')
        self.write('kept.txt', 'kept\n')
        self.reviewed = self.commit('baseline')
        self.write_ledger([('reviewed.txt', self.reviewed), ('kept.txt', self.reviewed)])
        self.write('reviewed.txt', 'changed after review\n')
        self.write('added.txt', 'not reviewed\n')
        self.write('.github/workflows/ci.yml', self.workflow)
        self.write('scripts/local-ci-steps.py', (ROOT / 'scripts/local-ci-steps.py').read_text())
        self.write('compatibility.json', json.dumps(COMPAT))
        self.head = self.commit('release candidate')

    def write(self, path, text):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def commit(self, message):
        git(self.repo, 'add', '-A')
        git(self.repo, 'commit', '-qm', message)
        return git(self.repo, 'rev-parse', 'HEAD')

    def write_ledger(self, entries, header=rr.LEDGER_HEADER):
        lines = ['\t'.join(header)]
        for path, revision in entries:
            digest = hashlib.sha256((self.repo / path).read_bytes()).hexdigest()
            lines.append('\t'.join([path, 'infra', 'full manual read', digest, revision][:len(header)]))
        self.write(rr.LEDGER, '\n'.join(lines) + '\n')

    def run_json(self, jobs, sha=None, **extra):
        data = dict({'databaseId': 1, 'headSha': sha or self.head, 'status': 'completed', 'conclusion': 'success',
                     'event': 'push', 'workflowName': 'CI', 'url': 'https://example.invalid/run/1', 'jobs': [
                         {'name': name, 'steps': [{'name': step, 'conclusion': conclusion}
                                                  for step, conclusion in steps.items()]}
                         for name, steps in jobs.items()]}, **extra)
        path = self.base / ('run-%d.json' % len(list(self.base.glob('run-*.json'))))
        path.write_text(json.dumps(data))
        return str(path)

    def passing_run(self, sha=None):
        return self.run_json({
            FULL: {'Set up job': 'success', 'Checkout': 'success', 'Unit': 'success', 'Install elan': 'success',
                   'Full only': 'success', 'Mutation check': 'skipped'},
            MUTATE: {'Unit': 'success', 'Full only': 'skipped', 'Mutation check': 'success'}}, sha)

    def local_dir(self, headers, status=0, **stamp):
        directory = Path(tempfile.mkdtemp(dir=self.base))
        values = dict({'revision': self.head, 'tracked_clean': 'yes', 'mode': 'full', 'version': '0.16.0'}, **stamp)
        (directory / 'source-revision').write_text(''.join('%s=%s\n' % item for item in values.items()))
        (directory / 'exit-status').write_text('%d\n' % status)
        (directory / 'container.log').write_text(''.join(
            '== CI %r: %s ==\nstep output\n' % (row, step) for row, step in headers))
        return str(directory)

    def record(self, **kwargs):
        return rr.build_record(self.repo, **kwargs)

    def gate(self, record, job, step):
        return next(g for g in record['gates'] if g['job'] == job and g['step'] == step)


class PlanTests(Repo):
    def test_gates_follow_matrix_conditions_and_exclude_setup_and_actions(self):
        plan = rr.build_plan(self.repo, self.head)
        jobs = {job['name']: job for job in plan['jobs']}
        self.assertEqual(list(jobs), [FULL, MUTATE])
        self.assertEqual(jobs[FULL]['gates'], ['Unit', 'Full only'])
        self.assertEqual(jobs[FULL]['not_applicable'], ['Mutation check'])
        self.assertEqual(jobs[MUTATE]['gates'], ['Unit', 'Mutation check'])
        self.assertEqual(jobs[FULL]['reproduce'], 'scripts/local-ci.sh full 0.16.0')
        self.assertEqual(jobs[MUTATE]['reproduce'], 'scripts/local-ci.sh mutations')
        self.assertEqual(plan['commands']['Full only'],
                         {'if': '${{ matrix.full && !matrix.mutate }}', 'env': {'MODE': 'full'},
                          'run': 'set -euo pipefail\necho "$MODE"\n'})
        self.assertNotIn('Install elan', plan['commands'])

    def test_unsupported_workflow_syntax_fails_closed(self):
        for bad in ('x: &anchor 1\n', 'x: >\n  folded\n', 'x: |+\n  kept\n', 'x: | # note\n  y\n', 'jobs:\n  test:\n    steps:\n    - name: a\n     run: b\n'):
            with self.subTest(bad=bad), self.assertRaises(rr.ReleaseError):
                rr.parse_workflow_yaml(bad)

    def test_dirty_tree_receipt_gate_is_refused(self):
        unit = 'run: echo unit'
        for change in ('run: AIR2LEAN_RECEIPT_ALLOW_DIRTY=1 bash tests/roadmap/proof-receipts/check.sh x y z',
                       'run: python3 scripts/proof-receipt.py prepare "$a" --profile "p" --allow-dirty',
                       'run: |\n          python3 scripts/proof-receipt.py prepare "$a" \\\n            --allow-dirty',
                       'env:\n          AIR2LEAN_RECEIPT_ALLOW_DIRTY: "1"\n        ' + unit):
            with self.subTest(change=change):
                self.write('.github/workflows/ci.yml', WORKFLOW.replace(unit, change))
                with self.assertRaisesRegex(rr.ReleaseError, 'lets a proof receipt bind a dirty tree'):
                    rr.build_plan(self.repo, self.commit('dirty receipt gate'))
        self.write('.github/workflows/ci.yml', WORKFLOW.replace(unit, 'env:\n          AIR2LEAN_RECEIPT_ALLOW_DIRTY: "0"\n        ' + unit))
        rr.build_plan(self.repo, self.commit('permission disabled'))

    def test_unevaluable_condition_fails_closed(self):
        self.write('.github/workflows/ci.yml', WORKFLOW.replace('if: matrix.mutate', "if: matrix.zig != '1'"))
        with self.assertRaisesRegex(rr.ReleaseError, 'unsupported condition'):
            rr.build_plan(self.repo, self.commit('unsupported'))


class RecordTests(Repo):
    def test_complete_record_binds_revision_profile_and_review(self):
        record = self.record(github_runs=[self.passing_run()])
        self.assertEqual(record['status'], 'complete')
        self.assertEqual(record['revision'], self.head)
        self.assertEqual(record['summary'], {'passed': 4, 'failed': 0, 'missing': 0, 'unavailable': 0})
        self.assertEqual(record['profile']['workflow_blob'], git(self.repo, 'rev-parse', 'HEAD:.github/workflows/ci.yml'))
        self.assertEqual(record['evidence'][0]['head_sha'], self.head)
        self.assertEqual(record['review']['reviewed_revisions'], {self.reviewed: 2})
        self.assertEqual(record['review']['changed_since_review'], ['reviewed.txt'])
        self.assertIn('added.txt', record['review']['not_in_ledger'])
        self.assertNotIn('kept.txt', record['review']['changed_since_review'])
        self.assertEqual(rr.verify_record(self.repo, json.loads(json.dumps(record))), [])

    def test_dirty_tree_is_refused(self):
        (self.repo / 'kept.txt').write_text('edited\n')
        with self.assertRaisesRegex(rr.ReleaseError, 'dirty tree'):
            self.record(github_runs=[self.passing_run()])
        git(self.repo, 'checkout', '--', 'kept.txt')
        (self.repo / 'untracked.txt').write_text('stray\n')
        with self.assertRaisesRegex(rr.ReleaseError, 'dirty tree.*untracked.txt'):
            self.record(github_runs=[self.passing_run()])

    def test_evidence_for_another_revision_is_refused(self):
        with self.assertRaisesRegex(rr.ReleaseError, 'not the recorded revision'):
            self.record(github_runs=[self.passing_run(sha=self.reviewed)])
        with self.assertRaisesRegex(rr.ReleaseError, 'not completed'):
            self.record(github_runs=[self.run_json({}, status='in_progress')])
        with self.assertRaisesRegex(rr.ReleaseError, 'pull_request run'):
            self.record(github_runs=[self.run_json({}, event='pull_request')])

    def test_missing_gates_make_record_incomplete_until_declared_unavailable(self):
        only_full = self.run_json({FULL: {'Unit': 'success', 'Full only': 'success', 'Mutation check': 'skipped'}})
        record = self.record(github_runs=[only_full])
        self.assertEqual(record['status'], 'incomplete')
        self.assertEqual(self.gate(record, MUTATE, 'Mutation check')['status'], 'missing')
        with tempfile.NamedTemporaryFile('w', suffix='.json', dir=self.base, delete=False) as out:
            pass
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(rr.main(['record', '--root', str(self.repo), '--github-run', only_full, '--out', out.name]), 1)
        record = self.record(github_runs=[only_full], unavailable=[MUTATE + '=mutation runner unavailable'])
        self.assertEqual(record['status'], 'complete')
        self.assertEqual(self.gate(record, MUTATE, 'Unit'),
                         {'job': MUTATE, 'step': 'Unit', 'evidence': [], 'details': [], 'status': 'unavailable',
                          'reason': 'mutation runner unavailable'})
        self.assertEqual(self.gate(record, FULL, 'Unit')['status'], 'passed')
        self.assertEqual(rr.verify_record(self.repo, record), [])

    def test_failures_and_skips_are_never_passed_or_hidden(self):
        run = self.run_json({FULL: {'Unit': 'failure', 'Full only': 'skipped'},
                             MUTATE: {'Unit': 'cancelled', 'Mutation check': 'success'}})
        record = self.record(github_runs=[run], unavailable=[FULL + '=host lost'])
        self.assertEqual([g['status'] for g in record['gates']], ['failed', 'failed', 'failed', 'passed'])
        self.assertEqual(record['status'], 'incomplete')
        with self.assertRaisesRegex(rr.ReleaseError, 'declared unavailable but has evidence'):
            self.record(github_runs=[run], unavailable=[FULL + '::Unit=flaky'])
        with self.assertRaisesRegex(rr.ReleaseError, 'names no gate'):
            self.record(github_runs=[run], unavailable=[FULL + '::Mutation check=not applicable here'])
        with self.assertRaisesRegex(rr.ReleaseError, 'JOB'):
            self.record(github_runs=[run], unavailable=[FULL + '=  '])

    def test_conflicting_evidence_fails_the_gate(self):
        good, bad = self.passing_run(), self.run_json({FULL: {'Unit': 'failure'}})
        record = self.record(github_runs=[good, bad])
        self.assertEqual(self.gate(record, FULL, 'Unit')['status'], 'failed')
        self.assertEqual(self.gate(record, FULL, 'Unit')['evidence'], [0, 1])

    def test_run_from_another_workflow_is_refused(self):
        with self.assertRaisesRegex(rr.ReleaseError, 'condition is false'):
            self.record(github_runs=[self.run_json({FULL: {'Unit': 'success', 'Mutation check': 'success'}})])
        with self.assertRaisesRegex(rr.ReleaseError, 'unknown or repeated'):
            self.record(github_runs=[self.run_json({'test (0.15.2, true, false)': {}})])
        with self.assertRaisesRegex(rr.ReleaseError, 'workflow'):
            self.record(github_runs=[self.run_json({}, workflowName='Other')])

    def test_gate_claimed_without_evidence_fails_verification(self):
        record = self.record(github_runs=[self.run_json({FULL: {'Unit': 'success', 'Full only': 'success'}})])
        claimed = json.loads(json.dumps(record))
        self.gate(claimed, MUTATE, 'Mutation check')['status'] = 'passed'
        problems = rr.verify_record(self.repo, claimed)
        self.assertIn('%s / Mutation check: passed without evidence for %s' % (MUTATE, self.head), problems)
        self.assertTrue(any('summary' in p for p in problems))
        cited = json.loads(json.dumps(record))
        self.gate(cited, MUTATE, 'Unit').update(status='passed', evidence=[0])
        cited['summary'], cited['status'] = rr.summarize(cited['gates']), 'incomplete'
        self.assertEqual(rr.verify_record(self.repo, cited),
                         ['%s / Unit: cited evidence does not cover this job' % MUTATE])
        foreign = json.loads(json.dumps(record))
        foreign['evidence'][0]['head_sha'] = self.reviewed
        self.assertIn('evidence 0 is not github-actions evidence for %s' % self.head,
                      rr.verify_record(self.repo, foreign))
        dropped = json.loads(json.dumps(record))
        dropped['gates'].pop()
        self.assertIn('gate list differs from the workflow at %s' % self.head, rr.verify_record(self.repo, dropped))

    def test_record_cli_writes_and_verifies(self):
        out = self.base / 'record.json'
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(rr.main(['record', '--root', str(self.repo), '--github-run', self.passing_run(),
                                      '--out', str(out)]), 0)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(rr.main(['verify', '--root', str(self.repo), str(out)]), 0)


class LocalCiTests(Repo):
    def test_completed_local_run_passes_its_rows_only(self):
        local = self.local_dir([(FULL_ROW, 'Unit'), (FULL_ROW, 'Full only')])
        record = self.record(local_runs=[local])
        self.assertEqual(self.gate(record, FULL, 'Full only')['status'], 'passed')
        self.assertEqual(self.gate(record, MUTATE, 'Unit')['status'], 'missing')
        self.assertEqual(record['evidence'][0]['jobs'], [FULL])

    def test_failed_local_run_fails_last_started_step(self):
        record = self.record(local_runs=[self.local_dir([(FULL_ROW, 'Unit'), (FULL_ROW, 'Full only')], status=1)])
        self.assertEqual([self.gate(record, FULL, s)['status'] for s in ('Unit', 'Full only')], ['passed', 'failed'])

    def test_local_negative_controls(self):
        headers = [(FULL_ROW, 'Unit'), (FULL_ROW, 'Full only')]
        cases = [
            (self.local_dir(headers, revision=self.reviewed), 'not the recorded revision'),
            (self.local_dir(headers, tracked_clean='no'), 'tracked changes'),
            (self.local_dir(headers, mode='targeted'), 'does not run workflow gates'),
            (self.local_dir([(FULL_ROW, 'Full only')]), 'out of the workflow order'),
            (self.local_dir(headers[:1]), 'not every gate'),
            (self.local_dir([(dict(FULL_ROW, zig='0.15.2'), 'Unit')]), 'not a matrix row'),
        ]
        for directory, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(rr.ReleaseError, message):
                self.record(local_runs=[directory])
        incomplete = self.local_dir(headers)
        os.unlink(os.path.join(incomplete, 'exit-status'))
        with self.assertRaisesRegex(rr.ReleaseError, 'incomplete local CI results'):
            self.record(local_runs=[incomplete])


MACOS_JOB = """  macos:
    runs-on: macos-14
    steps:
      - name: Checkout
        uses: actions/checkout@0000000000000000000000000000000000000000 # v0
      - name: Unit
        run: echo macos unit
      - name: Build when uncached
        if: steps.cache.outputs.cache-hit != 'true'
        run: echo build
"""


class MacosJobTests(Repo):
    """Q05's matrix-free `macos` job: GitHub evidence only; local CI never covers it."""
    workflow = WORKFLOW + MACOS_JOB

    def test_macos_gates_exclude_cache_dependent_setup(self):
        plan = rr.build_plan(self.repo, self.head)
        macos = plan['jobs'][-1]
        self.assertEqual((macos['name'], macos['matrix'], macos['gates']), ('macos', None, ['Unit']))
        self.assertEqual(macos['reproduce'], rr.MACOS_REPRODUCE)
        self.assertEqual(plan['commands']['macos::Unit'], {'run': 'echo macos unit'})
        self.assertEqual(plan['commands']['Unit'], {'run': 'echo unit'})

    def test_local_ci_leaves_macos_missing_and_github_covers_it(self):
        local = self.local_dir([(FULL_ROW, 'Unit'), (FULL_ROW, 'Full only')])
        record = self.record(local_runs=[local])
        self.assertEqual(self.gate(record, 'macos', 'Unit')['status'], 'missing')
        self.assertEqual(record['status'], 'incomplete')
        macos = self.run_json({'macos': {'Unit': 'failure'}})
        record = self.record(local_runs=[local], github_runs=[macos])
        self.assertEqual(self.gate(record, 'macos', 'Unit')['status'], 'failed')

    def test_other_jobs_and_macos_conditions_fail_closed(self):
        self.write('.github/workflows/ci.yml', self.workflow + '  lint:\n    runs-on: ubuntu-24.04\n')
        with self.assertRaisesRegex(rr.ReleaseError, 'only the test, macos, aarch64-linux, bitops-native-arm and build-modes-aarch64-linux jobs'):
            rr.build_plan(self.repo, self.commit('extra job'))
        self.write('.github/workflows/ci.yml', self.workflow.replace(
            'run: echo macos unit', 'if: failure()\n        run: echo macos unit'))
        with self.assertRaisesRegex(rr.ReleaseError, 'unsupported condition'):
            rr.build_plan(self.repo, self.commit('conditional macos step'))


class LedgerTests(Repo):
    def test_valid_ledger(self):
        errors, unverified, counts = rr.check_ledger(self.repo)
        self.assertEqual((errors, unverified, counts), ([], [], {self.reviewed: 2}))

    def test_entry_without_reviewed_revision_fails(self):
        lines = (self.repo / rr.LEDGER).read_text().splitlines()
        lines[1] = lines[1].rsplit('\t', 1)[0] + '\t'
        self.write(rr.LEDGER, '\n'.join(lines) + '\n')
        errors, _, _ = rr.check_ledger(self.repo)
        self.assertEqual(errors, ['REVIEW_COVERAGE.tsv:2: reviewed.txt does not name its reviewed revision'])
        self.write_ledger([('kept.txt', self.reviewed)], header=rr.LEDGER_HEADER[:4])
        with self.assertRaisesRegex(rr.ReleaseError, 'header must be'):
            rr.check_ledger(self.repo)

    def test_hash_and_revision_mismatches_fail(self):
        self.write_ledger([('reviewed.txt', self.reviewed), ('added.txt', self.reviewed)])
        errors, _, _ = rr.check_ledger(self.repo)
        self.assertEqual(len(errors), 2)
        self.assertIn('reviewed.txt at %s does not have the recorded baseline SHA-256' % self.reviewed, errors[0])
        self.assertIn('added.txt does not exist at reviewed revision', errors[1])
        absent = 'f' * 40
        self.write_ledger([('kept.txt', absent)])
        self.assertIn('is not available', rr.check_ledger(self.repo)[0][0])
        self.assertEqual(rr.check_ledger(self.repo, allow_unfetched=True)[:2], ([], [absent]))

    def test_record_refuses_invalid_ledger(self):
        self.write_ledger([('kept.txt', 'not-a-revision')])
        self.commit('bad ledger')
        with self.assertRaisesRegex(rr.ReleaseError, 'review ledger'):
            self.record(github_runs=[])


class RealWorkflowTests(Repo):
    """The merged main workflow and its successful GitHub run (fixtures/, run 37551078044)."""
    workflow = (FIXTURES / 'ci-d9dfa68.yml').read_text()

    def test_real_run_matches_github_job_names_and_skip_decisions(self):
        data = json.loads((FIXTURES / 'run-37551078044.json').read_text())
        self.assertEqual(data['headSha'], 'd9dfa68962c74fbcd44e2096cd23bab3b0b1c6f0')
        data['headSha'] = self.head  # the fixture repository's commit carries that workflow
        path = self.base / 'real-run.json'
        path.write_text(json.dumps(data))
        record = self.record(github_runs=[str(path)])
        self.assertEqual(record['status'], 'complete')
        self.assertEqual(record['summary']['missing'] + record['summary']['failed'], 0)
        self.assertEqual(len(record['jobs']), 8)
        self.assertEqual(rr.verify_record(self.repo, record), [])

    def test_current_workflow_plan_and_ledger_structure(self):
        plan = rr.build_plan(ROOT, rr.git_text(ROOT, 'rev-parse', 'HEAD'))
        self.assertTrue(all(job['gates'] for job in plan['jobs']))
        errors, _, counts = rr.check_ledger(ROOT, allow_unfetched=True)
        self.assertEqual(errors, [])
        self.assertTrue(counts)

    @unittest.skipUnless(importlib.util.find_spec('yaml'), 'PyYAML not installed')
    def test_parser_agrees_with_pyyaml(self):
        import yaml
        for text in (WORKFLOW, self.workflow, (ROOT / '.github/workflows/ci.yml').read_text()):
            expected = yaml.safe_load(text)
            expected['on'] = expected.pop(True)
            self.assertEqual(rr.parse_workflow_yaml(text), expected)


if __name__ == '__main__':
    unittest.main()
