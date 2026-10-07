#!/usr/bin/env python3
"""Q07 upgrade-qualification driver regressions on synthetic inventories and stub runners.

Consumes the real `scripts/coverage.py diff`; no Zig, Lake or Lean runs.
"""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts/qualify-upgrade.py'
spec = importlib.util.spec_from_file_location('qualify_upgrade', SCRIPT)
q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)

CANDIDATE = 'source-pipeline-candidate-unqualified'
REJECTED = 'normalizer-rejected-compiler-state-or-effect'


def tag(name, disposition, goldens=()):
    return {'tag': name, 'disposition': disposition, 'tests': {'paths': list(goldens)}}


def inventory(version='0.16.0', tags=None, models=None, compiler=None, sources=None):
    tags = tags if tags is not None else [
        tag('add', CANDIDATE, ['tests/golden/0.16.0/basic/air/basic.f.json']),
        tag('trap', REJECTED, ['tests/golden/0.16.0/lists/air/lists.g.json'])]
    return {'format': 1, 'zig_version': version, 'golden_os': 'linux',
            'universe': {'air_tags': sorted(t['tag'] for t in tags), 'types': ['int'], 'intern_keys': [],
                         'pointer_bases': ['nav']},
            'compiler_source_sha256': compiler or {'src/Air.zig': 'a' * 64, 'lib/std/Thread.zig': 'b' * 64},
            'project_source_sha256': sources or {'translation': {'Air2Lean/Emit.lean': 'c' * 64},
                                                 'runtime-models': {}, 'proof-sources': {},
                                                 'qualification-probes': {}, 'model-boundaries': {},
                                                 'inventory-tool': {}},
            'models': models if models is not None else [
                {'name': 'mem.Allocator.alloc', 'recognizer': 'allocFn?', 'disposition': 'recognized-model-boundary'}],
            'tags': tags, 'types': [{'name': 'int', 'disposition': 'exporter-arm-conditional-checker-review'}],
            'pointer_bases': [{'name': 'nav', 'disposition': 'exporter-explicit-arm-conditional-review'}]}


class Base(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base / 'repo'
        for example in ('basic', 'lists', 'threads'):
            (self.root / 'examples' / example).mkdir(parents=True)
            proofs = self.root / 'Proofs' / example.capitalize()
            proofs.mkdir(parents=True)
            (proofs / 'Gen.lean').write_text('')
            (proofs / 'Proofs.lean').write_text('')
        probes = self.root / 'tests/roadmap/abi-probes'
        probes.mkdir(parents=True)
        (probes / 'x86_64-linux-gnu-ReleaseSafe.json').write_text('{}')

    def tearDown(self):
        self.temporary.cleanup()

    def plan(self, before, after, name='record.json'):
        paths = []
        for label, value in (('before', before), ('after', after)):
            path = self.base / f'{name}.{label}.json'
            path.write_text(json.dumps(value))
            paths.append(path)
        record = q.make_plan(paths[0], paths[1], self.root)
        out = self.base / name
        q.write_record(out, record)
        return out, record, paths

    def ids(self, record):
        return [o['id'] for o in record['obligations']]


class PlanTests(Base):
    def test_identical_inventories_need_nothing(self):
        out, record, _ = self.plan(inventory(), inventory())
        self.assertEqual(record['obligations'], [])
        self.assertEqual(q.check_record(out), [])

    def test_support_expansion_targets_affected_example_only(self):
        after = inventory(tags=[tag('add', CANDIDATE, ['tests/golden/0.16.0/basic/air/basic.f.json']),
                                tag('trap', CANDIDATE, ['tests/golden/0.16.0/lists/air/lists.g.json'])])
        _, record, _ = self.plan(inventory(), after)
        ids = self.ids(record)
        self.assertEqual(ids, ['support:tags:trap', 'evidence:tags', 'translation:lists', 'proofs:lists'])
        support = record['obligations'][0]
        self.assertTrue(support['requires_evidence'])
        self.assertEqual((support['scope']['from'], support['scope']['to']), (REJECTED, CANDIDATE))
        translation = record['obligations'][2]
        self.assertEqual(translation['env']['AIR2LEAN_EXAMPLES'], 'lists')
        self.assertEqual(translation['command'], ['scripts/check.sh'])
        self.assertEqual(record['obligations'][3]['scope']['modules'], ['Proofs.Lists.Gen', 'Proofs.Lists.Proofs'])

    def test_narrowing_is_not_support_expansion(self):
        after = inventory(tags=[tag('add', REJECTED, ['tests/golden/0.16.0/basic/air/basic.f.json']),
                                tag('trap', REJECTED, ['tests/golden/0.16.0/lists/air/lists.g.json'])])
        _, record, _ = self.plan(inventory(), after)
        self.assertNotIn('support:tags:add', self.ids(record))
        self.assertIn('translation:basic', self.ids(record))

    def test_new_tag_or_unknown_disposition_is_expansion(self):
        tags = inventory()['tags'] + [tag('fresh', REJECTED), tag('odd', 'some-new-disposition')]
        before = inventory(tags=inventory()['tags'] + [tag('odd', REJECTED)])
        _, record, _ = self.plan(before, inventory(tags=tags))
        ids = self.ids(record)
        self.assertIn('support:tags:odd', ids)
        self.assertNotIn('support:tags:fresh', ids)  # added as rejected: universe review only
        self.assertIn('universe:air_tags', ids)
        universe = next(o for o in record['obligations'] if o['id'] == 'universe:air_tags')
        self.assertEqual(universe['scope']['added'], ['fresh'])

    def test_duplicate_rows_use_first_occurrence(self):
        after = inventory(tags=inventory()['tags'] + [tag('trap', CANDIDATE)])
        _, record, _ = self.plan(inventory(), after)
        self.assertNotIn('support:tags:trap', self.ids(record))
        self.assertEqual(len(self.ids(record)), len(set(self.ids(record))))

    def test_golden_os_change_retranslates_every_example(self):
        after = inventory()
        after['golden_os'] = 'macos'
        _, record, _ = self.plan(inventory(), after)
        self.assertEqual([i for i in self.ids(record) if i.startswith('translation:')],
                         ['translation:basic', 'translation:lists', 'translation:threads'])

    def test_type_and_pointer_expansion(self):
        before = inventory()
        before['types'][0]['disposition'] = 'exporter-fallback-unclassified'
        before['pointer_bases'][0]['disposition'] = 'exporter-fallback-unsupported-marker-review'
        _, record, _ = self.plan(before, inventory())
        self.assertIn('support:types:int', self.ids(record))
        self.assertIn('support:pointer_bases:nav', self.ids(record))

    def test_l01_dispositions_rank_from_coverage_vocabulary(self):
        known, forbidden = q.vocabulary()
        self.assertIn('emitted-unqualified', known['tags'])
        # Every L01 name is known: none ranks as an unknown (always-expansion) disposition.
        for category, names in known.items():
            for name in names:
                self.assertIsNotNone(q.rank(category, name, known, forbidden), (category, name))
        golden = ['tests/golden/0.16.0/basic/air/basic.f.json']

        def plan_tags(before, after):
            return self.ids(self.plan(inventory(tags=[tag('add', before, golden)]),
                                      inventory(tags=[tag('add', after, golden)]))[1])
        # Rejection -> emitted is an expansion; between rejections or between supported forms is not.
        self.assertIn('support:tags:add', plan_tags('rejected-unknown-tag', 'emitted-unqualified'))
        self.assertIn('support:tags:add', plan_tags(forbidden, 'erased-at-emission'))
        for before, after in (('rejected-unknown-tag', 'unreachable-at-export'),
                              ('rejected-exporter-unsupported', 'rejected-compiler-state-or-effect'),
                              ('emitted-unqualified', 'erased-at-emission'),
                              ('emitted-unqualified', 'rejected-fast-math'),
                              (CANDIDATE, 'emitted-unqualified'),  # legacy inventory -> L01 names
                              (REJECTED, 'rejected-unknown-tag')):
            self.assertNotIn('support:tags:add', plan_tags(before, after), (before, after))
        # A vocabulary the inventories embed (a newer coverage.py) is honoured.
        before, after = inventory(tags=[tag('add', REJECTED, golden)]), inventory(tags=[tag('add', 'rejected-new-kind', golden)])
        after['dispositions'] = {'tags': {'rejected-new-kind': 'synthetic'}}
        self.assertNotIn('support:tags:add', self.ids(self.plan(before, after)[1]))

    def test_committed_inventory_has_no_self_expansion(self):
        current = json.loads((ROOT / 'coverage/0.16.0.json').read_text())
        self.assertEqual(q.support_expansions(current, current), [])
        # Against itself with every row downgraded to rejected, only supported rows are expansions.
        downgraded = copy.deepcopy(current)
        for category in ('tags', 'types', 'constants', 'pointer_bases'):
            for row in downgraded[category]:
                row['disposition'] = 'unreachable-at-export' if category != 'pointer_bases' else 'rejected-unsupported-pointer-base'
        found = q.support_expansions(downgraded, current)
        known, forbidden = q.vocabulary(current)
        self.assertTrue(found)
        self.assertTrue(all(q.rank(r['category'], r['to'], known, forbidden) == 1 for r in found))

    def test_model_change_requires_reviews_and_all_examples(self):
        models = [{'name': 'mem.Allocator.alloc', 'recognizer': 'allocFn2?', 'disposition': 'recognized-model-boundary'}]
        _, record, _ = self.plan(inventory(), inventory(models=models))
        ids = self.ids(record)
        self.assertEqual(ids[:2], ['model:mem.Allocator.alloc', 'model-boundary'])
        self.assertTrue(all(o['requires_evidence'] for o in record['obligations'][:2]))
        self.assertEqual([i for i in ids if i.startswith('translation:')],
                         ['translation:basic', 'translation:lists', 'translation:threads'])
        self.assertFalse(any(i.startswith('probe:') for i in ids))

    def test_version_upgrade_requires_probes_translations_proofs(self):
        compiler = {'src/Air.zig': 'd' * 64, 'lib/std/Thread.zig': 'e' * 64}
        _, record, _ = self.plan(inventory('0.15.2'), inventory('0.16.0', compiler=compiler))
        ids = self.ids(record)
        for expected in ('model-boundary', 'compiler-sources', 'probe:float', 'probe:layout:x86_64-linux-gnu-ReleaseSafe',
                         'translation:threads', 'proofs:basic', 'proofs:threads'):
            self.assertIn(expected, ids)
        boundary = next(o for o in record['obligations'] if o['id'] == 'model-boundary')
        self.assertEqual(boundary['scope']['compiler_std_sources'], ['lib/std/Thread.zig'])

    def test_proof_source_change_targets_that_proof(self):
        sources = copy.deepcopy(inventory()['project_source_sha256'])
        sources['proof-sources'] = {'Proofs/Threads/Proofs.lean': 'f' * 64}
        _, record, _ = self.plan(inventory(), inventory(sources=sources))
        self.assertEqual(self.ids(record), ['proofs:threads'])

    def test_committed_inventories_plan(self):
        record = q.make_plan(ROOT / 'coverage/0.15.2.json', ROOT / 'coverage/0.16.0.json')
        kinds = {o['kind'] for o in record['obligations']}
        self.assertEqual(kinds, {'review', 'probe', 'translation', 'proofs'})


class RecordTests(Base):
    def setUp(self):
        super().setUp()
        models = [{'name': 'mem.Allocator.alloc', 'recognizer': 'allocFn2?', 'disposition': 'recognized-model-boundary'}]
        self.out, self.record, self.paths = self.plan(inventory(), inventory(models=models))
        self.commands = [o['id'] for o in self.record['obligations'] if o['command']]

    def stub(self, failing=()):
        calls = []

        def executor(argv, env, log, cwd):
            calls.append((argv, env))
            log.write_text(f'stub {argv} {env.get("AIR2LEAN_EXAMPLES")}\n')
            return 1 if env.get('AIR2LEAN_EXAMPLES') in failing else 0
        return executor, calls

    def accept_reviews(self):
        for o in self.record['obligations']:
            if o['kind'] == 'review':
                q.record_result(self.out, o['id'], reviewer='kr', decision='accepted',
                                evidence=['docs/std-models.md#allocator'], root=self.root)

    def test_check_requires_every_result(self):
        problems = q.check_record(self.out)
        self.assertEqual(len(problems), len(self.record['obligations']))
        self.assertTrue(all('no result recorded' in p for p in problems))

    def test_run_records_and_check_passes(self):
        executor, calls = self.stub(failing=('lists',))
        self.assertEqual(q.run_obligations(self.out, 'zig', executor=executor, root=self.root), 1)
        self.assertEqual(len(calls), len(self.commands))
        self.accept_reviews()
        problems = q.check_record(self.out)
        self.assertTrue(any('translation:lists: result is fail' in p for p in problems))
        executor, calls = self.stub()
        self.assertEqual(q.run_obligations(self.out, 'zig', executor=executor, root=self.root), 0)
        self.assertEqual([c[1]['AIR2LEAN_EXAMPLES'] for c in calls], ['lists'])  # passes are not rerun
        self.assertEqual(q.check_record(self.out, *self.paths, root=self.root), [])
        proofs = q.load_record(self.out)['results']['proofs:basic']
        self.assertNotIn('{out}', ' '.join(proofs['argv']))

    def test_run_rejects_unknown_only(self):
        executor, calls = self.stub()
        with self.assertRaises(ValueError):
            q.run_obligations(self.out, 'zig', only={'model-boundary'}, executor=executor, root=self.root)
        self.assertEqual(calls, [])

    def test_tampered_log_fails_check(self):
        executor, _ = self.stub()
        q.run_obligations(self.out, 'zig', executor=executor, root=self.root)
        self.accept_reviews()
        self.assertEqual(q.check_record(self.out), [])
        log = self.out.parent / q.load_record(self.out)['results']['translation:basic']['log']
        log.write_text('edited\n')
        self.assertTrue(any('log missing or changed' in p for p in q.check_record(self.out)))

    def test_model_review_needs_accepted_decision_and_evidence(self):
        executor, _ = self.stub()
        q.run_obligations(self.out, 'zig', executor=executor, root=self.root)
        self.accept_reviews()
        q.record_result(self.out, 'model:mem.Allocator.alloc', reviewer='kr', decision='rejected',
                        evidence=['x'], root=self.root)
        self.assertTrue(any('needs an accepted review' in p for p in q.check_record(self.out)))
        q.record_result(self.out, 'model:mem.Allocator.alloc', reviewer='kr', decision='accepted', root=self.root)
        self.assertEqual(q.check_record(self.out), ['model:mem.Allocator.alloc: support expansion or model change needs review evidence'])
        with self.assertRaises(ValueError):
            q.record_result(self.out, 'model-boundary', decision='accepted', root=self.root)

    def test_external_result_needs_evidence(self):
        with self.assertRaises(ValueError):
            q.record_result(self.out, 'translation:basic', status='pass', root=self.root)
        with self.assertRaises(ValueError):
            q.record_result(self.out, 'nonexistent', status='pass', evidence=['x'], root=self.root)
        q.record_result(self.out, 'translation:basic', status='pass', evidence=['ci-run-123'], root=self.root)
        self.assertNotIn('translation:basic: no result recorded', q.check_record(self.out))

    def test_removed_obligation_and_stale_plan_fail(self):
        record = q.load_record(self.out)
        record['obligations'].pop()
        q.write_record(self.out, record)
        self.assertTrue(any('plan digest mismatch' in p for p in q.check_record(self.out)))
        out, _, _ = self.plan(inventory(), inventory(), 'other.json')
        self.assertTrue(any('stale' in p for p in q.check_record(out, *self.paths, root=self.root)))

    def test_unknown_result_fails(self):
        record = q.load_record(self.out)
        record['results']['ghost'] = {'status': 'pass'}
        q.write_record(self.out, record)
        self.assertIn('ghost: result for an unknown obligation', q.check_record(self.out))


class CliTests(Base):
    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *map(str, args)], capture_output=True, text=True, env=ENV)

    def test_plan_commands_record_check(self):
        out = self.base / 'q.json'
        before, after = self.base / 'b.json', self.base / 'a.json'
        before.write_text(json.dumps(inventory()))
        after.write_text(json.dumps(inventory(tags=[tag('add', CANDIDATE), tag('trap', CANDIDATE)])))
        self.assertEqual(self.cli('plan', before, after, '--output', out).returncode, 0)
        refused = self.cli('plan', before, after, '--output', out)
        self.assertEqual(refused.returncode, 2)
        self.assertIn('exists', refused.stderr)
        listing = self.cli('commands', out, '--zig', '/opt/zig')
        self.assertEqual(listing.returncode, 0)
        self.assertNotIn('{zig}', listing.stdout)
        failing = self.cli('check', out, '--before', before, '--after', after)
        self.assertEqual(failing.returncode, 1)
        self.assertIn('support:tags:trap: no result recorded', failing.stderr)
        bad = self.cli('record', out, 'support:tags:trap', '--reviewer', 'kr')
        self.assertEqual(bad.returncode, 2)
        ids = [o['id'] for o in json.loads(out.read_text())['obligations']]
        for oid in ids:
            extra = ['--status', 'pass'] if oid.startswith(('translation:', 'proofs:')) else ['--decision', 'accepted']
            self.assertEqual(self.cli('record', out, oid, '--reviewer', 'kr', '--evidence', 'r.log', *extra).returncode, 0)
        self.assertEqual(self.cli('check', out, '--before', before, '--after', after).returncode, 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
