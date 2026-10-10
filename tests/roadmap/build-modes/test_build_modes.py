#!/usr/bin/env python3
"""T06 build-mode qualification record regressions, with negative controls. No Zig or Lean."""
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
spec = importlib.util.spec_from_file_location('build_modes', ROOT / 'scripts/build-modes.py')
bm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bm)

REGISTRY = json.loads((ROOT / bm.REGISTRY).read_text())
# Files the committed registry reads; a fixture tree copies only these.
FILES = {'docs/premises.md', 'compatibility.json', 'README.md', 'docs/build-modes.md'}
for record in REGISTRY['records']:
    FILES.update(item['path'] for item in record['evidence'])
    for item in record['evidence']:
        if item['kind'] == 'run':
            run = json.loads((ROOT / item['path']).read_text())
            FILES.update(e['reproducer'] for e in run['triage'] + run['excluded_examples'])
for part in REGISTRY['shipping'].values():
    if isinstance(part, dict):
        FILES.update(part['sources'])
for entry in REGISTRY['changed_semantics']:
    FILES.update(guard['path'] for guard in entry['guards'])


def record(data, mode, backend):
    return next(r for r in data['records'] if r['mode'] == mode and r['backend'] == backend)


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        for rel in FILES:
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, self.root / rel)
        self.data = copy.deepcopy(REGISTRY)

    def tearDown(self):
        self.tmp.cleanup()

    def errors(self):
        return bm.validate(self.data, self.root)

    def assertRejects(self, fragment):
        errors = self.errors()
        self.assertTrue(any(fragment in e for e in errors), f'{fragment!r} not in {errors}')


class CommittedRecord(unittest.TestCase):
    def test_repository_passes(self):
        self.assertEqual(bm.validate(REGISTRY, ROOT), [])

    def test_cli_check_and_commands(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(bm.main(['check']), 0)
        self.assertIn('8 records, 4 qualified', out.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(bm.main(['commands']), 0)
        self.assertIn('stage2_x86_64', out.getvalue())

    def test_qualified_pairs_are_the_llvm_builds(self):
        qualified = [(r['mode'], r['backend']) for r in REGISTRY['records'] if r['status'] == 'qualified']
        self.assertEqual(sorted(qualified), sorted((m, 'llvm') for m in bm.MODES))

    def test_every_pair_with_a_run_cites_each_target(self):
        for r in REGISTRY['records']:
            cited = sorted(Path(e['path']).name.split('--')[1] for e in r['evidence'] if e['kind'] == 'run')
            self.assertEqual(cited, sorted(r.get('targets', [])), r['mode'])

    def test_llvm_builds_are_run_on_all_three_targets(self):
        for mode in bm.MODES:
            self.assertEqual(record(REGISTRY, mode, 'llvm')['targets'],
                             ['aarch64-linux', 'aarch64-macos', 'x86_64-linux'])
            run = json.loads((ROOT / bm.RUN_DIR / f'0.16.0--aarch64-linux--{mode}--llvm.json').read_text())
            self.assertEqual((run['target'], run['emulated'], run['host']), ('aarch64-linux', False, 'Linux-aarch64'))
            # No aarch64-linux float model: the run leaves floatops and floatconv out, so it
            # shows none of the float @divExact mismatches the other two targets triage.
            self.assertEqual(run['counts'].get('mismatch', 0), 0)
            self.assertEqual(sorted(e['example'] for e in run['excluded_examples']), ['floatconv', 'floatops'])

    def test_unqualified_backend_records_state_findings(self):
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            stage2 = record(REGISTRY, mode, 'stage2_x86_64')
            self.assertEqual(stage2['status'], 'unqualified')
            self.assertIn('stage2-x86_64-narrow-int-extension', stage2['findings'])

    def test_release_fast_claim_states_premise(self):
        fast = record(REGISTRY, 'ReleaseFast', 'llvm')
        self.assertEqual(fast['claim'], 'no-illegal-behaviour-transfer')
        self.assertIn('TRU-03', fast['premises'])


class NegativeControls(Fixture):
    def test_fixture_copy_passes(self):
        self.assertEqual(self.errors(), [])

    def test_missing_pair(self):
        self.data['records'] = [r for r in self.data['records']
                                if (r['mode'], r['backend']) != ('Debug', 'stage2_x86_64')]
        self.assertRejects('no qualification record for Debug/stage2_x86_64')

    def test_duplicate_and_unknown_pair(self):
        self.data['records'].append(copy.deepcopy(self.data['records'][0]))
        self.data['records'].append(dict(self.data['records'][0], backend='stage2_wasm'))
        self.assertRejects('duplicate record ReleaseSafe/llvm')
        self.assertRejects('unknown mode/backend ReleaseSafe/stage2_wasm')

    def test_unknown_status_and_claim(self):
        record(self.data, 'Debug', 'llvm').update(status='partial', claim='binary')
        self.assertRejects('status must be one of')
        self.assertRejects('claim must be one of')

    def test_qualified_without_evidence(self):
        reference = record(self.data, 'ReleaseSafe', 'llvm')
        reference['evidence'] = []
        self.assertRejects('must cite a run for target aarch64-macos')
        reference['targets'] = []
        self.assertRejects('must cite profile evidence')
        self.assertRejects('must cite command evidence')

    def test_qualifying_without_evidence_or_claim(self):
        small = record(self.data, 'ReleaseSmall', 'stage2_x86_64')
        small['status'] = 'qualified'
        self.assertRejects('ReleaseSmall/stage2_x86_64: a qualified record must state its claim')
        self.assertRejects('ReleaseSmall/stage2_x86_64: a qualified record must cite profile evidence')

    def test_missing_evidence_file(self):
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'][0]['path'] = 'tests/golden/none.json'
        self.assertRejects('missing file tests/golden/none.json')

    def test_path_escape(self):
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'][0]['path'] = '../README.md'
        self.assertRejects('invalid repository path')

    def test_profile_mode_mismatch(self):
        # Citing a ReleaseSafe probe for ReleaseFast must not count.
        record(self.data, 'ReleaseFast', 'llvm')['evidence'][0]['path'] = \
            'tests/roadmap/abi-probes/x86_64-linux-gnu-ReleaseSafe.json'
        self.assertRejects("records build_mode 'ReleaseSafe', not 'ReleaseFast'")

    def test_profile_backend_mismatch(self):
        path = self.root / 'tests/roadmap/abi-probes/x86_64-linux-gnu-ReleaseSafe.json'
        profile = json.loads(path.read_text())
        profile['backend'] = 'stage2_x86_64'
        path.write_text(json.dumps(profile))
        self.assertRejects("records backend 'stage2_x86_64', not 'stage2_llvm'")

    def test_profile_evidence_for_wrong_backend_record(self):
        record(self.data, 'ReleaseSafe', 'stage2_x86_64')['evidence'] = [
            {'kind': 'profile', 'path': 'tests/roadmap/abi-probes/x86_64-linux-gnu-ReleaseSafe.json'}]
        self.assertRejects("not 'stage2_x86_64'")

    def test_command_mode_mismatch(self):
        record(self.data, 'ReleaseFast', 'llvm')['evidence'].append(
            {'kind': 'command', 'path': 'scripts/diff.sh', 'text': 'build-exe -OReleaseSafe -mcpu=baseline'})
        self.assertRejects('does not select -OReleaseFast')

    def test_command_backend_mismatch(self):
        record(self.data, 'ReleaseSafe', 'stage2_x86_64')['evidence'] = [
            {'kind': 'command', 'path': 'scripts/diff.sh', 'text': 'build-exe -OReleaseSafe -mcpu=baseline'}]
        self.assertRejects('does not select a non-LLVM backend')

    def test_command_text_absent_from_source(self):
        path = self.root / 'scripts/diff.sh'
        path.write_text(path.read_text().replace('-OReleaseSafe -mcpu=baseline', '-OReleaseFast -mcpu=baseline'))
        self.assertRejects("scripts/diff.sh does not contain 'build-exe -OReleaseSafe -mcpu=baseline'")

    def test_unknown_premise(self):
        record(self.data, 'ReleaseFast', 'llvm')['premises'].append('TRU-99')
        self.assertRejects('unknown premise TRU-99')

    def test_claim_without_premises(self):
        record(self.data, 'ReleaseFast', 'llvm')['premises'] = []
        self.assertRejects("claim 'no-illegal-behaviour-transfer' must cite the premises")

    def test_unqualified_claim_needs_commands(self):
        stage2 = record(self.data, 'Debug', 'stage2_x86_64')
        stage2.update(claim='tested-input-agreement', premises=['TRU-03'])
        del stage2['commands']
        self.assertRejects('must list the commands')

    def test_excluded_cannot_claim(self):
        record(self.data, 'ReleaseSmall', 'stage2_x86_64').update(
            status='excluded', claim='no-illegal-behaviour-transfer', premises=['TRU-03'])
        self.assertRejects('an excluded record cannot support a claim')

    def test_fast_math_must_be_excluded(self):
        self.data['changed_semantics'][0]['status'] = 'unqualified'
        self.assertRejects('changed semantics must be excluded')
        self.data['changed_semantics'] = self.data['changed_semantics'][1:]
        self.assertRejects("missing 'fast-math' treatment")

    def test_fast_math_guard_removed(self):
        path = self.root / 'Air2Lean/Air/Normalize.lean'
        path.write_text(path.read_text().replace('optimized float mode is outside the subset', 'accepted'))
        self.assertRejects('guard text')

    def test_shipping_flags_drift(self):
        path = self.root / 'scripts/check.sh'
        path.write_text(path.read_text().replace('-OReleaseSafe -fno-error-tracing', '-OReleaseFast -fno-error-tracing'))
        self.assertRejects("shipping.export: scripts/check.sh does not contain")

    def test_compatibility_mode_drift(self):
        path = self.root / 'compatibility.json'
        compat = json.loads(path.read_text())
        compat['translation']['optimize'] = 'ReleaseFast'
        path.write_text(json.dumps(compat))
        record(self.data, 'ReleaseFast', 'llvm')['status'] = 'unqualified'
        self.assertRejects("translation.optimize is 'ReleaseFast'")
        self.assertRejects('reference build ReleaseFast/llvm is not qualified')

    def test_doc_claim_without_record_link(self):
        (self.root / 'docs/extra.md').write_text(
            '# Extra\n\nIntro.\n\nA proof also covers the ReleaseFast build.\n')
        self.assertRejects('docs/extra.md:5: paragraph names an unchecked release mode')

    def test_readme_link_removed(self):
        path = self.root / 'README.md'
        path.write_text(path.read_text().replace('[docs/build-modes.md](docs/build-modes.md)', 'the docs'))
        self.assertRejects('README.md:')

    def test_doc_with_link_passes(self):
        (self.root / 'docs/extra.md').write_text(
            'ReleaseSmall is unqualified ([build-modes.md](build-modes.md)).\n')
        self.assertEqual(self.errors(), [])


dspec = importlib.util.spec_from_file_location('diff_report', ROOT / 'scripts/diff-report.py')
dr = importlib.util.module_from_spec(dspec)
dspec.loader.exec_module(dr)


class UnsafeModes(unittest.TestCase):
    """scripts/diff-report.py: what ReleaseFast and ReleaseSmall may exclude."""

    def classify(self, native, model, nkind, mkind, exclude_ub):
        return dr.classify(native, model, nkind, mkind, None, False, None, exclude_ub)

    def test_model_throw_is_excluded_only_without_safety_checks(self):
        args = ({'ok': 1}, {'fail': 'Zig.Error.overflow'}, dr.Kind.VALUE, dr.Kind.MODEL_PANIC)
        self.assertEqual(self.classify(*args, True), dr.Status.UB_EXCLUDED)
        self.assertEqual(self.classify(*args, False), dr.Status.MISMATCH)

    def test_value_difference_without_a_model_throw_stays_a_mismatch(self):
        args = ({'ok': 1}, {'ok': 2}, dr.Kind.VALUE, dr.Kind.VALUE)
        self.assertEqual(self.classify(*args, True), dr.Status.MISMATCH)

    def test_unrenderable_result_of_an_illegal_call(self):
        args = ({'fail': 'unknown'}, {'fail': 'Zig.Error.panic'},
                dr.Kind.NATIVE_HARNESS_FAILURE, dr.Kind.MODEL_PANIC)
        self.assertEqual(self.classify(*args, True), dr.Status.UB_EXCLUDED)
        self.assertEqual(self.classify(*args, False), dr.Status.NATIVE_HARNESS_FAILURE)

    def test_unrenderable_result_of_a_model_illegal_call(self):
        # An out-of-bounds slice pointer is `.illegal` in the model (MM-3): without safety checks
        # the native result can be a wild pointer that the harness cannot render.
        args = ({'fail': 'unknown'}, {'fail': 'Zig.Error.illegal'},
                dr.Kind.NATIVE_HARNESS_FAILURE, dr.Kind.ILLEGAL)
        self.assertEqual(self.classify(*args, True), dr.Status.UB_EXCLUDED)
        self.assertEqual(self.classify(*args, False), dr.Status.NATIVE_HARNESS_FAILURE)

    def test_harness_failure_with_a_value_model_is_never_excluded(self):
        args = ({'fail': 'unknown'}, {'ok': 1}, dr.Kind.NATIVE_HARNESS_FAILURE, dr.Kind.VALUE)
        self.assertEqual(self.classify(*args, True), dr.Status.NATIVE_HARNESS_FAILURE)

    def test_legacy_bucket(self):
        self.assertEqual(dr.legacy_bucket({'ok': 1}, {'fail': 'Zig.Error.overflow'}, False, None, None, True),
                         'ub_excluded')
        self.assertEqual(dr.legacy_bucket({'ok': 1}, {'fail': 'Zig.Error.overflow'}, False), 'mismatch')


class RunControls(Fixture):
    """Negative controls for the native run records."""

    def run_path(self, mode, backend, target='x86_64-linux'):
        return self.root / bm.RUN_DIR / f'0.16.0--{target}--{mode}--{backend}.json'

    def edit(self, mode, backend, change, target='x86_64-linux'):
        path = self.run_path(mode, backend, target)
        run = json.loads(path.read_text())
        change(run)
        path.write_text(json.dumps(run))

    def test_counts_must_add_up(self):
        self.edit('Debug', 'llvm', lambda r: r['counts'].update(value_match=r['counts']['value_match'] + 1))
        self.assertRejects('counts do not add up to cases')

    def test_safety_checked_mode_cannot_exclude_model_throws(self):
        def change(run):
            run['counts']['value_match'] -= 1
            run['counts']['ub_excluded'] = 1
        self.edit('Debug', 'llvm', change)
        self.assertRejects('Debug keeps safety checks')

    def test_mismatch_needs_triage(self):
        def change(run):
            run['counts']['value_match'] -= 1
            run['counts']['mismatch'] = 1
        self.edit('Debug', 'llvm', change)
        self.assertRejects('mismatches that the triage entries do not cover')

    def test_triage_needs_reproducer_and_stated_exception(self):
        (self.root / 'tests/roadmap/build-modes/reproducers/float-divexact-inexact.zig').unlink()
        self.assertRejects('needs a note and an existing reproducer file')
        record(self.data, 'ReleaseFast', 'llvm')['exceptions'] = []
        self.assertRejects('is not a stated exception of the record')

    def test_qualified_record_needs_every_target(self):
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'] = [
            e for e in record(self.data, 'ReleaseSafe', 'llvm')['evidence']
            if 'aarch64-macos--ReleaseSafe' not in e['path']]
        self.assertRejects('must cite a run for target aarch64-macos')

    def test_qualified_record_needs_the_aarch64_linux_run(self):
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'] = [
            e for e in record(self.data, 'ReleaseSafe', 'llvm')['evidence']
            if 'aarch64-linux--ReleaseSafe' not in e['path']]
        self.assertRejects('must cite a run for target aarch64-linux')

    def test_run_for_another_pair(self):
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'][-1]['path'] = \
            f'{bm.RUN_DIR}/0.16.0--x86_64-linux--Debug--llvm.json'
        self.assertRejects("records mode 'Debug', not 'ReleaseSafe'")

    def test_flags_must_select_backend(self):
        self.edit('Debug', 'stage2_x86_64', lambda r: r.update(flags='-ODebug -mcpu=baseline'))
        self.assertRejects('do not select -ODebug and the stage2_x86_64 backend')

    def test_stage2_only_on_x86_64(self):
        self.edit('Debug', 'stage2_x86_64', lambda r: r.update(target='aarch64-macos'))
        self.assertRejects('only generates x86_64 code')

    def test_unexplained_skipped_example(self):
        self.edit('Debug', 'stage2_x86_64', lambda r: r.update(excluded_examples=[]))
        self.assertRejects('every example left out of the run must be listed')

    def test_fast_math_in_tested_sources(self):
        (self.root / 'examples').mkdir(exist_ok=True)
        (self.root / 'examples/fm.zig').write_text('comptime { @setFloatMode(.optimized); }\n')
        self.assertRejects('fast-math needs separate treatment')

    def test_pin_violations_and_incomplete_runs(self):
        self.edit('Debug', 'llvm', lambda r: r.update(pin_violations=1))
        self.assertRejects('has pin violations')


if __name__ == '__main__':
    unittest.main()
