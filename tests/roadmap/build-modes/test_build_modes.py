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
        self.assertIn('8 records, 1 qualified', out.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(bm.main(['commands']), 0)
        self.assertIn('ReleaseFast.json', out.getvalue())

    def test_reference_build_is_the_only_qualified_pair(self):
        qualified = [(r['mode'], r['backend']) for r in REGISTRY['records'] if r['status'] == 'qualified']
        self.assertEqual(qualified, [('ReleaseSafe', 'llvm')])

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
        record(self.data, 'ReleaseSafe', 'llvm')['evidence'] = []
        self.assertRejects('must cite profile evidence')
        self.assertRejects('must cite command evidence')

    def test_qualifying_without_evidence_or_claim(self):
        debug = record(self.data, 'Debug', 'llvm')
        debug['status'] = 'qualified'
        self.assertRejects('Debug/llvm: a qualified record must state its claim')
        self.assertRejects('Debug/llvm: a qualified record must cite profile evidence')

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
        del record(self.data, 'ReleaseFast', 'llvm')['commands']
        self.assertRejects('must list the commands')

    def test_excluded_cannot_claim(self):
        record(self.data, 'ReleaseFast', 'stage2_x86_64')['claim'] = 'no-illegal-behaviour-transfer'
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


if __name__ == '__main__':
    unittest.main()
