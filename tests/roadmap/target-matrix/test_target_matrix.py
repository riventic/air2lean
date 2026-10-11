#!/usr/bin/env python3
"""Offline declared-support target matrix regressions (Q05); no Zig, Lake or Lean process."""
import contextlib
import io
import json
from pathlib import Path
import runpy
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
TM = runpy.run_path(str(ROOT/'scripts/target-matrix.py'))
SOURCES = ['compatibility.json', TM['MAP'], TM['WORKFLOW']] + [
    p['expected'] for p in json.loads((ROOT/TM['MAP']).read_text())['abi_profiles']]
DARWIN_15 = ('0.15.2', 'aarch64-macos')


def run(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = TM['main'](list(map(str, args)))
    return code, out.getvalue() + err.getvalue()


class Scratch(unittest.TestCase):
    """Each test edits a private copy of exactly the committed inputs."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean target matrix ')
        self.root = Path(self.temp.name)
        for rel in SOURCES:
            (self.root/rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/rel, self.root/rel)

    def tearDown(self):
        self.temp.cleanup()

    def edit_json(self, rel, change):
        data = json.loads((self.root/rel).read_text())
        change(data)
        (self.root/rel).write_text(json.dumps(data))

    def edit_text(self, rel, old, new):
        text = (self.root/rel).read_text()
        self.assertIn(old, text)
        (self.root/rel).write_text(text.replace(old, new, 1))

    def entry(self, data, zig, host):
        return next(p for p in data['paths'] if (p['zig'], p['host']) == (zig, host))

    def check_fails(self, *needles, strict=False):
        args = ['check', '--root', self.root] + (['--strict'] if strict else [])
        code, output = run(*args)
        self.assertEqual(code, 1, output)
        for needle in needles:
            self.assertIn(needle, output)
        return output


def version(data, zig):
    """compatibility.json's entry for `zig` (the list is newest first)."""
    return next(v for v in data['zig']['versions'] if v['version'] == zig)


class CommittedMatrix(Scratch):
    def test_every_declared_path_is_backed_without_gaps(self):
        code, output = run('check', '--root', self.root, '--json')
        self.assertEqual(code, 0, output)
        report = json.loads(output)
        paths = {row['path']: row for row in report['paths']}
        self.assertEqual(set(paths), {
            '0.17.0/x86_64-linux/x86_64-linux/abi64-le-v1',
            '0.17.0/aarch64-macos/aarch64-macos/abi64-le-v1',
            '0.16.0/x86_64-linux/x86_64-linux/abi64-le-v1',
            '0.15.2/x86_64-linux/x86_64-linux/abi64-le-v1',
            '0.14.1/x86_64-linux/x86_64-linux/abi64-le-v1',
            '0.16.0/aarch64-macos/aarch64-macos/abi64-le-v1',
            '0.15.2/aarch64-macos/aarch64-macos/abi64-le-v1',
            '0.16.0/aarch64-linux/aarch64-linux/abi64-le-v1',
            '0.15.2/aarch64-linux/aarch64-linux/abi64-le-v1',
            '0.14.1/aarch64-linux/aarch64-linux/abi64-le-v1'})
        self.assertEqual(paths['0.16.0/aarch64-macos/aarch64-macos/abi64-le-v1']['job'], 'macos')
        self.assertEqual(paths['0.14.1/aarch64-linux/aarch64-linux/abi64-le-v1']['job'], 'aarch64-linux')
        self.assertEqual({row['status'] for row in paths.values()}, {'backed'})
        self.assertEqual([row["gaps"] for row in paths.values()], [[]] * len(paths))
        self.assertEqual(report['input_only_profiles'], ['legacy-abi64-le'])

    def test_committed_matrix_passes_strict(self):
        code, output = run('check', '--root', self.root, '--strict')
        self.assertEqual(code, 0, output)

    def test_strict_mode_rejects_recorded_gaps(self):
        def change(data):
            for zig, host in (('0.14.1', 'x86_64-linux'), DARWIN_15):
                entry = self.entry(data, zig, host)
                entry['evidence'].pop('target_probe')
                entry['gaps'] = {'target_probe': 'later'}
        self.edit_json(TM['MAP'], change)
        self.assertEqual(run('check', '--root', self.root)[0], 0)
        self.check_fails('0.14.1/x86_64-linux/x86_64-linux/abi64-le-v1: --strict',
                         '0.15.2/aarch64-macos/aarch64-macos/abi64-le-v1: --strict', strict=True)

    def test_missing_input_is_exit_2(self):
        (self.root/TM['MAP']).unlink()
        code, output = run('check', '--root', self.root)
        self.assertEqual(code, 2, output)


class ForeignGoldens(Scratch):
    def test_linux_job_compiling_the_darwin_golden_cannot_back_a_darwin_path(self):
        # Exactly the pre-Q05 state: the 0.15.2 Linux job builds Gen-darwin.lean proofs.
        def change(data):
            entry = self.entry(data, *DARWIN_15)
            entry.update(job='test', matrix={'zig': '0.15.2', 'full': True, 'mutate': False})
            entry['evidence'] = {'proof_check': ['Build threadsync proofs (macOS translation)'],
                                 'native_execution': ['Golden AIR, translate, build, differential test']}
            entry['gaps'] = {'target_probe': 'none'}
        self.edit_json(TM['MAP'], change)
        self.check_fails("runs on 'ubuntu-24.04' (x86_64-linux), not aarch64-macos",
                         'foreign-golden compilation')

    def test_foreign_golden_step_on_the_right_host_does_not_count(self):
        def change(data):
            entry = self.entry(data, '0.15.2', 'x86_64-linux')
            entry['evidence']['proof_check'] = ['Build threadsync proofs (macOS translation)']
        self.edit_json(TM['MAP'], change)
        self.check_fails('compiles foreign golden Gen-darwin.lean on linux')

    def test_macos_runner_moved_to_linux_unbacks_the_darwin_paths(self):
        self.edit_text(TM['WORKFLOW'], 'runs-on: macos-14', 'runs-on: ubuntu-24.04')
        self.check_fails('0.16.0/aarch64-macos/aarch64-macos/abi64-le-v1: job',
                         '0.15.2/aarch64-macos/aarch64-macos/abi64-le-v1: job')


class Evidence(Scratch):
    def test_unmapped_declared_path_fails(self):
        self.edit_json(TM['MAP'], lambda d: d['paths'].remove(self.entry(d, '0.16.0', 'aarch64-macos')))
        self.check_fails('0.16.0/aarch64-macos/aarch64-macos/abi64-le-v1: declared supported')

    def test_new_declared_host_without_a_job_fails(self):
        def change(data):
            version(data, '0.17.0')['hosts'].append('aarch64-linux')
        self.edit_json('compatibility.json', change)
        self.check_fails('0.17.0/aarch64-linux/aarch64-linux/abi64-le-v1: declared supported')

    def test_declared_target_listed_as_not_declared_fails(self):
        self.edit_json(TM['MAP'], lambda d: d['not_declared'].append(
            {'target': 'aarch64-linux', 'depends_on': ['T04'], 'reason': 'stale'}))
        self.check_fails('aarch64-linux is listed as not declared')

    def test_aarch64_linux_moved_off_its_runner_unbacks_its_paths(self):
        self.edit_text(TM['WORKFLOW'], 'aarch64-linux:\n    runs-on: ubuntu-24.04-arm',
                       'aarch64-linux:\n    runs-on: ubuntu-24.04')
        self.check_fails('0.14.1/aarch64-linux/aarch64-linux/abi64-le-v1: job')

    def test_entry_for_an_undeclared_path_is_stale(self):
        def change(data):
            version(data, '0.15.2')['hosts'].remove('aarch64-macos')
        self.edit_json('compatibility.json', change)
        self.check_fails('0.15.2/aarch64-macos/aarch64-macos/abi64-le-v1 is not a path')

    def test_restricted_job_without_diff_is_not_native_execution(self):
        def change(data):
            entry = self.entry(data, '0.14.1', 'x86_64-linux')
            entry['evidence']['native_execution'] = ['Golden AIR, translate, build, differential test']
        self.edit_json(TM['MAP'], change)
        self.check_fails('do not perform native_execution')

    def test_step_whose_condition_skips_the_row_does_not_count(self):
        def change(data):
            entry = self.entry(data, '0.14.1', 'x86_64-linux')
            entry['evidence']['target_probe'] = ['Float target probe']
        self.edit_json(TM['MAP'], change)
        self.check_fails("'Float target probe': its `if` is false for this row")

    def test_version_specific_abi_probes_back_only_their_version(self):
        def change(data):
            self.entry(data, '0.15.2', 'x86_64-linux')['evidence']['target_probe'] = [
                'ABI target probe (0.14.1)']
            self.entry(data, '0.16.0', 'aarch64-macos')['evidence']['target_probe'] = [
                'macOS ABI target probe (0.15.2)']
        self.edit_json(TM['MAP'], change)
        self.check_fails("0.15.2/x86_64-linux/x86_64-linux/abi64-le-v1: target_probe step "
                         "'ABI target probe (0.14.1)': its `if` is false for this row",
                         "0.16.0/aarch64-macos/aarch64-macos/abi64-le-v1: target_probe step "
                         "'macOS ABI target probe (0.15.2)': bound to Zig 0.15.2, not 0.16.0")

    def test_probe_step_must_run_the_probe(self):
        self.edit_text(TM['WORKFLOW'], 'python3 scripts/abi-probe.py observe --zig "$PWD/host-zig/zig"',
                       'python3 scripts/abi-probe.py --help --zig "$PWD/host-zig/zig"')
        self.check_fails("'ABI target probe (0.14.1)': its commands do not perform target_probe")

    def test_evidence_of_another_version_does_not_count(self):
        def change(data):
            self.entry(data, *DARWIN_15)['evidence']['proof_check'] = ['macOS proofs (0.16.0)']
        self.edit_json(TM['MAP'], change)
        self.check_fails('bound to Zig 0.16.0, not 0.15.2')

    def test_unbound_step_in_a_job_without_matrix_fails(self):
        self.edit_text(TM['WORKFLOW'], '      - name: macOS proofs (0.16.0)\n        env:\n'
                       '          AIR2LEAN_ZIG_VERSION: "0.16.0"\n',
                       '      - name: macOS proofs (0.16.0)\n        env:\n'
                       '          OTHER: "0.16.0"\n')
        self.check_fails('must bind AIR2LEAN_ZIG_VERSION')

    def test_step_commands_must_perform_the_kind(self):
        self.edit_text(TM['WORKFLOW'],
                       '          lake build Proofs\n\n      - name: macOS golden AIR, translate, differential test (0.17.0)',
                       '          lake build ZigLean\n\n      - name: macOS golden AIR, translate, differential test (0.17.0)')
        self.check_fails("'macOS proofs (0.16.0)': its commands do not perform proof_check")

    def test_missing_or_renamed_step_fails(self):
        self.edit_text(TM['WORKFLOW'], 'name: macOS ABI target probe (0.16.0)',
                       'name: macOS ABI probe (0.16.0)')
        self.check_fails("'macOS ABI target probe (0.16.0)': not found in the job")

    def test_unknown_condition_context_fails_closed(self):
        self.edit_text(TM['WORKFLOW'], '      - name: macOS proofs (0.15.2)\n',
                       "      - name: macOS proofs (0.15.2)\n        if: steps.x.outputs.y == 'true'\n")
        self.check_fails("unsupported term 'steps.x.outputs.y'")

    def test_ambiguous_matrix_selector_fails(self):
        def change(data):
            self.entry(data, '0.16.0', 'x86_64-linux')['matrix'] = {'zig': '0.16.0'}
        self.edit_json(TM['MAP'], change)
        self.check_fails('matches 6 rows')


class Gaps(Scratch):
    def test_proof_check_cannot_be_waived(self):
        def change(data):
            entry = self.entry(data, *DARWIN_15)
            entry['evidence'].pop('proof_check')
            entry['gaps'] = {'proof_check': 'later'}
        self.edit_json(TM['MAP'], change)
        self.check_fails('proof_check cannot be waived')

    def test_more_than_one_gap_is_not_a_supported_path(self):
        def change(data):
            entry = self.entry(data, *DARWIN_15)
            entry['evidence'].pop('native_execution')
            entry['evidence'].pop('target_probe')
            entry['gaps'] = {'native_execution': 'later', 'target_probe': 'later'}
        self.edit_json(TM['MAP'], change)
        self.check_fails('more than one gap')

    def test_gap_needs_a_reason_and_excludes_evidence(self):
        def change(data):
            entry = self.entry(data, *DARWIN_15)
            entry['gaps'] = {'target_probe': ' '}
        self.edit_json(TM['MAP'], change)
        self.check_fails('target_probe gap needs a reason', 'lists both evidence and a gap')


class Declarations(Scratch):
    def test_declaring_wasm_without_a_native_host_fails(self):
        def change(data):
            data['profiles'][0]['target_triples'].append('wasm32-wasi-musl')
        self.edit_json('compatibility.json', change)
        self.check_fails('declares target wasm32-wasi-musl with no supported native host',
                         'wasm32-wasi is listed as not declared')

    def test_profile_without_targets_is_not_silently_ignored(self):
        self.edit_json('compatibility.json', lambda d: d['profiles'].append(
            {'name': 'empty', 'target_triples': []}))
        self.check_fails('profile empty declares no target triples')

    def test_malformed_shapes_are_exit_2(self):
        self.edit_json('compatibility.json', lambda d: d['profiles'][0].pop('name'))
        code, output = run('check', '--root', self.root)
        self.assertEqual(code, 2, output)

    def test_evidence_must_be_a_list_of_step_names(self):
        def change(data):
            self.entry(data, '0.16.0', 'x86_64-linux')['evidence']['proof_check'] = 'Build proofs'
        self.edit_json(TM['MAP'], change)
        self.check_fails('proof_check evidence must be a list of step names')

    def test_input_only_profiles_must_match(self):
        self.edit_json(TM['MAP'], lambda d: d.__setitem__('input_only_profiles', []))
        self.check_fails('input_only_profiles [] != ')

    def test_not_declared_entries_need_a_dependency(self):
        self.edit_json(TM['MAP'], lambda d: d['not_declared'][0].pop('depends_on'))
        self.check_fails('needs depends_on and a reason')


class AbiProfiles(Scratch):
    """T04 ABI-only profiles: native probe on the profile's host, a model check of its file."""
    LINUX = 'abi 0.16.0/aarch64-linux-gnu/ReleaseSafe'

    def profile(self, data, triple='aarch64-linux-gnu'):
        return next(p for p in data['abi_profiles'] if p['target_triple'] == triple)

    def test_committed_profiles_are_abi_only(self):
        code, output = run('check', '--root', self.root, '--json')
        self.assertEqual(code, 0, output)
        rows = {row['profile']: row for row in json.loads(output)['abi_profiles']}
        self.assertEqual(set(rows), {f'{version}/{triple}/ReleaseSafe'
                                     for version in ('0.17.0', '0.16.0', '0.15.2', '0.14.1')
                                     for triple in ('aarch64-linux-gnu', 'aarch64-macos-none')})
        self.assertEqual(rows['0.16.0/aarch64-linux-gnu/ReleaseSafe']['probe_job'], 'aarch64-linux')

    def test_probe_on_another_host_does_not_count(self):
        self.edit_text(TM['WORKFLOW'], 'runs-on: ubuntu-24.04-arm', 'runs-on: ubuntu-24.04')
        self.check_fails(f"{self.LINUX}: probe: job 'aarch64-linux' runs on 'ubuntu-24.04' (x86_64-linux)")

    def test_probe_must_check_its_own_target(self):
        self.edit_text(TM['WORKFLOW'], '--target aarch64-linux-gnu --output',
                       '--target aarch64-macos-none --output')
        self.check_fails(f'{self.LINUX}: probe step', 'do not run the native probe and compare')

    def test_ignored_failure_does_not_count(self):
        self.edit_text(TM['WORKFLOW'], '"$RUNNER_TEMP/aarch64-linux-gnu-0.16.0-ReleaseSafe.txt"',
                       '"$RUNNER_TEMP/aarch64-linux-gnu-0.16.0-ReleaseSafe.txt" || true')
        self.check_fails(f'{self.LINUX}: probe step', 'ignores a failure')

    def test_proof_must_check_the_profile_file(self):
        self.edit_text(TM['WORKFLOW'], 'Model.lean aarch64-linux-gnu \\\n',
                       'Model.lean aarch64-macos-none \\\n')
        self.check_fails(f'{self.LINUX}: proof step', 'do not run the profile model check')

    def test_expected_file_must_be_versioned_and_present(self):
        self.edit_json(TM['MAP'], lambda d: self.profile(d).update(
            expected='tests/roadmap/aarch64-abi/expected/0.15.2/aarch64-linux-gnu-ReleaseSafe.txt'))
        self.check_fails('is not the versioned file of this profile')
        self.edit_json(TM['MAP'], lambda d: self.profile(d).update(
            expected='tests/roadmap/aarch64-abi/expected/0.16.0/aarch64-linux-gnu-ReleaseSafe.txt'))
        (self.root/'tests/roadmap/aarch64-abi/expected/0.16.0/aarch64-linux-gnu-ReleaseSafe.txt').unlink()
        self.check_fails('expected file tests/roadmap/aarch64-abi/expected/0.16.0/'
                         'aarch64-linux-gnu-ReleaseSafe.txt is missing')

    def test_abi_profile_does_not_declare_translation(self):
        self.edit_json(TM['MAP'], lambda d: self.profile(d).update(host='aarch64-macos'))
        self.check_fails('target aarch64-linux-gnu is not native to host aarch64-macos')


class Expressions(unittest.TestCase):
    def value(self, text, matrix=None, os='Linux'):
        return TM['evaluate'](text, {'matrix': matrix, 'runner.os': os})

    def test_github_semantics(self):
        full = {'zig': '0.16.0', 'full': True, 'mutate': False}
        restricted = {'zig': '0.14.1', 'full': False, 'mutate': False}
        self.assertEqual(self.value("matrix.full && '1' || '0'", full), '1')
        self.assertEqual(self.value("matrix.full && '1' || '0'", restricted), '0')
        self.assertTrue(self.value("!matrix.mutate && matrix.zig == '0.16.0'", full))
        self.assertFalse(self.value("!matrix.mutate && matrix.zig == '0.16.0'", restricted))
        self.assertTrue(self.value("matrix.full && matrix.zig == '0.15.2' || matrix.full && "
                                   "matrix.zig == '0.16.0'", full))
        self.assertTrue(self.value("runner.os == 'linux'"))
        self.assertFalse(self.value('failure() && !matrix.mutate', full))
        self.assertFalse(self.value('!(matrix.full)', full))
        with self.assertRaises(TM['Unknown']):
            self.value('matrix.full')
        with self.assertRaises(TM['Unknown']):
            self.value("github.ref == 'x'", full)

    def test_runner_labels(self):
        host = TM['runner_host']
        self.assertEqual(host('ubuntu-24.04'), 'x86_64-linux')
        self.assertEqual(host('ubuntu-24.04-arm'), 'aarch64-linux')
        self.assertEqual(host('macos-14'), 'aarch64-macos')
        self.assertEqual(host('macos-13'), 'x86_64-macos')
        self.assertEqual(host('macos-15-large'), 'x86_64-macos')
        self.assertIsNone(host('${{ matrix.os }}'))


if __name__ == '__main__':
    unittest.main()
