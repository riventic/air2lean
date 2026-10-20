#!/usr/bin/env python3
"""Offline declared-support target matrix regressions (Q05); no Zig, Lake or Lean process."""
import contextlib
import io
import json
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
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


# Every step after the reuse decision carries this guard (docs/ci.md, scripts/ci-reuse.py).
GUARD = '        if: ${{ !env.AIR2LEAN_REUSED }}\n'

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
            '0.17.0/aarch64-linux/aarch64-linux/abi64-le-v1',
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
        # The 0.14.1 row is not `full`: without its own AIR2LEAN_DIFF clause check.sh skips the diff.
        self.edit_text('.github/workflows/ci.yml', "matrix.full && '1' || matrix.zig == '0.14.1' && '1' || '0'",
                       "matrix.full && '1' || '0'")
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
                         "'macOS ABI target probe (0.15.2)': its `if` is false for this row")

    def test_probe_step_must_run_the_probe(self):
        self.edit_text(TM['WORKFLOW'], 'python3 scripts/abi-probe.py observe --zig "$PWD/host-zig/zig"',
                       'python3 scripts/abi-probe.py --help --zig "$PWD/host-zig/zig"')
        self.check_fails("'ABI target probe (0.14.1)': its commands do not perform target_probe")

    def test_evidence_of_another_version_does_not_count(self):
        def change(data):
            self.entry(data, *DARWIN_15)['matrix'] = {'zig': '0.16.0'}
        self.edit_json(TM['MAP'], change)
        self.check_fails('bound to Zig 0.16.0, not 0.15.2')

    def test_step_bound_to_another_version_fails(self):
        self.edit_text(TM['WORKFLOW'], '      - name: macOS proofs\n' + GUARD + '        env:\n'
                       '          AIR2LEAN_ZIG_VERSION: ${{ matrix.zig }}\n',
                       '      - name: macOS proofs\n' + GUARD + '        env:\n'
                       '          AIR2LEAN_ZIG_VERSION: "0.17.0"\n')
        self.check_fails('bound to Zig 0.17.0, not 0.16.0', 'bound to Zig 0.17.0, not 0.15.2')

    def test_unbound_step_in_a_job_without_matrix_fails(self):
        # The macos job without its matrix: one version, bound by each step's environment.
        workflow = (self.root/TM['WORKFLOW']).read_text()
        start = workflow.index('  macos:\n')
        end = workflow.index('\n  # T04: native aarch64-linux', start)
        job = workflow[start:end]
        rows = job[job.index('    strategy:\n'):job.index('    steps:\n')]
        job = job.replace(rows, '').replace('${{ matrix.zig }}', '0.16.0').replace(
            '      - name: macOS proofs\n' + GUARD + '        env:\n          AIR2LEAN_ZIG_VERSION: 0.16.0\n',
            '      - name: macOS proofs\n' + GUARD + '        env:\n          OTHER: 0.16.0\n')
        (self.root/TM['WORKFLOW']).write_text(workflow[:start] + job + workflow[end:])

        def change(data):
            data['paths'] = [p for p in data['paths'] if p['host'] != 'aarch64-macos' or p['zig'] == '0.16.0']
            self.entry(data, '0.16.0', 'aarch64-macos').pop('matrix')
            data['abi_profiles'][1]['probe'].pop('matrix')
        self.edit_json(TM['MAP'], change)
        self.check_fails('must bind AIR2LEAN_ZIG_VERSION')

    def test_step_commands_must_perform_the_kind(self):
        self.edit_text(TM['WORKFLOW'], '          lake build Proofs\n\n      # As in the test job',
                       '          lake build ZigLean\n\n      # As in the test job')
        self.check_fails("'macOS proofs': its commands do not perform proof_check")

    def test_missing_or_renamed_step_fails(self):
        self.edit_text(TM['WORKFLOW'], 'name: macOS ABI target probe (0.16.0)',
                       'name: macOS ABI probe (0.16.0)')
        self.check_fails("'macOS ABI target probe (0.16.0)': not found in the job")

    def test_unknown_condition_context_fails_closed(self):
        self.edit_text(TM['WORKFLOW'], '      - name: macOS proofs\n' + GUARD,
                       "      - name: macOS proofs\n        if: ${{ !env.AIR2LEAN_REUSED && steps.x.outputs.y == 'true' }}\n")
        self.check_fails("unsupported term 'steps.x.outputs.y'")

    def test_ambiguous_matrix_selector_fails(self):
        def change(data):
            self.entry(data, '0.16.0', 'x86_64-linux')['matrix'] = {'zig': '0.16.0'}
        self.edit_json(TM['MAP'], change)
        self.check_fails('matches 15 rows')


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


class WorkflowData(unittest.TestCase):
    def test_shared_matrix_boundary_refuses_axes_before_target_projection(self):
        text='''jobs:
  test:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        flag: [true]
        include:
          - zig: "0.17.0"
    steps:
      - name: gate
        if: ${{ !matrix.flag }}
        run: lake build Proofs
'''
        entry={'job':'test','matrix':{'zig':'0.17.0'},'evidence':{'proof_check':['gate']}}
        for reader in (TM['parse_workflow_yaml'],TM['parse_workflow'],
                       lambda source:TM['check_entry'](entry,('0.17.0','x86_64-linux'),TM['parse_workflow'](source))):
            with self.subTest(reader=reader),self.assertRaisesRegex(TM['Unreadable'],
                    'ci.yml: job test: only strategy.matrix.include is supported'):
                reader(text)

    def selector_jobs(self, rows):
        return TM['parse_workflow']('''jobs:
  test:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        include:
'''+rows+'''    steps:
      - name: gate
        run: |
          scripts/check.sh
          scripts/floatprobe.sh
          lake build Proofs
''')

    def assert_selected(self, jobs, selector, expected):
        job,context,errors=TM['job_context'](jobs,'test',selector,'x86_64-linux')
        self.assertEqual(errors,[])
        self.assertEqual(TM['canonical'](context['matrix']),TM['canonical'](expected))
        entry={'job':'test','matrix':selector,'evidence':{kind:['gate'] for kind in TM['KINDS']}}
        self.assertEqual(TM['check_entry'](entry,('0.17.0','x86_64-linux'),jobs),([],[]))

    def test_both_actual_selectors_preserve_numeric_boolean_data_identity(self):
        rows='''          - zig: "0.17.0"
            flag: 0.0
          - zig: "0.17.0"
            flag: false
'''
        jobs=self.selector_jobs(rows)
        for flag in (0.0,False):
            with self.subTest(flag=repr(flag)):
                self.assert_selected(jobs,{'flag':flag},{'zig':'0.17.0','flag':flag})
        numeric=self.selector_jobs('          - zig: "0.17.0"\n            flag: 0.0\n')
        entry={'job':'test','matrix':{'flag':False}}
        self.assertIn('matches 0 rows',TM['check_entry'](entry,('0.17.0','x86_64-linux'),numeric)[0][0])
        self.assertIn('matches 0 rows',TM['job_context'](numeric,'test',{'flag':False})[2][0])

    def test_both_actual_selectors_require_presence_for_explicit_null(self):
        jobs=self.selector_jobs('''          - zig: "0.17.0"
          - zig: "0.17.0"
            optional: null
''')
        self.assert_selected(jobs,{'optional':None},{'zig':'0.17.0','optional':None})
        absent=self.selector_jobs('          - zig: "0.17.0"\n')
        entry={'job':'test','matrix':{'optional':None}}
        self.assertIn('matches 0 rows',TM['check_entry'](entry,('0.17.0','x86_64-linux'),absent)[0][0])
        self.assertIn('matches 0 rows',TM['job_context'](absent,'test',{'optional':None})[2][0])

    def test_projection_refuses_invalid_container_shapes_with_job_context(self):
        templates=(('jobs:\n  test: VALUE\n','must be a mapping'),
                   ('jobs:\n  test:\n    env: VALUE\n','env'),
                   ('jobs:\n  test:\n    strategy: VALUE\n','strategy'),
                   ('jobs:\n  test:\n    strategy:\n      matrix: VALUE\n','strategy.matrix'),
                   ('jobs:\n  test:\n    strategy:\n      matrix:\n        include: VALUE\n','include'),
                   ('jobs:\n  test:\n    steps: VALUE\n','step'),
                   ('jobs:\n  test:\n    steps:\n      - name: gate\n        env: VALUE\n','step 0 env'))
        for template,field in templates:
            values=('false','0','null','""','[wrong]')+(() if field in ('step','include') else ('[]',))
            for value in values:
                with self.subTest(field=field,value=value),self.assertRaisesRegex(TM['Unreadable'],
                        r'ci.yml: job test.*'+re.escape(field)):
                    TM['parse_workflow'](template.replace('VALUE',value))
        with self.assertRaisesRegex(TM['Unreadable'],'include must be a list of mappings'):
            TM['parse_workflow']('jobs:\n  test:\n    strategy:\n      matrix:\n        include: [wrong]\n')
        jobs=TM['parse_workflow']('jobs:\n  test:\n    runs-on: ubuntu-24.04\n')
        self.assertEqual(jobs['test']['env'],{})
        self.assertEqual(jobs['test']['steps'],[])
        self.assertIsNone(jobs['test']['matrix'])

    def test_raw_unicode_breaks_refuse_while_runtime_unicode_transport_is_preserved(self):
        for separator in ('\u2028','\u2029'):
            with self.subTest(separator=separator):
                with self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:2: unsupported raw YAML Unicode line break'):
                    TM['parse_workflow_yaml']('name: CI\nflag: false'+separator+'\n')
                decoded='東京'+separator+'payload'
                self.assertEqual(TM['expression_string'](decoded),decoded)
                self.assertEqual(TM['interpolate']('${{ matrix.value }}',{'matrix':{'value':decoded}}),decoded)
                self.assertTrue(TM['condition']('matrix.value',{'matrix':{'value':decoded}}))
    def test_literal_block_grid_matches_specification_content_and_breaks(self):
        # YAML 1.2.2 productions165/171/173: empty lines, literal text, and final chomp.
        bodies=(([],('', '', ''),('', '', '\n')),
                (['a'],('a','a','a'),('a\n','a','a\n')),
                (['','a'],('\na','\na','\na'),('\na\n','\na','\na\n')),
                (['a','','b'],('a\n\nb','a\n\nb','a\n\nb'),('a\n\nb\n','a\n\nb','a\n\nb\n')),
                (['a',''],('a\n','a','a\n'),('a\n','a','a\n\n')),
                (['a','  '],('a\n  ','a\n  ','a\n  '),('a\n  \n','a\n  ','a\n  \n')),
                (['a','  b'],('a\n  b','a\n  b','a\n  b'),('a\n  b\n','a\n  b','a\n  b\n')),
                (['a','\u00a0'],('a\n\u00a0','a\n\u00a0','a\n\u00a0'),('a\n\u00a0\n','a\n\u00a0','a\n\u00a0\n')))
        for column,header in enumerate(('|','|-','|+')):
            for width in (2,4):
                for body,at_eof,with_break in bodies:
                    for ended in (False,True):
                        text='value: '+header+'\n'+'\n'.join(' '*width+line for line in body)
                        if ended:text+='\n'
                        with self.subTest(header=header,width=width,body=body,ended=ended):
                            self.assertEqual(TM['parse_workflow_yaml'](text)['value'],(with_break if ended else at_eof)[column])
        for text,expected in (('value: |\n  on','on'),('value: |\n  on\n','on\n'),
                              ('value: |-\n  a\n    \n','a\n  '),
                              ('value: |+\n  a\n\n','a\n\n'),('value: |+\n  on','on'),
                              ('value: |+\n  \n','\n')):
            self.assertEqual(TM['parse_workflow_yaml'](text)['value'],expected)

    def test_literal_block_unsupported_indentation_and_headers_refuse(self):
        for text in ('value: |\n    \n  text\n','value: |-\n    a\n  b\n',
                     'value: |\n\t\n','value: |\n  a\n  \t\n','value: "a\tb"\n'):
            with self.subTest(text=text):
                with self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:[0-9]+:'):
                    TM['parse_workflow_yaml'](text)
        for header in ('|++','|2','|2-','|-2','| # comment','>'):
            with self.subTest(header=header),self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:1:'):
                TM['parse_workflow_yaml']('value: '+header+'\n  text\n')

    def test_literal_eof_data_keeps_actual_conditional_target_gate(self):
        text='''jobs:
  test:
    runs-on: ubuntu-24.04
    steps:
      - name: EOF gate
        if: matrix.examples == 'on'
        run: |
          scripts/check.sh
          scripts/floatprobe.sh
          lake build Proofs
    strategy:
      matrix:
        include:
          - zig: "0.17.0"
            examples: |
              on'''
        entry={'job':'test','matrix':{'zig':'0.17.0'},
               'evidence':{kind:['EOF gate'] for kind in TM['KINDS']}}
        self.assertEqual(TM['check_entry'](entry,('0.17.0','x86_64-linux'),TM['parse_workflow'](text)),([],[]))
        for value in ('left:','left: # comment'):
            with self.subTest(value=value),self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:1: unsupported YAML syntax'):
                TM['parse_workflow']('value: '+value+'\n')

    def test_plain_scalar_kinds_are_explicit_and_quoted_scalars_stay_strings(self):
        cases=(('0.0',float,0.0),('-0',int,0),('+12',int,12),('001',int,1),
               ('FALSE',bool,False),('True',bool,True),('Null',type(None),None),
               ('~',type(None),None),('１',str,'１'),('yes',str,'yes'),
               ('on',str,'on'),('0.17.0',str,'0.17.0'),('\u00a00.0\u00a0',str,'\u00a00.0\u00a0'),("'FALSE'",str,'FALSE'),
               ('"null"',str,'null'),("'it''s exact'",str,"it's exact"))
        for source,kind,value in cases:
            with self.subTest(source=source):
                result=TM['parse_workflow_yaml']('value: '+source+'\n')['value']
                self.assertIs(type(result),kind)
                self.assertEqual(result,value)

    def test_real_yaml_false_kinds_cannot_back_conditional_proof_evidence(self):
        entry={'job':'test','matrix':{'zig':'0.17.0'},
               'evidence':{'proof_check':['DATA-dependent proof']},
               'gaps':{'native_execution':'fixture','target_probe':'fixture'}}
        text='''jobs:
  test:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        include:
          - zig: "0.17.0"
            flag: VALUE
    steps:
      - name: DATA-dependent proof
        if: matrix.flag
        run: lake build Proofs
'''
        for source,applies in (('0.0',False),('-0',False),('FALSE',False),('null',False),
                               ('1.5',True),('TRUE',True),('１',True),('\u00a00.0\u00a0',True),("'FALSE'",True)):
            with self.subTest(source=source):
                errors,_=TM['check_entry'](entry,('0.17.0','x86_64-linux'),
                                          TM['parse_workflow'](text.replace('VALUE',source)))
                self.assertEqual(any('its `if` is false' in error for error in errors),not applies,errors)
                self.assertEqual([e for e in errors if 'proof_check' in e],[] if applies else [
                    '0.17.0/x86_64-linux: proof_check step \'DATA-dependent proof\': its `if` is false for this row'])
        errors,_=TM['check_entry'](entry,('0.17.0','x86_64-linux'),TM['parse_workflow'](
            text.replace('VALUE','１').replace('if: matrix.flag','if: matrix.flag == 1')))
        self.assertTrue(any("unsupported numeric string '１'" in error for error in errors),errors)

    def test_unqualified_yaml_forms_refuse_with_workflow_and_line(self):
        for source in ('0x10','0o10','1e2','.inf','.NaN','!!str false','&anchor false',
                       '*anchor','["a,b"]','[a,,b]','[a,]','{x: 1}',
                       '"escape\\n"','>','|++','plain: nested','1\x1c','1\x86','1\x9f'):
            with self.subTest(source=source),self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:1:'):
                TM['parse_workflow_yaml']('value: '+source+'\n')

    def test_data_integer_identity_is_preserved_before_expression_consumption(self):
        row=TM['parse_workflow_yaml']('shard: 1\nlarge: 9007199254740993\n')
        self.assertIs(type(row['shard']),int)
        self.assertEqual(str(row['shard']),'1')
        self.assertEqual(row['large'],2**53+1)
        self.assertTrue(TM['condition']('matrix.large == 9007199254740992',{'matrix':row}))

    def test_colon_structure_is_only_supported_in_quoted_or_block_strings(self):
        for value in ("'left: right'",'"left: right"','|-\n  left: right'):
            with self.subTest(value=value):
                self.assertEqual(TM['parse_workflow_yaml']('value: '+value+'\n')['value'],'left: right')
        with self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:1: unsupported YAML syntax'):
            TM['parse_workflow_yaml']('value: left: right\n')
        for key in ('false','NULL','1'):
            with self.subTest(key=key),self.assertRaisesRegex(TM['Unreadable'],r'ci.yml:1: unsupported non-string mapping key'):
                TM['parse_workflow_yaml'](key+': value\n')
        self.assertEqual(TM['parse_workflow_yaml']('value: |-\n  before\n  \u00a0\n  after\n')['value'],
                         'before\n\u00a0\nafter')

    def test_real_yaml_bound_environment_uses_shared_scalar_conversion(self):
        for source,enabled in (('0',False),('FALSE',True),("'0'",False),('1',True)):
            with self.subTest(source=source):
                job=TM['parse_workflow']('''jobs:
  test:
    runs-on: ubuntu-24.04
    env:
      AIR2LEAN_ZIG_VERSION: "0.17.0"
    steps:
      - name: Native gate
        env:
          AIR2LEAN_DIFF: VALUE
        run: scripts/check.sh
'''.replace('VALUE',source))['test']
                errors=TM['check_step'](job['steps'],job,{'matrix':None},'0.17.0','native_execution','linux')
                self.assertEqual(errors,[] if enabled else ['its commands do not perform native_execution'])
                if source=='FALSE':
                    self.assertEqual(TM['expression_string'](job['steps'][0]['env']['AIR2LEAN_DIFF']),'false')


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

    def test_comparisons_reject_unsupported_values_and_numeric_overflow(self):
        for value in ([], {}, ('tuple',), object()):
            for expression in ('matrix.value == 1', '1 != matrix.value',
                               'matrix.value == null', 'null != matrix.value',
                               'matrix.value == matrix.value'):
                with self.subTest(value=value, expression=expression), self.assertRaisesRegex(TM['Unknown'], 'matrix.value: unsupported expression scalar'):
                    self.value(expression, {'value': value})
        with self.assertRaisesRegex(TM['Unknown'], 'outside the GitHub expression range'):
            self.value('matrix.value == 1', {'value': 10**4000})
        for value, expected in ((1, True), (1.0, True), (2, False)):
            with self.subTest(value=value):
                self.assertEqual(self.value('matrix.value == 1', {'value': value}), expected)
                self.assertEqual(self.value('matrix.value != 1', {'value': value}), not expected)

    def test_comparisons_support_own_kinds_and_canonical_binary64(self):
        for left, right, expected in ((None, None, True), (False, False, True), (True, False, False),
                                      ('LINUX', 'linux', True), ('NaN', 'nan', True),
                                      ('Infinity', 'infinity', True), ('1e2', '1E2', True), ('0x10', '0X10', True),
                                      (1, 1.0, True), (2**53 + 1, 2**53, True),
                                      (2**53 + 2, 2**53, False), (-0.0, 0, True),
                                      (float('1.7976931348623157e308'), float('1.7976931348623157e308'), True)):
            with self.subTest(left=left, right=right):
                self.assertEqual(self.value('matrix.left == matrix.right', {'left': left, 'right': right}), expected)
                self.assertEqual(self.value('matrix.left != matrix.right', {'left': left, 'right': right}), not expected)
        self.assertFalse(self.value("'1.0' == '1'"))
        for expression in ('null == 0', 'null != false', "null == ''", 'true == 1', 'false == 0'):
            with self.subTest(expression=expression), self.assertRaisesRegex(TM['Unknown'], 'mixed-kind'):
                self.value(expression)

    def test_number_string_comparisons_share_supported_decimal_conversion(self):
        for text, numeric, expected in (('',0,True),('   ',0,True),('\u00a0',0,True),
                                        ('+16',16,True),('-.25',-.25,True),('1.5',1.5,True),
                                        ('2',1,False),(str(2**53+1),2**53,True)):
            for expression in ('matrix.text == matrix.numeric','matrix.numeric == matrix.text'):
                with self.subTest(text=text,numeric=numeric,expression=expression):
                    row={'text':text,'numeric':numeric}
                    self.assertEqual(self.value(expression,row),expected)
                    self.assertEqual(self.value(expression.replace('==','!='),row),not expected)
        for text in ('0x10','0o10','1_0','1e2','Infinity','NaN','ordinary','١٠','10\0','9'*309):
            for expression in ('matrix.text == matrix.numeric','matrix.numeric == matrix.text'):
                with self.subTest(text=text,expression=expression),self.assertRaises(TM['Unknown']) as caught:
                    self.value(expression,{'text':text,'numeric':10})
                self.assertIn(expression,str(caught.exception))

    def test_decimal_conversion_supports_trimmed_text_and_finite_range_boundaries(self):
        for text, expected in (('', 0), (' \t\n', 0), ('+16', 16), ('-16', -16), ('.5', .5),
                               ('5.', 5), ('-.25', -.25), ('001.50', 1.5),
                               (str(2**53 + 1), float(2**53)),
                               ('17976931348623157' + '0'*292, float('1.7976931348623157e308')),
                               ('0.' + '0'*323 + '5', float('5e-324')),
                               ('0.' + '0'*400 + '1', 0)):
            with self.subTest(text=text):
                self.assertEqual(TM['number'](text), expected)
        for text in ('0x10', '0o10', '1_0', '1e2', '-1E-2', 'Infinity', 'NaN', 'inf',
                     '١٠', '１２', '10\0', 'not numeric', '9'*309):
            with self.subTest(text=text), self.assertRaises(TM['Unknown']):
                TM['number'](text)
        for value in (None, True, False):
            with self.subTest(value=value), self.assertRaises(TM['Unknown']):
                TM['number'](value)

    def test_nonfinite_and_aggregate_context_values_fail_at_every_consumption(self):
        for value in (float('nan'), float('inf'), float('-inf'), [], {}, ('tuple',), object()):
            context = {'matrix': {'value': value}}
            for expression in ('matrix.value', '!matrix.value', 'matrix.value == matrix.value',
                               'matrix.value != 1', 'true || matrix.value',
                               "format('{0}', matrix.value)", "format('unused', matrix.value)"):
                with self.subTest(value=value, expression=expression), self.assertRaisesRegex(TM['Unknown'], 'matrix.value:'):
                    TM['condition'](expression, context)
            with self.assertRaisesRegex(TM['Unknown'], 'matrix.value:'):
                TM['interpolate']('${{ matrix.value }}', context)
            for consumer in (TM['truthy'], TM['expression_string']):
                with self.assertRaises(TM['Unknown']):
                    consumer(value)
        for text in ('NaN', 'Infinity', '1e2', 'not numeric'):
            context = {'matrix': {'value': text}}
            self.assertEqual(TM['interpolate']('${{ matrix.value }}', context), text)
            self.assertTrue(TM['condition']('matrix.value', context))

    def test_expression_whitespace_is_shared_with_decimal_conversion(self):
        whitespace = ('\t\n\v\f\r \x85\xa0\u1680\u2000\u2001\u2002\u2003\u2004\u2005'
                      '\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000')
        for char in whitespace:
            with self.subTest(char=ord(char)):
                self.assertEqual(TM['number'](char + '1' + char), 1)
                self.assertTrue(TM['condition'](char + 'true' + char, {}))
                self.assertTrue(TM['condition'](char + '${{' + char + 'true' + char + '}}' + char, {}))
        for char in ('\x1c', '\x1d', '\x1e', '\x1f', '\u180e', '\u200b', '\ufeff'):
            for text in (char + 'true', 'true' + char, 'true' + char + '&& true',
                         char + '${{ true }}', '${{' + char + 'true }}'):
                with self.subTest(char=ord(char), text=text), self.assertRaises(TM['Unknown']):
                    TM['condition'](text, {})
            with self.assertRaises(TM['Unknown']):
                TM['number'](char + '1' + char)
            self.assertEqual(self.value("'" + char + "'"), char)  # String data is not token whitespace.

    def test_unsupported_numeric_literals_and_nonascii_identifiers_fail_closed(self):
        self.assertTrue(self.value('+1.5 == 1.5'))
        self.assertTrue(self.value('.5 == 0.5'))
        for expression in ('1e2 == 100', '-2.99e-2 == -0.0299', '0x10 == 16', '0o10 == 8',
                           '1_0 == 10', '١٠ == 10', '1٢ == 12', 'Infinity == 1', 'NaN == 1',
                           'matrix.é', 'matrix.xé == 1'):
            with self.subTest(expression=expression), self.assertRaises(TM['Unknown']):
                self.value(expression, {'é': True, 'xé': 1})

    def test_string_comparison_is_ascii_only_while_unicode_transport_is_preserved(self):
        for left, right in (('K', 'k'), ('k', 'K'), ('Σ', 'ς'), ('é', 'é'), ('ascii', 'é')):
            for operator in ('==', '!='):
                expression = 'matrix.left %s matrix.right' % operator
                with self.subTest(left=left, right=right, operator=operator), self.assertRaises(TM['Unknown']) as caught:
                    self.value(expression, {'left': left, 'right': right})
                self.assertIn(expression, str(caught.exception))
                self.assertIn('non-ASCII string comparison', str(caught.exception))
        self.assertTrue(self.value("'LiNuX' == 'linux'"))
        self.assertFalse(self.value("'different' == 'TEXT'"))
        for text in ('K', 'Σς', 'é', '東京', ''):
            context = {'matrix': {'value': text}}
            self.assertEqual(TM['evaluate']('matrix.value', context), text)
            self.assertEqual(TM['interpolate']('${{ matrix.value }}', context), text)
            self.assertEqual(TM['evaluate']("format('{0}', matrix.value)", context), text)
            self.assertEqual(TM['condition']('matrix.value', context), bool(text))

    def test_identifier_segments_and_nested_matrix_references_fail_closed(self):
        for expression in ('matrix.1', 'matrix..x', 'matrix.x.', 'matrix.x.1',
                           'matrix.foo.bar', 'matrix.foo.bar == true'):
            row = {'1': True, '.x': True, 'x.': True, 'x.1': True,
                   'foo.bar': True, 'foo': {'bar': False}}
            with self.subTest(expression=expression), self.assertRaises(TM['Unknown']):
                self.value(expression, row)
        with self.assertRaisesRegex(TM['Unknown'], 'unsupported nested matrix reference'):
            self.value('matrix.foo.bar', {'foo.bar': True, 'foo': {'bar': False}})
        for name, value in (('x1', 1), ('_x', 2), ('x-y', 3)):
            with self.subTest(name=name):
                self.assertEqual(self.value('matrix.' + name, {name: value}), value)

    def test_matrix_fields_are_ascii_case_insensitive_without_ambiguous_fallback(self):
        self.assertTrue(self.value("matrix.ZIG == '0.17.0'", {'zig': '0.17.0'}))
        self.assertTrue(self.value("matrix.zig == '0.17.0'", {'ZIG': '0.17.0'}))
        self.assertEqual(self.value('matrix.missing', {'zig': '0.17.0'}), None)
        self.assertTrue(self.value('matrix.missing == null', {'zig': '0.17.0'}))
        for row in ({'zig': '0.17.0', 'ZIG': '0.16.0'}, {'zig': 'same', 'ZIG': 'same'}):
            for reference in ('matrix.zig', 'matrix.ZIG'):
                with self.subTest(row=row, reference=reference), self.assertRaisesRegex(TM['Unknown'], 'ambiguous case variants'):
                    self.value(reference, row)
        with self.assertRaisesRegex(TM['Unknown'], 'ambiguous case variants'):
            self.value('matrix.zig', {'other': 1, 'OTHER': 2, 'zig': '0.17.0'})
        for row in ({'K': True}, {'é': True, 'key': True}, {1: True}):
            with self.subTest(row=row), self.assertRaisesRegex(TM['Unknown'], 'context key'):
                self.value('matrix.key', row)
        for reference in ('Matrix.zig', 'MATRIX.missing', 'RUNNER.os'):
            with self.subTest(reference=reference), self.assertRaises(TM['Unknown']):
                self.value(reference, {'zig': '0.17.0'})

    def test_format_documented_examples_and_literal_braces(self):
        self.assertEqual(self.value("format('Hello {0} {1} {2}', 'Mona', 'the', 'Octocat')"),
                         'Hello Mona the Octocat')
        self.assertEqual(self.value("format('{{Hello {0} {1} {2}!}}', 'Mona', 'the', 'Octocat')"),
                         '{Hello Mona the Octocat!}')
        self.assertEqual(self.value("FoRmAt('{1}:{0}:{1}:{{literal}}', 'x', 'y')"),
                         'y:x:y:{literal}')
        self.assertEqual(self.value("format('{0}', '{1}')"), '{1}')
        self.assertEqual(self.value("format('literal')"), 'literal')
        self.assertEqual(self.value("format(null, 'unused')"), '')
        self.assertEqual(self.value("format('{0}', format('{0}!', 'nested'))"), 'nested!')

    def test_format_uses_explicit_workspace_temp_and_nested_matrix_context(self):
        context = {'matrix': {'zig': '0.17.0'}, 'runner.os': 'Linux',
                   'github.workspace': '/work tree', 'runner.temp': '/tmp/CI run'}
        expression = "format('{0}/zig-air-{1}/bin/zig', github.workspace, matrix.zig)"
        self.assertEqual(TM['evaluate'](expression, context), '/work tree/zig-air-0.17.0/bin/zig')
        self.assertEqual(TM['interpolate']('${{ '+expression+' }}', context),
                         '/work tree/zig-air-0.17.0/bin/zig')
        self.assertEqual(TM['evaluate']("format('{0}/{1}', runner.temp, runner.os)", context),
                         '/tmp/CI run/Linux')
        self.assertEqual(TM['evaluate']("format('{0}', env.AIR2LEAN_REUSED)",
                                      {'env.AIR2LEAN_REUSED': 'a different run'}), '')

    def test_format_and_interpolation_share_github_scalar_conversion(self):
        # The runner uses invariant G15, including when a number is a matrix integer.
        for value, expected in ((None, ''), (True, 'true'), (False, 'false'), ('text', 'text'),
                                (3, '3'), (3.0, '3'), (-2.5, '-2.5'), (-0.0, '-0'),
                                (1e20, '1E+20'), (1e-5, '1E-05'),
                                (1.2345678901234567, '1.23456789012346'),
                                (9007199254740993, '9.00719925474099E+15')):
            with self.subTest(value=value):
                context = {'matrix': {'value': value}}
                self.assertEqual(TM['evaluate']("format('{0}', matrix.value)", context), expected)
                self.assertEqual(TM['interpolate']('${{ matrix.value }}', context), expected)
        self.assertEqual(self.value("format('{0}/{1}', -9.2, -0.0299)"), '-9.2/-0.0299')

    def test_format_rejects_directives_traversal_unbalanced_fields_and_missing_arguments(self):
        for field in ('{}', '{name}', '{0.name}', '{0[0]}', '{0!r}', '{0:}', '{0:>8}',
                      '{0:.2f}', '{-1}', '{0', '}', '{1}'):
            with self.subTest(field=field), self.assertRaises(TM['Unknown']):
                self.value("format('"+field+"', 'one')")
        for expression in ("format()", "format('{0}')", "format('{0}',)",
                           "format('{0}', 'x'", "format('{0}', , 'x')", "success(true)"):
            with self.subTest(expression=expression), self.assertRaises(TM['Unknown']):
                self.value(expression)

    def test_format_argument_bounds_match_the_runner(self):
        arguments = ', '.join(["'x'"] * 254)
        self.assertEqual(self.value("format('{253}', "+arguments+")"), 'x')
        with self.assertRaises(TM['Unknown']):
            self.value("format('unused', "+arguments+", 'one too many')")

    def test_unknown_context_and_nonscalar_string_conversion_fail_closed(self):
        for expression in ("format('{0}', github.workspace)", "format('{0}', runner.temp)",
                           "format('unused', github.ref)", "format('{0}', steps.x.outputs.y)"):
            with self.subTest(expression=expression), self.assertRaises(TM['Unknown']):
                self.value(expression)
        for value in ([], {}, ('tuple',), object()):
            context = {'matrix': {'value': value}}
            with self.subTest(value=value), self.assertRaises(TM['Unknown']):
                TM['evaluate']("format('{0}', matrix.value)", context)
            with self.assertRaises(TM['Unknown']):
                TM['interpolate']('${{ matrix.value }}', context)
        with self.assertRaises(TM['Unknown']):
            TM['evaluate']('matrix.zig', {'matrix': []})

    def test_interpolation_respects_quoted_delimiters_and_rejects_incomplete_expressions(self):
        self.assertEqual(TM['interpolate']("before ${{ format('{{{0}}}', 'It''s fine') }} after", {}),
                         "before {It's fine} after")
        self.assertEqual(TM['interpolate']("${{ '}}' }} ${{ format('{0}', '${{') }}", {}), '}} ${{')
        for text in ("${{ format('{0}', 'x')", "${{ format('{0}', 'x) }}",
                     "${{ 'valid' }} then ${{", "${{ unknown.context }}"):
            with self.subTest(text=text), self.assertRaises(TM['Unknown']):
                TM['interpolate'](text, {})

    def test_literal_boolean_conditions_keep_their_value(self):
        self.assertTrue(TM['condition'](None, {}))
        self.assertTrue(TM['condition'](True, {}))
        self.assertFalse(TM['condition'](False, {}))
        for value in (0, 1, [], {}):
            with self.subTest(value=value), self.assertRaisesRegex(TM['Unknown'], 'condition type'):
                TM['condition'](value, {})

    def test_unterminated_quoted_interpolation_rejects_without_backtracking_hang(self):
        probe = '''import runpy,sys
module=runpy.run_path(sys.argv[1])
try:module['interpolate']('${{ '+"'"*10000,{})
except module['Unknown']:raise SystemExit(0)
raise SystemExit('malformed interpolation was accepted')
'''
        result = subprocess.run([sys.executable, '-c', probe, str(ROOT/'scripts/target-matrix.py')],
                                capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors='replace'))

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
