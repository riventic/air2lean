#!/usr/bin/env python3
"""First-use shell regressions. Every compiler/toolchain command is a fake."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
SHELL = os.environ.get('AIR2LEAN_TEST_BASH', 'bash')

FAKE = r'''#!/usr/bin/env python3
import json, os, pathlib, sys
kind = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
root = pathlib.Path(os.environ['MOCK_REPO'])
mode = os.environ.get('MOCK_MODE', '')
with open(os.environ['MOCK_LOG'], 'a') as f:
    f.write(json.dumps([kind, args, os.environ.get('ZIG_AIR_JSON_DIR'), os.getcwd(), os.environ.get('ZIG_AIR_JSON_FILTER')]) + '\n')
if kind == 'elan':
    toolchain = (root / 'lean-toolchain').read_text().strip()
    if args == ['toolchain', 'list']:
        print('no installed toolchains' if mode == 'missing-lean' else toolchain + ' (default)')
    else:
        assert args[:3] == ['run', toolchain, 'lake'], args
        assert os.environ.get('LEAN_NUM_THREADS') == '1'
        action = args[3:]
        if action == ['build', 'ZigLean', 'air2lean']:
            if mode == 'build-fail': sys.exit(1)
            if mode == 'hold-build':
                import time
                gate = pathlib.Path(os.environ['MOCK_BUILD_GATE'])
                gate.with_suffix('.ready').touch()
                while not gate.exists(): time.sleep(0.01)
            target = root / '.lake/build/bin/air2lean'
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(pathlib.Path(__file__).read_text())
            target.chmod(0o755)
        else:
            assert action[:2] == ['env', 'lean'], action
            assert pathlib.Path(action[2]).read_text().startswith('import ZigLean\n')
            if mode == 'lean-fail': sys.exit(1)
elif kind in ('zig', 'stock-zig'):
    if args == ['version']:
        print('0.15.2' if mode == 'wrong-version' and kind == 'zig' else '0.16.0')
    else:
        assert kind == 'zig'
        assert args[:7] == ['build-obj', '-fno-emit-bin', '-OReleaseSafe', '-fno-error-tracing', '-target', 'x86_64-linux', '-mcpu=baseline'], args
        assert pathlib.Path(args[7]).is_file()
        if mode == 'export-fail': sys.exit(1)
        air = pathlib.Path(os.environ['ZIG_AIR_JSON_DIR'])
        assert list(air.iterdir()) == [], 'AIR directory must be fresh'
        if mode != 'empty-air': (air / 'source.foo.json').write_text('{}')
        if mode == 'partial-export': print('warning: air2lean: name too long for a file, no JSON for source.long', file=sys.stderr)
elif kind == 'air2lean':
    assert pathlib.Path(args[0]).is_dir()
    assert list(pathlib.Path(args[0]).glob('*.json'))
    if mode == 'translate-fail': sys.exit(1)
    if mode != 'missing-output': pathlib.Path(args[args.index('-o')+1]).write_text('import ZigLean\n-- fresh generated output\n')
else:
    raise AssertionError('unexpected tool ' + kind)
'''


class Workflow(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean mock space ')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / 'repo with spaces'
        (self.repo / 'scripts').mkdir(parents=True)
        for name in ('translate.sh', 'doctor.sh', 'doctor.py', 'compat.py', 'workflow-common.sh', 'safe-output.py'):
            shutil.copy2(ROOT / 'scripts' / name, self.repo / 'scripts' / name)
        shutil.copy2(ROOT / 'lean-toolchain', self.repo / 'lean-toolchain')
        shutil.copy2(ROOT / 'compatibility.json', self.repo / 'compatibility.json')
        self.bin = self.base / 'fake tools'
        self.bin.mkdir()
        self.write_tool(self.bin / 'elan')
        self.write_tool(self.bin / 'stock-zig')
        self.patch = self.repo / 'zig-air-0.16.0/bin/zig'
        self.write_tool(self.patch)
        self.caller = self.base / 'caller with spaces'
        self.caller.mkdir()
        self.source = self.caller / 'source space.zig'
        self.source.write_text('export fn foo() u32 { return 1; }\n')
        self.output = self.caller / 'output space.lean'
        self.output.write_text('previous checked output\n')
        self.log = self.base / 'calls.jsonl'
        self.env = os.environ.copy()
        for key in ('AIR2LEAN_ZIG_VERSION', 'AIR2LEAN_ZIG_AIR', 'AIR2LEAN_ZIG'):
            self.env.pop(key, None)
        self.env.update(PATH=str(self.bin) + os.pathsep + self.env['PATH'],
                        MOCK_REPO=str(self.repo), MOCK_LOG=str(self.log),
                        AIR2LEAN_ZIG=str(self.bin / 'stock-zig'), TMPDIR=str(self.base),
                        AIR2LEAN_DOCKER=str(self.bin / 'no-docker'))

    def write_tool(self, path):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(FAKE)
        path.chmod(0o755)

    def run_script(self, script='translate.sh', args=None, mode='', expected=0):
        if args is None:
            args = [self.source.name, '-o', self.output.name, '--namespace', 'User.Program']
        result = subprocess.run([SHELL, str(self.repo / 'scripts' / script)] + args,
                                cwd=self.caller, env=dict(self.env, MOCK_MODE=mode),
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, expected, result.stdout)
        return result.stdout

    def events(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def test_space_paths_and_serial_stages(self):
        before = self.source.read_bytes()
        self.run_script()
        self.assertIn('fresh generated', self.output.read_text())
        self.assertEqual(self.source.read_bytes(), before)
        events = self.events()
        self.assertEqual([event[0] for event in events], ['elan', 'zig', 'elan', 'zig', 'air2lean', 'elan'])
        translator = events[-2][1]
        self.assertEqual(translator[translator.index('--prefix')+1], 'source space.')
        self.assertEqual(list(self.caller.glob('.air2lean-output.*')), [])
        self.assertEqual(list(self.base.glob('air2lean-translate.*')), [])

    def test_failures_preserve_input_and_output(self):
        for mode, hint in [('missing-lean', 'toolchain install'), ('wrong-version', 'expected'),
                           ('build-fail', 'Lean build failed'), ('export-fail', 'AIR export failed'),
                           ('empty-air', 'no fresh AIR'), ('partial-export', 'export was incomplete'),
                           ('translate-fail', 'translation failed'),
                           ('missing-output', 'did not write fresh Lean'), ('lean-fail', 'did not elaborate')]:
            with self.subTest(mode=mode):
                original = self.source.read_bytes(), self.output.read_bytes()
                self.assertIn(hint, self.run_script(mode=mode, expected=1))
                self.assertEqual(original, (self.source.read_bytes(), self.output.read_bytes()))
                self.assertEqual(list(self.caller.glob('.air2lean-output.*')), [])

    def test_fresh_air_on_each_run_and_empty_export_cannot_reuse_it(self):
        self.run_script()
        self.run_script()
        airs = [event[2] for event in self.events() if event[0] == 'zig' and event[1] != ['version']]
        self.assertEqual(len(set(airs)), 2)
        good_output = self.output.read_bytes()
        self.run_script(mode='empty-air', expected=1)
        self.assertEqual(self.output.read_bytes(), good_output)

    def test_relative_tmpdir_is_resolved_and_cleaned(self):
        self.env['TMPDIR'] = '.'
        self.run_script()
        export = [event for event in self.events() if event[0] == 'zig' and event[1] != ['version']][0]
        self.assertTrue(Path(export[2]).is_absolute())
        self.assertFalse(Path(export[2]).exists())
        self.assertEqual(list(self.caller.glob('air2lean-translate.*')), [])

    def test_invalid_float_mode_runs_no_tools(self):
        before = self.output.read_bytes()
        args = [self.source.name, '-o', self.output.name, '--namespace', 'User', '--float-semantics', 'iee']
        self.assertIn('invalid --float-semantics', self.run_script(args=args, expected=2))
        self.assertEqual(self.events(), [])
        self.assertEqual(self.output.read_bytes(), before)

    def test_fake_toolchain_follows_repository_pin(self):
        (self.repo / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        self.run_script()

    def test_flags_forwarded_and_relative_patched_path(self):
        relative = os.path.relpath(self.patch, self.caller)
        self.run_script(args=[self.source.name, '-o', self.output.name, '--namespace', 'Names',
                              '--zig-air', relative, '--prefix', 'custom.', '--filter', 'custom.,std.extra.',
                              '--float-semantics', 'compiler-rt'])
        translator = [event[1] for event in self.events() if event[0] == 'air2lean'][0]
        self.assertEqual(translator[-6:], ['--namespace', 'Names', '--prefix', 'custom.', '--float-semantics', 'compiler-rt'])
        export = [event for event in self.events() if event[0] == 'zig' and event[1] != ['version']][0]
        self.assertEqual(export[4], 'custom.,std.extra.')

    def test_output_path_guards(self):
        self.output.unlink()
        self.output.symlink_to(self.source)
        self.assertIn('no symlinks', self.run_script(expected=1))
        self.output.unlink()
        self.output.mkdir()
        self.assertIn('no symlinks', self.run_script(expected=1))
        self.output.rmdir()
        os.mkfifo(self.output)
        self.assertIn('regular file path', self.run_script(expected=1))
        self.assertEqual(self.events(), [])

    def test_input_hardlink_and_nonexistent_parent(self):
        self.output.unlink()
        os.link(self.source, self.output)
        self.assertIn('distinct', self.run_script(expected=1))
        self.assertIn('directory does not exist', self.run_script(args=[self.source.name, '-o', 'missing/Gen.lean',
                                                                      '--namespace', 'User'], expected=1))
        self.assertEqual(self.events(), [])

    def test_unknown_and_missing_options(self):
        for args, hint in [(['--typo'], 'unknown option'), (['--zig-air'], 'missing value'),
                           ([], 'required'), ([self.source.name, 'extra.zig'], 'unexpected argument')]:
            with self.subTest(args=args):
                self.assertIn(hint, self.run_script(args=args, expected=2))
        self.assertEqual(self.events(), [])

    def test_help_without_tools(self):
        (self.bin / 'elan').unlink()
        self.patch.unlink()
        for script in ('doctor.sh', 'translate.sh'):
            self.assertIn('Usage:', self.run_script(script, ['--help']))
        self.assertEqual(self.events(), [])

    def test_leading_hyphen_input(self):
        source = self.caller / '-source.zig'
        source.write_text(self.source.read_text())
        self.run_script(args=['-o', self.output.name, '--namespace', 'User', '--', source.name])

    def test_reject_unlocked_and_unsupported_versions(self):
        unlocked = self.patch.with_name('zig-unlocked')
        self.write_tool(unlocked)
        for extra, hint in [(['--zig-air', str(unlocked)], 'safety lock'),
                            (['--zig-version', 'latest'], 'unsupported Zig')]:
            args = [self.source.name, '-o', self.output.name, '--namespace', 'User'] + extra
            self.assertIn(hint, self.run_script(args=args, expected=1))
        self.assertEqual(self.events(), [])

    def test_doctor_ready_and_missing_optional_stock(self):
        self.assertIn('Ready:', self.run_script('doctor.sh', []))
        self.env['AIR2LEAN_ZIG'] = str(self.bin / 'no-stock-zig')
        result = self.run_script('doctor.sh', [])
        self.assertIn('stock Zig is missing', result)
        self.assertIn('Ready for committed proofs', result)
        self.assertFalse(any(event[0] == 'air2lean' for event in self.events()))

    def test_doctor_lean_ready_but_exporter_missing(self):
        self.patch.unlink()
        result = self.run_script('doctor.sh', [], expected=1)
        self.assertIn('Ready for committed proofs', result)
        self.assertIn('zig-patch/build.sh 0.16.0', result)

    def test_concurrent_pipeline_fails_without_stealing_lock(self):
        gate = self.base / 'release-gate'
        args = [SHELL, str(self.repo / 'scripts/translate.sh'), self.source.name,
                '-o', self.output.name, '--namespace', 'User']
        running = subprocess.Popen(args, cwd=self.caller,
                                   env=dict(self.env, MOCK_MODE='hold-build', MOCK_BUILD_GATE=str(gate)),
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 5
            while not gate.with_suffix('.ready').exists():
                if running.poll() is not None or time.monotonic() > deadline:
                    self.fail('mock first pipeline did not enter build')
                time.sleep(0.01)
            result = self.run_script(expected=1)
            self.assertIn('another translation owns', result)
            self.assertTrue((self.repo / '.lake/air2lean-translate.lock').is_dir())
            gate.touch()
            output, _ = running.communicate(timeout=5)
            self.assertEqual(running.returncode, 0, output)
            self.assertFalse((self.repo / '.lake/air2lean-translate.lock').exists())
        finally:
            gate.touch()
            if running.poll() is None:
                running.kill()
                running.communicate()

    def test_existing_lock_is_never_stolen(self):
        lock = self.repo / '.lake/air2lean-translate.lock'
        lock.mkdir(parents=True)
        self.assertIn('another translation owns', self.run_script(expected=1))
        self.assertTrue(lock.is_dir())
        self.assertEqual(self.output.read_text(), 'previous checked output\n')

    def test_failed_new_output_is_not_published(self):
        self.output.unlink()
        self.run_script(mode='lean-fail', expected=1)
        self.assertFalse(self.output.exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
