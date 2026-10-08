#!/usr/bin/env python3
"""I08 safe output/execution regressions. Every compiler, Lean and auditor command is a stub.

Each scenario asserts that a failed, interrupted or timed-out stage leaves the previously
published artifact byte-identical, publishes no partial file and leaves no live stage process.
"""
import importlib.util
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[3]
SHELL = os.environ.get('AIR2LEAN_TEST_BASH', 'bash')
PRIOR = b'-- previously checked artifact\n'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


safe = load('safe_output', ROOT / 'scripts/safe-output.py')

# One stub for elan, zig, lake and air2lean (selected by argv[0]); MOCK_MODE picks a behavior.
STUB = r'''#!/usr/bin/env python3
import os, pathlib, signal, subprocess, sys, time
kind = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
mode = os.environ.get('MOCK_MODE', 'ok')
pids = pathlib.Path(os.environ['MOCK_PIDS'])
ready = pathlib.Path(os.environ['MOCK_READY'])

def record(pid):
    with open(pids, 'a') as f:
        f.write(f'{pid}\n')

def hang(ignore_term=False):
    if ignore_term:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    record(os.getpid())
    ready.touch()
    while True:
        time.sleep(0.05)

def translate(out):
    out = pathlib.Path(out)
    if mode == 'partial-fail':
        out.write_text('-- partial generated prefix')
        sys.exit(1)
    if mode == 'partial-hang':
        out.write_text('-- partial generated prefix')
        hang()
    if mode == 'stubborn':
        child = subprocess.Popen([sys.executable, '-c', 'import signal, time\n'
                                  'signal.signal(signal.SIGTERM, signal.SIG_IGN)\n'
                                  'time.sleep(60)'])
        record(child.pid)
        out.write_text('-- partial generated prefix')
        hang(ignore_term=True)
    if mode == 'hang':
        hang()
    if mode.startswith('setsid'):
        # A new session is outside the stage's process group. 'scrubbed' also drops the stage's
        # environment marker; 'orphan' has the leader exit; 'double' forks through a short-lived parent.
        env = {} if 'scrubbed' in mode else None
        sleeper = 'import time; time.sleep(60)'
        if 'double' in mode:
            code = ('import os, subprocess, sys\n'
                    f'c = subprocess.Popen([sys.executable, "-c", {sleeper!r}], start_new_session=True)\n'
                    'print(c.pid)')
            child = subprocess.run([sys.executable, '-c', code], capture_output=True, text=True, env=env)
            record(int(child.stdout))
        else:
            record(subprocess.Popen([sys.executable, '-c', sleeper], start_new_session=True, env=env).pid)
        if 'orphan' in mode:
            time.sleep(1)
            sys.exit(0)
        hang()
    if mode == 'leave-child':
        child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
        record(child.pid)
    out.write_text('import ZigLean\n-- fresh generated output\n')

if kind == 'elan':
    toolchain = pathlib.Path(os.environ['MOCK_REPO'], 'lean-toolchain').read_text().strip()
    if args == ['toolchain', 'list']:
        print(toolchain + ' (default)')
        sys.exit(0)
    assert args[:3] == ['run', toolchain, 'lake'], args
    action = args[3:]
    if action == ['build', 'ZigLean', 'air2lean']:
        target = pathlib.Path(os.environ['MOCK_REPO'], '.lake/build/bin/air2lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(pathlib.Path(__file__).read_text())
        target.chmod(0o755)
    else:
        assert action[:2] == ['env', 'lean'], action
        if mode == 'lean-hang':
            hang()
        if mode == 'lean-fail':
            sys.exit(1)
elif kind == 'zig':
    if args == ['version']:
        print('0.16.0')
    else:
        pathlib.Path(os.environ['ZIG_AIR_JSON_DIR'], 'demo.foo.json').write_text('{}')
elif kind == 'air2lean':
    translate(args[args.index('-o') + 1])
elif kind == 'lake' and args[:1] == ['build']:
    if mode == 'build-hang':
        hang()
elif kind == 'normalize-generated.py':
    pathlib.Path(args[-1]).write_text('{}')
elif kind == 'normalize-air.py':
    pass
elif kind == 'diff.sh':
    if mode == 'diff-hang':
        hang()
elif kind == 'lake':
    assert args[:2] == ['exe', 'air2lean'], args
    translate(args[args.index('-o') + 1])
else:
    raise AssertionError(kind)
'''


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    try:  # A zombie is not a live writer; reap it if it is ours.
        return os.waitpid(pid, os.WNOHANG) == (0, 0)
    except ChildProcessError:
        return True


class Stubbed(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean safe output ')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        self.pids = self.base / 'pids'
        self.ready = self.base / 'ready'
        self.bin = self.base / 'bin'
        self.bin.mkdir()
        self.env = os.environ.copy()
        for key in ('AIR2LEAN_ZIG_VERSION', 'AIR2LEAN_ZIG_AIR', 'AIR2LEAN_STAGE_TIMEOUT', 'AIR2LEAN_CI',
                    'AIR2LEAN_OUT_DIR', 'AIR2LEAN_CHECK_REPORT_DIR'):
            self.env.pop(key, None)
        self.env.update(PATH=str(self.bin) + os.pathsep + self.env['PATH'], MOCK_PIDS=str(self.pids),
                        MOCK_READY=str(self.ready), TMPDIR=str(self.base))
        self.addCleanup(self.reap)

    def stub(self, path):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(STUB)
        path.chmod(0o755)

    def recorded(self):
        return [int(line) for line in self.pids.read_text().split()] if self.pids.exists() else []

    def reap(self):
        for pid in self.recorded():
            try:
                os.kill(pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass

    def assert_stopped(self):
        pids = self.recorded()
        self.assertTrue(pids, 'the stub never recorded a stage process')
        deadline = time.monotonic() + 3
        while any(alive(pid) for pid in pids) and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertEqual([pid for pid in pids if alive(pid)], [], 'stage processes survived')

    def start(self, argv, cwd, mode):
        self.ready.unlink(missing_ok=True)
        return subprocess.Popen(argv, cwd=cwd, env=dict(self.env, MOCK_MODE=mode),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def interrupt(self, process, signum):
        deadline = time.monotonic() + 20
        while not self.ready.exists():
            self.assertIsNone(process.poll(), process.stdout.read().decode() if process.poll() is not None else '')
            self.assertLess(time.monotonic(), deadline, 'stage never became ready')
            time.sleep(0.02)
        process.send_signal(signum)
        output, _ = process.communicate(timeout=20)
        return process.returncode, output.decode()

    def finish(self, process):
        output, _ = process.communicate(timeout=30)
        return process.returncode, output.decode()


class Publish(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.dir = Path(self.temp.name)
        self.staged = self.dir / 'staged.lean'
        self.staged.write_bytes(b'-- new checked artifact\n')
        self.dest = self.dir / 'out' / 'Gen.lean'
        self.dest.parent.mkdir()
        self.dest.write_bytes(PRIOR)
        self.dest.chmod(0o640)

    def leftovers(self):
        return [p.name for p in self.dest.parent.iterdir() if p.name != 'Gen.lean']

    def test_overwrite_replaces_atomically_and_keeps_mode(self):
        safe.publish(self.staged, self.dest, overwrite=True)
        self.assertEqual(self.dest.read_bytes(), b'-- new checked artifact\n')
        self.assertEqual(self.dest.stat().st_mode & 0o777, 0o640)
        self.assertEqual(self.leftovers(), [])

    def test_no_clobber_refuses_existing_and_publishes_fresh(self):
        with self.assertRaises(safe.Refused):
            safe.publish(self.staged, self.dest, overwrite=False)
        self.assertEqual(self.dest.read_bytes(), PRIOR)
        fresh = self.dest.parent / 'Fresh.lean'
        safe.publish(self.staged, fresh, overwrite=False)
        self.assertEqual(fresh.read_bytes(), b'-- new checked artifact\n')
        self.assertEqual(sorted(self.leftovers()), ['Fresh.lean'])

    def test_interrupt_mid_write_keeps_prior_and_no_partial(self):
        real = os.fsync
        def interrupted(fd):
            raise KeyboardInterrupt
        os.fsync = interrupted
        try:
            with self.assertRaises(KeyboardInterrupt):
                safe.publish(self.staged, self.dest, overwrite=True)
        finally:
            os.fsync = real
        self.assertEqual(self.dest.read_bytes(), PRIOR)
        self.assertEqual(self.leftovers(), [])

    def test_rejects_symlink_and_directory_destinations_and_missing_policy(self):
        link = self.dest.parent / 'Link.lean'
        link.symlink_to(self.dest)
        with self.assertRaises(safe.Refused):
            safe.publish(self.staged, link, overwrite=True)
        with self.assertRaises(safe.Refused):
            safe.publish(self.staged, self.dest.parent, overwrite=True)
        self.assertEqual(self.dest.read_bytes(), PRIOR)
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/safe-output.py'), 'publish',
                                 str(self.staged), str(self.dest)], stderr=subprocess.PIPE)
        self.assertEqual(result.returncode, 2)  # Overwrite policy must be explicit.
        self.assertEqual(self.dest.read_bytes(), PRIOR)


class Runner(Stubbed):
    def run_stub(self, mode, *options):
        tool = self.bin / 'air2lean'
        self.stub(tool)
        out = self.base / 'Gen.lean'
        argv = [sys.executable, str(ROOT / 'scripts/safe-output.py'), 'run', '--grace', '0.5', *options,
                '--', str(tool), 'air', '-o', str(out)]
        return self.start(argv, self.base, mode)

    def test_exit_status_passthrough(self):
        self.assertEqual(self.finish(self.run_stub('partial-fail'))[0], 1)
        self.assertEqual(self.finish(self.run_stub('ok'))[0], 0)

    def test_timeout_stops_group(self):
        started = time.monotonic()
        code, output = self.finish(self.run_stub('stubborn', '--timeout', '1'))
        self.assertEqual(code, safe.TIMEOUT, output)
        self.assertIn('timeout', output)
        self.assertLess(time.monotonic() - started, 10)
        self.assert_stopped()

    def test_sigterm_stops_term_ignoring_child_and_grandchild(self):
        code, output = self.interrupt(self.run_stub('stubborn'), signal.SIGTERM)
        self.assertEqual(code, 128 + signal.SIGTERM, output)
        self.assert_stopped()

    def test_leader_exit_with_live_descendant_fails(self):
        code, output = self.finish(self.run_stub('leave-child'))
        self.assertEqual(code, safe.DESCENDANTS, output)
        self.assert_stopped()


def marker_visible():
    """Whether this host's ps shows other processes' environments (the marker scan needs it)."""
    probe = subprocess.Popen(['sleep', '5'], env={safe.MARKER: 'probe'})
    try:
        time.sleep(0.2)
        return any('probe' in row[2] for row in safe._processes().values() if safe.MARKER in row[2])
    finally:
        probe.kill()
        probe.wait()


class Escape(Stubbed):
    """Descendants that leave the stage's process group with setsid are found and stopped."""

    run_stub = Runner.run_stub

    def cancel(self, mode, signum=signal.SIGTERM):
        code, output = self.interrupt(self.run_stub(mode), signum)
        self.assertEqual(code, 128 + signum, output)
        self.assertEqual(len(self.recorded()), 2)
        self.assert_stopped()

    def test_setsid_child_stopped_on_cancel(self):
        self.cancel('setsid')

    def test_setsid_child_with_scrubbed_environment_stopped_on_cancel(self):
        process = self.run_stub('setsid-scrubbed')
        deadline = time.monotonic() + 20
        while not self.ready.exists():
            self.assertLess(time.monotonic(), deadline)
            time.sleep(0.02)
        time.sleep(1)  # The parent link is the only trace: let a process-table sample see it.
        process.send_signal(signal.SIGTERM)
        process.communicate(timeout=20)
        self.assertEqual(process.returncode, 128 + signal.SIGTERM)
        self.assert_stopped()

    def test_setsid_child_stopped_on_timeout(self):
        code, output = self.finish(self.run_stub('setsid', '--timeout', '1'))
        self.assertEqual(code, safe.TIMEOUT, output)
        self.assert_stopped()

    def test_setsid_child_orphaned_by_leader_exit_fails_the_stage(self):
        code, output = self.finish(self.run_stub('setsid-scrubbed-orphan'))
        self.assertEqual(code, safe.DESCENDANTS, output)
        self.assert_stopped()

    @unittest.skipUnless(marker_visible(), 'ps does not show process environments on this host')
    def test_double_forked_setsid_child_found_by_marker(self):
        code, output = self.finish(self.run_stub('setsid-double-orphan'))
        self.assertEqual(code, safe.DESCENDANTS, output)
        self.assert_stopped()

    def test_marker_and_parent_links_in_a_process_table(self):
        class Leader:
            pid, returncode = 10, None
        t = 'Thu Oct  8 12:00:00 2026'
        table = {10: (1, t, 'leader'), 11: (10, t, 'child'), 12: (1, t, 'orphan'),
                 13: (12, t, 'grandchild'), 14: (1, t, f'sleep 60 HOME=/ {safe.MARKER}=tok'),
                 15: (1, t, f'sleep 60 {safe.MARKER}=other'), 16: (1, t, 'unrelated')}
        escapees = safe.Escapees(Leader, 'tok')
        original = safe._processes
        try:
            safe._processes = lambda: table
            self.assertEqual(sorted(escapees.scan()), [11, 14])
            table[12] = (11, t, 'orphan')  # Reached through an owned parent only later.
            self.assertEqual(sorted(escapees.scan()), [11, 12, 13, 14])
            table[11] = (1, 'Fri Oct  9 12:00:00 2026', 'reused pid')  # Same pid, other process.
            self.assertEqual(sorted(escapees.scan()), [12, 13, 14])
        finally:
            safe._processes = original

    def test_clean_stage_is_not_slowed_or_failed(self):
        started = time.monotonic()
        self.assertEqual(self.finish(self.run_stub('ok'))[0], 0)
        self.assertLess(time.monotonic() - started, 5)


class Translate(Stubbed):
    def setUp(self):
        super().setUp()
        self.repo = self.base / 'repo'
        (self.repo / 'scripts').mkdir(parents=True)
        for name in ('translate.sh', 'workflow-common.sh', 'safe-output.py'):
            shutil.copy2(ROOT / 'scripts' / name, self.repo / 'scripts' / name)
        shutil.copy2(ROOT / 'lean-toolchain', self.repo / 'lean-toolchain')
        self.stub(self.bin / 'elan')
        self.stub(self.repo / 'zig-air-0.16.0/bin/zig')
        self.env['MOCK_REPO'] = str(self.repo)
        self.caller = self.base / 'caller'
        self.caller.mkdir()
        (self.caller / 'demo.zig').write_text('export fn foo() u32 { return 1; }\n')
        self.output = self.caller / 'Demo.lean'
        self.output.write_bytes(PRIOR)

    def translate(self, mode, *options):
        argv = [SHELL, str(self.repo / 'scripts/translate.sh'), 'demo.zig', '-o', self.output.name,
                '--namespace', 'Demo', *options]
        return self.start(argv, self.caller, mode)

    def assert_prior_intact(self):
        self.assertEqual(self.output.read_bytes(), PRIOR)
        self.assertEqual(sorted(p.name for p in self.caller.iterdir()), ['Demo.lean', 'demo.zig'])
        self.assertEqual(list(self.base.glob('air2lean-translate.*')), [])
        self.assertFalse((self.repo / '.lake/air2lean-translate.lock').exists())

    def test_failing_translator_with_partial_output(self):
        code, output = self.finish(self.translate('partial-fail'))
        self.assertEqual(code, 1, output)
        self.assertIn('translation failed', output)
        self.assert_prior_intact()

    def test_interrupt_mid_write(self):
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=signum):
                code, output = self.interrupt(self.translate('partial-hang'), signum)
                self.assertEqual(code, 128 + signum, output)
                self.assert_stopped()
                self.assert_prior_intact()

    def test_live_child_after_sigterm(self):
        code, output = self.interrupt(self.translate('stubborn'), signal.SIGTERM)
        self.assertEqual(code, 143, output)
        self.assertEqual(len(self.recorded()), 2)
        self.assert_stopped()
        self.assert_prior_intact()

    def test_interrupted_lean_check(self):
        code, output = self.interrupt(self.translate('lean-hang'), signal.SIGTERM)
        self.assertEqual(code, 143, output)
        self.assert_stopped()
        self.assert_prior_intact()

    def test_timeout(self):
        code, output = self.finish(self.translate('stubborn', '--timeout', '1'))
        self.assertEqual(code, 1, output)
        self.assertIn('timeout', output)
        self.assert_stopped()
        self.assert_prior_intact()

    def test_translator_leaving_child_is_not_published(self):
        code, output = self.finish(self.translate('leave-child'))
        self.assertEqual(code, 1, output)
        self.assertIn('live child processes', output)
        self.assert_stopped()
        self.assert_prior_intact()

    def test_overwrite_policy(self):
        code, output = self.finish(self.translate('ok', '--no-clobber'))
        self.assertEqual(code, 1, output)
        self.assertIn('--no-clobber', output)
        self.assertFalse((self.repo / '.lake').exists(), 'no stage may run before the refusal')
        self.assert_prior_intact()
        self.output.unlink()
        self.assertEqual(self.finish(self.translate('ok', '--no-clobber'))[0], 0)
        self.assertIn(b'fresh generated output', self.output.read_bytes())
        self.output.write_bytes(PRIOR)
        self.assertEqual(self.finish(self.translate('ok', '--overwrite'))[0], 0)
        self.assertIn(b'fresh generated output', self.output.read_bytes())
        self.assertEqual(self.finish(self.translate('ok', '--timeout', 'soon'))[0], 2)


class Check(Stubbed):
    def setUp(self):
        super().setUp()
        self.repo = self.base / 'repo'
        (self.repo / 'scripts').mkdir(parents=True)
        for name in ('check.sh', 'workflow-common.sh', 'safe-output.py'):
            shutil.copy2(ROOT / 'scripts' / name, self.repo / 'scripts' / name)
        (self.repo / 'examples/demo').mkdir(parents=True)
        (self.repo / 'examples/demo/demo.zig').write_text('export fn foo() u32 { return 1; }\n')
        self.gen = self.repo / 'Proofs/Demo/Gen.lean'
        self.gen.parent.mkdir(parents=True)
        self.gen.write_bytes(PRIOR)
        self.reports = self.base / 'reports'
        self.stub(self.bin / 'zig')
        self.stub(self.bin / 'lake')
        self.env.update(AIR2LEAN_ZIG_AIR=str(self.bin / 'zig'), AIR2LEAN_EXAMPLES='demo', AIR2LEAN_DIFF='0',
                        AIR2LEAN_CHECK_REPORT_DIR=str(self.reports))

    def check(self, mode):
        return self.start([SHELL, str(self.repo / 'scripts/check.sh')], self.repo, mode)

    def assert_prior_intact(self):
        self.assertEqual(self.gen.read_bytes(), PRIOR)
        self.assertEqual([p.name for p in self.gen.parent.iterdir()], ['Gen.lean'])
        self.assertFalse(self.reports.exists() and any(self.reports.iterdir()))
        self.assertEqual(list(self.base.glob('air2lean-check.*')), [])

    def test_failing_translator_with_partial_output(self):
        code, output = self.finish(self.check('partial-fail'))
        self.assertEqual(code, 1, output)
        self.assert_prior_intact()

    def test_interrupt_mid_write(self):
        for signum in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=signum):
                code, output = self.interrupt(self.check('partial-hang'), signum)
                self.assertEqual(code, 128 + signum, output)
                self.assert_stopped()
                self.assert_prior_intact()

    def test_live_child_after_sigterm(self):
        code, output = self.interrupt(self.check('stubborn'), signal.SIGTERM)
        self.assertEqual(code, 143, output)
        self.assertEqual(len(self.recorded()), 2)
        self.assert_stopped()
        self.assert_prior_intact()

    def test_timeout(self):
        self.env['AIR2LEAN_STAGE_TIMEOUT'] = '1'
        code, output = self.finish(self.check('stubborn'))
        self.assertEqual(code, safe.TIMEOUT, output)
        self.assertIn('timeout', output)
        self.assert_stopped()
        self.assert_prior_intact()


class FinalStages(Check):
    """check.sh's final lake build and differential test are bounded and cancellable."""

    def setUp(self):
        super().setUp()
        self.env.pop('AIR2LEAN_DIFF')
        for name in ('diff.sh', 'normalize-generated.py', 'normalize-air.py'):
            self.stub(self.repo / 'scripts' / name)
        self.generated = b'import ZigLean\n-- fresh generated output\n'

    def assert_gen_complete(self):
        # Gen.lean is published before the build; it is never a prefix, and nothing else is left.
        self.assertEqual(self.gen.read_bytes(), self.generated)
        self.assertEqual([p.name for p in self.gen.parent.iterdir()], ['Gen.lean'])

    def test_build_timeout(self):
        self.env['AIR2LEAN_STAGE_TIMEOUT'] = '1'
        code, output = self.finish(self.check('build-hang'))
        self.assertEqual(code, safe.TIMEOUT, output)
        self.assertIn('timeout', output)
        self.assert_stopped()
        self.assert_gen_complete()

    def test_build_interrupt(self):
        code, output = self.interrupt(self.check('build-hang'), signal.SIGINT)
        self.assertEqual(code, 130, output)
        self.assert_stopped()
        self.assert_gen_complete()

    def test_diff_timeout_and_interrupt(self):
        self.env['AIR2LEAN_STAGE_TIMEOUT'] = '1'
        code, output = self.finish(self.check('diff-hang'))
        self.assertEqual(code, safe.TIMEOUT, output)
        self.assert_stopped()
        self.env['AIR2LEAN_STAGE_TIMEOUT'] = '0'
        code, output = self.interrupt(self.check('diff-hang'), signal.SIGTERM)
        self.assertEqual(code, 143, output)
        self.assert_stopped()
        self.assert_gen_complete()

    def test_diff_status_is_the_exit_status(self):
        self.assertEqual(self.finish(self.check('ok'))[0], 0)


class ProofReceipt(Stubbed):
    def setUp(self):
        super().setUp()
        self.receipts = load('proof_receipt', ROOT / 'scripts/proof-receipt.py')

    def test_interrupted_receipt_write_publishes_nothing_and_never_clobbers(self):
        path = self.base / 'receipt.json'
        real = os.fsync
        def interrupted(fd):
            raise KeyboardInterrupt
        os.fsync = interrupted
        try:
            with self.assertRaises(KeyboardInterrupt):
                self.receipts.write_new(path, {'status': 'audited'})
        finally:
            os.fsync = real
        self.assertEqual(sorted(p.name for p in self.base.iterdir()), ['bin'])
        self.receipts.write_new(path, {'status': 'audited'})
        original = path.read_bytes()
        with self.assertRaises(FileExistsError):
            self.receipts.write_new(path, {'status': 'other'})
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(sorted(p.name for p in self.base.iterdir()), ['bin', 'receipt.json'])

    def worker(self, mode):
        tool = self.bin / 'air2lean'
        self.stub(tool)
        program = ('import importlib.util, sys\n'
                   'spec = importlib.util.spec_from_file_location("r", sys.argv[1])\n'
                   'r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)\n'
                   'try:\n'
                   '    sys.exit(r.run_child([sys.argv[2], "air", "-o", sys.argv[3]], sys.argv[4], grace=0.5).returncode)\n'
                   'except KeyboardInterrupt:\n'
                   '    sys.exit(130)\n'
                   'except ValueError as error:\n'
                   '    print(error); sys.exit(2)\n')
        return self.start([sys.executable, '-c', program, str(ROOT / 'scripts/proof-receipt.py'), str(tool),
                           str(self.base / 'audit.json'), str(self.base)], self.base, mode)

    def test_cancelled_auditor_group_is_stopped(self):
        code, output = self.interrupt(self.worker('stubborn'), signal.SIGTERM)
        self.assertEqual(code, 130, output)
        self.assertEqual(len(self.recorded()), 2)
        self.assert_stopped()

    def test_auditor_leaving_child_fails(self):
        code, output = self.finish(self.worker('leave-child'))
        self.assertEqual(code, 2, output)
        self.assertIn('live child processes', output)
        self.assert_stopped()


if __name__ == '__main__':
    unittest.main(verbosity=2)
