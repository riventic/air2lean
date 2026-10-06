"""Portable tests; every subprocess and POSIX exit observation is a controlled fake."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import tempfile
import unittest
from unittest.mock import patch, call

SPEC = importlib.util.spec_from_file_location("deadline_recipe", Path(__file__).with_name("root-runtime.py"))
recipe = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(recipe)
REQUIRE_SUPERVISION = recipe.require_supervision
EXIT_OBSERVATION = recipe.exited_without_reaping


class Process:
    pid = 123

    def __init__(self, code=0):
        self.code = code
        self.returncode = None
        self.waits = []

    def wait(self, timeout=None):
        self.waits.append(timeout)
        self.returncode = self.code
        return self.code


class RuntimeRecipeTests(unittest.TestCase):
    def setUp(self):
        # These portable tests do not claim native waitid or process-group conformance.
        self.capability = patch.object(recipe, "require_supervision")
        self.capability.start()
        self.observation = patch.object(recipe, "exited_without_reaping", return_value=True)
        self.observation.start()
        self.addCleanup(self.capability.stop)
        self.addCleanup(self.observation.stop)

    def receipt(self, directory, process_factory):
        argv = ["root-runtime.py", "--execute", "--artifacts", directory]
        with patch("sys.argv", argv), patch.dict(os.environ, {"AIR2LEAN_ROOT_LANE": "1"}):
            with patch.object(recipe.subprocess, "Popen", side_effect=process_factory), patch.object(recipe.os, "killpg"), patch.object(recipe.time, "sleep"), contextlib.redirect_stdout(io.StringIO()):
                code = recipe.main()
        report = json.loads(next(Path(directory).glob("deadline-runtime-*/report.json")).read_text())
        return code, report

    def test_plan_never_invokes_a_toolchain(self):
        output = io.StringIO()
        with patch("sys.argv", ["root-runtime.py"]), patch.object(recipe.subprocess, "Popen") as process:
            with contextlib.redirect_stdout(output):
                self.assertEqual(recipe.main(), 0)
        process.assert_not_called()
        plan = json.loads(output.getvalue())
        self.assertEqual(plan["status"], "prepared")
        self.assertIn("unsupported", plan["source_adapter"])
        self.assertEqual([name for name, _ in plan["commands"]],
                         ["build-time", "build-timed-scheduler", "kernel", "runtime"])
        for _, command in plan["commands"]:
            self.assertNotIn("version", command)
            self.assertNotIn("--version", command)

    def test_execution_requires_root_lane(self):
        with patch("sys.argv", ["root-runtime.py", "--execute"]), patch.dict(os.environ, {}, clear=True):
            with patch.object(recipe.subprocess, "Popen") as process, contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as rejected:
                    recipe.main()
        self.assertEqual(rejected.exception.code, 2)
        process.assert_not_called()

    def test_invalid_timeout_rejected_before_execution(self):
        with patch("sys.argv", ["root-runtime.py", "--timeout", "0"]):
            with patch.object(recipe.subprocess, "Popen") as process, contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as rejected:
                    recipe.main()
        self.assertEqual(rejected.exception.code, 2)
        process.assert_not_called()

    def test_overflowing_timeout_cannot_start_a_process(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen") as process:
                with self.assertRaises(OverflowError):
                    recipe.run_command(["fake"], directory, Path(directory) / "log", 10 ** 310)
        process.assert_not_called()

    def test_timeout_kills_group_before_reaping(self):
        process = Process(-9)
        anchored = []
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen", return_value=process), patch.object(recipe.time, "monotonic", side_effect=[0, 4]), patch.object(recipe.time, "sleep"):
                with patch.object(recipe.os, "killpg", side_effect=lambda *_: anchored.append(process.returncode is None)) as kill:
                    self.assertEqual(recipe.run_command(["fake"], directory, Path(directory) / "log", 4), (-9, True, []))
        self.assertEqual(kill.call_args_list, [call(123, signal.SIGTERM), call(123, signal.SIGKILL)])
        self.assertEqual(process.waits, [2])
        self.assertEqual(anchored, [True, True])

    def test_waitid_observation_is_non_reaping(self):
        process = Process()
        fake_info = type("ExitInfo", (), {"si_pid": 123})()
        with contextlib.ExitStack() as patches:
            for name, value in (("P_PID", 1), ("WEXITED", 2), ("WNOWAIT", 4), ("WNOHANG", 8)):
                patches.enter_context(patch.object(recipe.os, name, value, create=True))
            waitid = patches.enter_context(patch.object(recipe.os, "waitid", return_value=fake_info, create=True))
            self.assertTrue(EXIT_OBSERVATION(process))
            waitid.assert_called_once_with(1, 123, 14)
        self.assertIsNone(process.returncode)
        self.assertEqual(process.waits, [])

    def test_interrupt_after_failed_timeout_reap_does_not_repeat_cleanup(self):
        process = Process()
        interrupts = []
        def failed_reap(timeout):
            interrupts.append(signal.SIGTERM)
            raise recipe.subprocess.TimeoutExpired("fake", timeout)
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen", return_value=process), patch.object(process, "wait", side_effect=failed_reap) as wait, patch.object(recipe.time, "monotonic", side_effect=[0, 4]), patch.object(recipe.time, "sleep"), patch.object(recipe.os, "killpg") as kill:
                with self.assertRaises(recipe.RecipeInterrupted) as interrupted:
                    recipe.run_command(["fake"], directory, Path(directory) / "log", 4, interrupts)
        self.assertEqual(interrupted.exception.signum, signal.SIGTERM)
        self.assertEqual(len(interrupted.exception.cleanup_errors), 1)
        self.assertEqual(kill.call_args_list, [call(123, signal.SIGTERM), call(123, signal.SIGKILL)])
        wait.assert_called_once_with(timeout=2)

    def test_failed_command_is_not_a_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen", return_value=Process(1)), patch.object(recipe.os, "killpg"), patch.object(recipe.time, "sleep"):
                self.assertEqual(recipe.run_command(["fake"], directory, Path(directory) / "log", 4), (1, False, []))

    def test_signal_during_normal_reap_follows_group_cleanup(self):
        process = Process()
        interrupts = []
        anchored = []
        def reap(timeout):
            process.waits.append(timeout)
            interrupts.append(signal.SIGTERM)
            process.returncode = 0
            return 0
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen", return_value=process), patch.object(process, "wait", side_effect=reap), patch.object(recipe.time, "sleep") as sleep:
                with patch.object(recipe.os, "killpg", side_effect=lambda *_: anchored.append(process.returncode is None)) as kill:
                    with self.assertRaises(recipe.RecipeInterrupted) as interrupted:
                        recipe.run_command(["fake"], directory, Path(directory) / "log", 4, interrupts)
        self.assertEqual(interrupted.exception.signum, signal.SIGTERM)
        self.assertEqual(kill.call_args_list, [call(123, signal.SIGTERM), call(123, signal.SIGKILL)])
        self.assertEqual(anchored, [True, True])
        self.assertEqual(process.waits, [2])
        sleep.assert_called_once_with(0)

    def test_transitive_imports_are_retained(self):
        files = recipe.qualification_files(recipe.ROOT)
        self.assertIn("ZigLean/Mem/Enc.lean", files)
        self.assertIn("ZigLean/Packed.lean", files)

    def test_unsupported_waitid_rejected_before_launch(self):
        with patch.object(recipe.os, "waitid", None, create=True), patch.object(recipe.subprocess, "Popen") as process:
            with self.assertRaisesRegex(RuntimeError, "non-reaping waitid"):
                REQUIRE_SUPERVISION()
        process.assert_not_called()

    def test_failed_reap_is_bounded_and_recorded(self):
        process = Process()
        with patch.object(process, "wait", side_effect=recipe.subprocess.TimeoutExpired("fake", 2)) as wait:
            with patch.object(recipe.os, "killpg"), patch.object(recipe.time, "sleep"):
                code, errors = recipe.cleanup_process_group(process)
        self.assertIsNone(code)
        wait.assert_called_once_with(timeout=2)
        self.assertEqual(len(errors), 1)

    def test_startup_failure_retains_terminal_step_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            def missing(*_args, **_kwargs):
                raise FileNotFoundError("fake missing compiler")
            code, report = self.receipt(directory, missing)
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["steps"][0]["status"], "failed_to_start")
        self.assertIn("elapsed_seconds", report["steps"][0])
        self.assertIn("fake missing compiler", report["steps"][0]["error"])

    def test_successful_exit_with_cleanup_error_is_not_a_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe, "cleanup_process_group", return_value=(0, ["fake denied cleanup"])):
                code, report = self.receipt(directory, lambda *_args, **_kwargs: Process())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["steps"][0]["status"], "failed_cleanup")
        self.assertEqual(report["steps"][0]["cleanup_errors"], ["fake denied cleanup"])

    def test_constructor_signal_is_recorded_until_process_is_owned(self):
        process = Process(-9)
        previous = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
        with tempfile.TemporaryDirectory() as directory:
            def interrupted_creation(*_args, **_kwargs):
                signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)
                return process
            code, report = self.receipt(directory, interrupted_creation)
        self.assertEqual(code, 143)
        self.assertEqual(report["status"], "interrupted")
        self.assertEqual(report["steps"][0]["status"], "interrupted")
        self.assertEqual(process.waits, [2])
        self.assertEqual({sig: signal.getsignal(sig) for sig in previous}, previous)

    def test_wait_observation_does_not_reap_before_interruption_cleanup(self):
        process = Process(-9)
        interrupts = []
        anchored = []
        def observe(_process):
            interrupts.append(signal.SIGINT)
            return True
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(recipe.subprocess, "Popen", return_value=process), patch.object(recipe, "exited_without_reaping", side_effect=observe), patch.object(recipe.time, "sleep"):
                with patch.object(recipe.os, "killpg", side_effect=lambda *_: anchored.append(process.returncode is None)):
                    with self.assertRaises(recipe.RecipeInterrupted):
                        recipe.run_command(["fake"], directory, Path(directory) / "log", 4, interrupts)
        self.assertEqual(process.waits, [2])
        self.assertEqual(anchored, [True, True])

    def test_cleanup_entry_signals_cannot_bypass_group_kill(self):
        process = Process(-9)
        interrupts = []
        def record(signum, _frame):
            interrupts.append(signum)
        handlers = recipe.install_handlers(record)
        try:
            with patch.object(recipe.os, "killpg", side_effect=lambda _pid, _sig: signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)) as kill, patch.object(recipe.time, "sleep"):
                code, errors = recipe.cleanup_process_group(process)
        finally:
            recipe.restore_handlers(handlers)
        self.assertEqual(code, -9)
        self.assertEqual(errors, [])
        self.assertEqual(kill.call_args_list, [call(123, signal.SIGTERM), call(123, signal.SIGKILL)])
        self.assertEqual(process.waits, [2])
        self.assertEqual(interrupts, [signal.SIGTERM, signal.SIGTERM])

    def test_repeated_cleanup_signals_preserve_first_reason(self):
        process = Process(-9)
        interrupts = [signal.SIGTERM]
        def record(signum, _frame):
            interrupts.append(signum)
        def deliver(_grace):
            signal.getsignal(signal.SIGINT)(signal.SIGINT, None)
            signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)
        handlers = recipe.install_handlers(record)
        try:
            with tempfile.TemporaryDirectory() as directory:
                with patch.object(recipe.subprocess, "Popen", return_value=process), patch.object(recipe.os, "killpg"), patch.object(recipe.time, "sleep", side_effect=deliver):
                    # First request arrives during creation, before the first wait.
                    interrupts.clear()
                    def creation(*_args, **_kwargs):
                        interrupts.append(signal.SIGTERM)
                        return process
                    with patch.object(recipe.subprocess, "Popen", side_effect=creation):
                        with self.assertRaises(recipe.RecipeInterrupted) as interrupted:
                            recipe.run_command(["fake"], directory, Path(directory) / "log", 4, interrupts)
        finally:
            recipe.restore_handlers(handlers)
        self.assertEqual(interrupted.exception.signum, signal.SIGTERM)
        self.assertEqual(process.waits, [2])
        self.assertEqual(interrupts, [signal.SIGTERM, signal.SIGINT, signal.SIGTERM])


if __name__ == "__main__":
    unittest.main()
