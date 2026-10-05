#!/usr/bin/env python3
"""Compiler-free tests for fixture isolation and CLI failure handling."""
import subprocess
import unittest
from unittest.mock import patch

from test_cli import proved_fields, run_cli


class CliHelpers(unittest.TestCase):
    def test_fresh_proved_fields(self):
        first, second = proved_fields(), proved_fields()
        first["errors"].append("panic")
        first["dependencies"].append("premise")
        self.assertEqual(second["errors"], [])
        self.assertEqual(second["dependencies"], [])
        self.assertEqual(proved_fields("tupleSelect", "tupleContract", "tupleEvidence")["proof"],
                         "RegistryExample.tupleEvidence")

    def test_normal_failure_and_uniform_runner(self):
        result = subprocess.CompletedProcess(["stub"], 1, "", "missing value for -o")
        with patch("test_cli.subprocess.run", return_value=result) as runner:
            self.assertIs(run_cli(["stub", "-o"], cwd="fixture", success=False,
                                  diagnostic="missing value for -o"), result)
            runner.assert_called_once_with(["stub", "-o"], cwd="fixture", capture_output=True,
                                           text=True, timeout=10)

    def test_crashes_and_missing_diagnostics_fail(self):
        for code, error in [(-11, "segmentation fault"), (2, "panic"), (0, ""),
                            (1, ""), (1, "unrelated error")]:
            with self.subTest(code=code, error=error):
                result = subprocess.CompletedProcess(["stub"], code, "", error)
                with patch("test_cli.subprocess.run", return_value=result):
                    with self.assertRaises(AssertionError):
                        run_cli(["stub"], success=False, diagnostic="expected failure")

    def test_timeout_propagates(self):
        with patch("test_cli.subprocess.run", side_effect=subprocess.TimeoutExpired(["stub"], 10)) as runner:
            with self.assertRaises(subprocess.TimeoutExpired):
                run_cli(["stub"], success=False)
            self.assertEqual(runner.call_args.kwargs["timeout"], 10)


if __name__ == "__main__":
    unittest.main()
