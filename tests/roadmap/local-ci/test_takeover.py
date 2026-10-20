#!/usr/bin/env python3
"""Startup and reproduction guidance controls; no toolchain builds or containers."""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from test_cache import runner

ROOT = Path(__file__).resolve().parents[3]
STEPS = ROOT / 'scripts/local-ci-steps.py'


class PythonStartup(unittest.TestCase):
    def startup(self, version):
        # Exercise the actual entry point with a simulated version. The installed
        # interpreter still parses the source; this does not qualify an older Python.
        code = (
            'import runpy,sys\n'
            'script=sys.argv[1]\n'
            f'sys.version_info={version!r}\n'
            'sys.argv=[script,"--snapshot"]\n'
            'runpy.run_path(script,run_name="__main__")\n'
        )
        with tempfile.TemporaryDirectory() as checkout:
            return subprocess.run([sys.executable, '-B', '-c', code, str(STEPS)],
                                  cwd=checkout, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                                  capture_output=True, text=True, timeout=30)

    def test_old_python_is_named_before_checkout_access(self):
        for version in ((3, 10, 0, 'final', 0), (3, 11, 99, 'final', 0)):
            with self.subTest(version=version):
                result = self.startup(version)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('local-ci: Python 3.12 or newer is required', result.stderr)
                self.assertIn('found ' + '.'.join(map(str, version[:3])), result.stderr)
                self.assertNotIn('Traceback', result.stderr)

    def test_python_312_reaches_the_actual_snapshot_usage_check(self):
        result = self.startup((3, 12, 0, 'final', 0))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('usage: local-ci-steps.py --snapshot SNAPSHOT ARTIFACTS MODE VERSION', result.stderr)
        self.assertNotIn('Python 3.12 or newer is required', result.stderr)
        self.assertNotIn('Traceback', result.stderr)


class ReproductionGuidance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('takeover_release_record', ROOT / 'scripts/release-record.py')
        cls.release = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.release)

    def test_macos_distinguishes_unrestricted_diagnostics_from_rejected_parts(self):
        text = self.release.NATIVE_JOBS['macos']
        self.assertIn('scripts/local-ci.sh discover macos/<version>', text)
        self.assertIn('unrestricted diagnostic', text)
        self.assertIn('scripts/local-ci.sh part macos/<version> is rejected', text)
        self.assertIn('scripts directly', text)
        self.assertIn('scripts/check.sh', text)
        self.assertIn('still require GitHub evidence', text)
        self.assertNotIn('runner only', text)

    def test_arm_names_the_local_native_engine_and_retains_the_evidence_boundary(self):
        for job in ('aarch64-linux', 'bitops-native-arm', 'build-modes-aarch64-linux'):
            with self.subTest(job=job):
                text = self.release.NATIVE_JOBS[job]
                self.assertIn('Native linux/arm64 Docker engine', text)
                self.assertIn('scripts/local-ci.sh part <job/part>', text)
                self.assertIn(job, text)
                self.assertIn('still require GitHub evidence', text)
                self.assertNotIn('runner only', text)


class QualifiedWorkflowSteps(unittest.TestCase):
    def test_actual_workflow_matches_every_qualified_setup_step(self):
        workflow = runner.TM.parse_workflow_yaml((ROOT / '.github/workflows/ci.yml').read_text())
        steps = workflow['jobs']['test']['steps']
        for name, expected in runner.QUALIFIED_TEST_SUBSTITUTIONS.items():
            with self.subTest(step=name):
                matches = [step for step in steps if step.get('name') == name]
                self.assertEqual(len(matches), 1, 'qualified setup must name one actual workflow step')
                self.assertEqual(runner.step_digest(matches[0]), expected,
                                 'changed setup body, guard, environment or action options need qualification')


if __name__ == '__main__':
    unittest.main()
