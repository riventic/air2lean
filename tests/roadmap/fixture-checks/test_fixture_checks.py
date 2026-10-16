"""scripts/fixture-checks.py: which CI checks it runs, and what a unit's pre-key names.

Discovery runs over the real workflow: every Python test a CI step runs (a tests/ script run by
python3, a `unittest discover -s tests/...`) and every proof-fixture check.sh is in a unit. A
unit is keyed by scripts/ci-reuse.py's traced records (tests/roadmap/ci-reuse/test_traced.py);
what the unit runs (its pre-key identity) names its step, its toolchains and the staging code.
"""
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("air2lean_fixture_checks", ROOT / "scripts/fixture-checks.py")
fc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fc)


class Discovery(unittest.TestCase):
    def test_python_test_commands_and_what_leaves_one_out(self):
        tree = fc.Tree()
        run = ("set -euo pipefail\n"
               "PYTHONDONTWRITEBYTECODE=1 python3 -B tests/roadmap/outcome-taxonomy/test_taxonomy.py\n"
               "python3 -m unittest discover -s tests/roadmap/coverage-report -p 'test_*.py' -v 2>&1 \\\n"
               "  | tee \"$RUNNER_TEMP/coverage.log\"\n"
               "python3 scripts/ci-reuse.py check-workflow\n"
               "python3 -I -B tests/roadmap/stable-generation/test_cli.py \"$PWD/.lake/build/bin/air2lean\"\n"
               "python3 tests/roadmap/asm-wrappers/audit.py --assurance \"$RUNNER_TEMP/assumptions.json\"\n")
        found = fc.python_tests(tree, run)
        self.assertEqual([test for _, test, _ in found], [
            "tests/roadmap/outcome-taxonomy/test_taxonomy.py", "tests/roadmap/coverage-report",
            "tests/roadmap/stable-generation/test_cli.py", "tests/roadmap/asm-wrappers/audit.py"])
        self.assertEqual([reason for _, _, reason in found][:3], [None, None, None])
        self.assertIn("$RUNNER_TEMP/assumptions.json", found[3][2])  # an earlier step's file: left out
        self.assertTrue(found[0][0].startswith("PYTHONDONTWRITEBYTECODE=1 python3"))
        self.assertNotIn("tee", found[1][0])
        self.assertIn(fc.WS + "/.lake/build/bin/air2lean", found[2][0])  # the step's directory: the workspace
        self.assertEqual(fc.proof_fixtures(tree, run + "tests/roadmap/noalias/check.sh\n"),
                         ["tests/roadmap/noalias/check.sh"])

    def test_every_python_test_ci_runs_is_a_unit_or_left_out_by_name(self):
        tree = fc.Tree()
        named = set()
        for job in (fc.CR.load_workflow(fc.ROOT).get("jobs") or {}).values():
            for step in job.get("steps") or []:
                run = str(step.get("run", ""))
                if not fc.proof_fixtures(tree, run):  # such a step runs whole, its tests included
                    named |= {test for _, test, _ in fc.python_tests(tree, run)}
        self.assertGreater(len(named), 80)
        self.assertEqual(named - {c for u in fc.discover(tree) for c in u["checks"]}, set())


class Identity(unittest.TestCase):
    unit = {"run": "tests/x/check.sh", "env": {"A": "1"}, "zig": "0.17.0",
            "toolchains": {"patched": ["0.17.0"], "stock": []}}

    def identity(self, unit=None, inputs="inputs"):
        fc._tool.cache_clear()
        with mock.patch.object(fc.CAS, "host_zig", return_value=Path("/zig/0.17.0/zig")), \
                mock.patch.object(fc.CAS, "zig_patch_inputs", return_value=inputs):
            return fc.identity(unit or self.unit)

    def test_the_step_the_toolchains_and_the_staging_code_are_named(self):
        self.addCleanup(fc._tool.cache_clear)
        identity = self.identity()
        self.assertEqual(identity["tools"], {"patched": {"0.17.0": ("/zig/0.17.0/zig", "inputs")}, "stock": {}})
        self.assertEqual(identity["path-zig"], "/zig/0.17.0/zig")
        for change in ({"run": "tests/y/check.sh"}, {"env": {"A": "2"}}):
            self.assertNotEqual(identity, self.identity(dict(self.unit, **change)))
        self.assertNotEqual(identity, self.identity(inputs="other"))
        with mock.patch.object(fc, "RUNNER", "another"):
            self.assertNotEqual(identity, self.identity())

    def test_the_runner_key_is_the_staging_code(self):
        text = (ROOT / "scripts/fixture-checks.py").read_text()
        region = text[text.index("# ---- key-relevant: begin"):text.index("# ---- key-relevant: end")]
        for name in ("def identity(", "def _stage(", "def staged_job("):
            self.assertIn(name, region)
        self.assertNotIn("def discover(", region)


if __name__ == "__main__":
    unittest.main()
