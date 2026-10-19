"""scripts/fixture-checks.py: which CI checks it runs.

Discovery runs over the real workflow: every Python test a CI step runs (a tests/ script run by
python3, a `unittest discover -s tests/...`) and every proof-fixture check.sh is in a unit.
"""
import importlib.util
from pathlib import Path
import sys
import unittest

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
        # A test after an operator runs where the line put it: left out by name, never dropped.
        after = fc.python_tests(tree, "cd tests && python3 tests/roadmap/outcome-taxonomy/test_taxonomy.py\n")
        self.assertEqual([(test, reason) for _, test, reason in after],
                         [("tests/roadmap/outcome-taxonomy/test_taxonomy.py", "follows `&&` in its line")])
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

    def test_a_unit_after_a_heavy_regeneration_in_its_job_is_left_out(self):
        # CI makes those generated files for the PR's tree; the gate has main's (fetched).
        heavy = ["provenance", "provenance-gap"]
        self.assertEqual(fc.regenerated("python3 scripts/generated.py produce --group provenance --out x", heavy),
                         {"provenance"})
        self.assertEqual(fc.regenerated("python3 scripts/generated.py produce --group coverage", heavy), set())
        self.assertEqual(fc.regenerated("python3 scripts/generated.py materialize", heavy), set())  # fetches
        self.assertEqual(fc.regenerated("python3 scripts/generated.py materialize --heavy regen", heavy), set(heavy))
        units = {u["checks"][0]: u for u in fc.discover(fc.Tree())}
        self.assertIn("regenerates", units["tests/roadmap/artifact-manifest/test_fixture.py"]["left_out"])
        self.assertIsNone(units["tests/roadmap/outcome-taxonomy/test_taxonomy.py"]["left_out"])


if __name__ == "__main__":
    unittest.main()
