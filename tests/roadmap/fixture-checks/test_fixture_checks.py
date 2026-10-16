"""scripts/fixture-checks.py: which CI checks it runs, and that a unit's key is what it read.

Discovery runs over the real workflow: every Python test a CI step runs (a tests/ script run by
python3, a `unittest discover -s tests/...`) and every proof-fixture check.sh is in a unit. Records
run over a temporary repository: a read Lake output stands for its module's import closure, so a
comment in a module reruns only the units that loaded an importer of it, a docs edit reruns none
of them, and a new file in a directory a unit read from reruns it. A traced run in a worktree
reports the files and directories its command read and no others, and leaves no worktree.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("air2lean_fixture_checks", ROOT / "scripts/fixture-checks.py")
fc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fc)


def repo(files):
    """A temporary git repository with FILES ({path: text}), committed."""
    tmp = tempfile.TemporaryDirectory()
    path = Path(tmp.name).resolve() / "repo"
    for name, text in files.items():
        (path / name).parent.mkdir(parents=True, exist_ok=True)
        (path / name).write_text(text)
    git = ["git", "-C", str(path), "-c", "user.name=t", "-c", "user.email=t@t"]
    subprocess.run(git[:3] + ["init", "-q"], check=True)
    subprocess.run(git + ["add", "-A"], check=True)
    subprocess.run(git + ["commit", "-qm", "x"], check=True)
    return tmp, path


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

    def test_the_runner_key_is_the_staging_tracing_and_recording_code(self):
        text = (ROOT / "scripts/fixture-checks.py").read_text()
        region = text[text.index("# ---- key-relevant: begin"):text.index("# ---- key-relevant: end")]
        for name in ("class Keyer", "def traced(", "def watch(", "def _stage(", "def cloned_entries("):
            self.assertIn(name, region)
        self.assertNotIn("def discover(", region)


class Records(unittest.TestCase):
    def setUp(self):
        self.tmp, self.repo = repo({
            "lakefile.toml": '[[lean_lib]]\nname = "Lib"\n\n[[lean_exe]]\nname = "tool"\nroot = "Lib.Main"\n',
            "lean-toolchain": "leanprover/lean4:test\n",
            "Lib/A.lean": "import Lib.B\n", "Lib/B.lean": "-- b\n", "Lib/Main.lean": "import Lib.A\n",
            "Other/C.lean": "def c := 1\n", "tests/x/data.json": "{}\n", "docs/ci.md": "# ci\n"})
        self.addCleanup(self.tmp.cleanup)
        patcher = mock.patch.object(fc, "ROOT", self.repo)
        patcher.start()
        self.addCleanup(patcher.stop)

    def keyer(self):
        return fc.Keyer(fc.Tree())

    def write(self, name, text):
        (self.repo / name).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / name).write_text(text)

    def test_a_lake_output_stands_for_its_import_closure(self):
        record = self.keyer().record(None, [".lake/build/lib/lean/Lib/A.olean"])
        for path in ("Lib/A.lean", "Lib/B.lean", "lakefile.toml", "lean-toolchain", "Lib/"):
            self.assertIn(path, record)
        for path in ("Lib/Main.lean", "Other/C.lean", "docs/ci.md"):
            self.assertNotIn(path, record)
        tool = self.keyer().record(None, [".lake/build/bin/tool"])
        self.assertTrue({"Lib/Main.lean", "Lib/A.lean", "Lib/B.lean"} <= set(tool))

    def test_a_comment_reruns_only_the_units_that_loaded_an_importer(self):
        keyer = self.keyer()
        lean = keyer.record(None, [".lake/build/lib/lean/Lib/A.olean"])
        data = keyer.record(None, ["tests/x/data.json"])
        self.write("Lib/B.lean", "-- b, a comment\n")
        self.assertFalse(self.keyer().matches(lean))
        self.assertTrue(self.keyer().matches(data))
        self.write("Lib/B.lean", "-- b\n")
        self.write("docs/ci.md", "# ci, edited\n")
        self.assertTrue(self.keyer().matches(lean))
        self.assertTrue(self.keyer().matches(data))

    def test_a_new_file_where_a_unit_read_reruns_it(self):
        record = self.keyer().record(None, ["tests/x/data.json"])
        self.write("Other/new.lean", "\n")
        self.assertTrue(self.keyer().matches(record))
        self.write("tests/x/new.json", "{}\n")
        self.assertFalse(self.keyer().matches(record))


class Traced(unittest.TestCase):
    def setUp(self):
        self.tmp, self.repo = repo({"a.txt": "a\n", "b.txt": "b\n", "sub/c.txt": "c\n"})
        self.addCleanup(self.tmp.cleanup)
        patcher = mock.patch.object(fc, "ROOT", self.repo)
        patcher.start()
        self.addCleanup(patcher.stop)

    def reads(self, argv):
        scratch = Path(self.tmp.name) / "run"
        scratch.mkdir(exist_ok=True)
        spec = scratch / "spec.json"
        spec.write_text(json.dumps({"argv": argv, "dest": str(scratch / "tree"), "commit": fc.CR.snapshot(self.repo),
                                    "clone": [], "trace": str(scratch / "trace.json")}))
        self.assertEqual(fc.traced(spec), 0)
        self.assertFalse((scratch / "tree").exists())
        return json.loads((scratch / "trace.json").read_text())

    def test_what_the_command_read_and_nothing_else(self):
        reads = self.reads(["cat", "a.txt"])
        self.assertIn("a.txt", reads)
        self.assertNotIn("b.txt", reads)
        self.assertNotIn("sub/c.txt", reads)
        reads = self.reads(["ls", "sub"])
        self.assertIn("sub/", reads)
        self.assertNotIn("sub/c.txt", reads)

    def test_git_status_reads_no_unchanged_file(self):
        reads = self.reads(["git", "status", "--porcelain", "--untracked-files=no"])
        self.assertNotIn("a.txt", reads)
        self.assertNotIn("sub/c.txt", reads)

    def test_no_worktree_is_left(self):
        self.reads(["true"])
        worktrees = subprocess.run(["git", "-C", str(self.repo), "worktree", "list"], capture_output=True,
                                   text=True, check=True).stdout.splitlines()
        self.assertEqual(len(worktrees), 1)


if __name__ == "__main__":
    unittest.main()
