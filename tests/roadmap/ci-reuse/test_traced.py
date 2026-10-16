"""scripts/ci-reuse.py's traced records (docs/ci.md#traced-records): the one mechanism that keys the
units of scripts/gate.py and scripts/fixture-checks.py.

Records run over a temporary repository: a unit is reused while every file it read and the names
in every directory a probe could have looked in are as they were. A rebuilt Lake output reruns
only the units that read it; a docs edit reruns none; a file created next to or above a file a
unit read, or on the Lean search path it loaded from, reruns it. A traced run reads its own tree
only: what it read is reported exactly, a unit that only probed a path reruns when the path is
created, its `git status` reads no unchanged file and nothing is left behind. Outside the checkout
(the macOS sandbox): a file outside every keyed root reads as absent even when it exists, and a
change inside a keyed root changes every pre-key.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("air2lean_ci_reuse", ROOT / "scripts/ci-reuse.py")
CR = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CR)


def atime_moves():
    """Whether a read moves an access time set before the modification time here (not on a
    `noatime` mount)."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "f"
        path.write_text("x")
        os.utime(path, ns=(0, path.stat().st_mtime_ns))
        path.read_text()
        return path.stat().st_atime_ns != 0


SANDBOX = CR.Outside(ROOT).available()


def repo(files):
    """A temporary git repository with FILES ({path: text}), committed; its path."""
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


class Records(unittest.TestCase):
    def setUp(self):
        self.tmp, self.repo = repo({
            "lakefile.toml": '[[lean_lib]]\nname = "Lib"\n', ".gitignore": ".lake/\n",
            "Lib/A.lean": "import Lib.B\n", "Lib/B.lean": "-- b\n", "Other/C.lean": "def c := 1\n",
            "tests/x/data.json": "{}\n", "docs/ci.md": "# ci\n"})
        self.addCleanup(self.tmp.cleanup)
        self.write(".lake/build/lib/lean/Lib/A.olean", "olean A")
        self.write(".lake/build/lib/lean/Lib/B.olean", "olean B")

    def write(self, name, text):
        (self.repo / name).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / name).write_text(text)

    def records(self):
        return CR.Records(self.repo, CR.snapshot(self.repo))

    def test_a_rebuilt_build_output_reruns_only_the_units_that_read_it(self):
        records = self.records()
        lean = records.record([".lake/build/lib/lean/Lib/A.olean", ".lake/build/lib/lean/Lib/B.olean"])
        data = records.record(["tests/x/data.json"])
        self.assertIn(".lake/build/lib/lean/Lib/", lean)  # the search-path directory it loaded from
        self.write("Lib/B.lean", "-- b, a comment\n")  # the full build rebuilds B's output
        self.write(".lake/build/lib/lean/Lib/B.olean", "olean B'")
        self.assertFalse(self.records().matches(lean))
        self.assertTrue(self.records().matches(data))
        lean = self.records().record([".lake/build/lib/lean/Lib/A.olean", ".lake/build/lib/lean/Lib/B.olean"])
        self.write("docs/ci.md", "# ci, edited\n")
        self.assertTrue(self.records().matches(lean))
        self.assertTrue(self.records().matches(data))

    def test_a_probe_next_to_or_above_what_a_unit_read_reruns_it(self):
        # `[ -e tests/x/flag ]` is a stat (no access time); the listings of every ancestor cover it.
        record = self.records().record(["tests/x/data.json"])
        for probe in ("tests/x/flag", "tests/flag", "flag"):
            with self.subTest(probe=probe):
                self.write(probe, "")
                self.assertFalse(self.records().matches(record))
                (self.repo / probe).unlink()
                self.assertTrue(self.records().matches(record))

    def test_a_module_appearing_on_the_lean_search_path_reruns(self):
        self.write("tests/diff/lakefile.toml", "")
        self.write("tests/diff/.lake/build/lib/lean/Other.olean", "olean")
        record = self.records().record([".lake/build/lib/lean/Lib/A.olean"])
        self.write(".lake/build/lib/lean/Lib/New.olean", "olean")
        self.assertFalse(self.records().matches(record))
        (self.repo / ".lake/build/lib/lean/Lib/New.olean").unlink()
        self.assertTrue(self.records().matches(record))
        # Earlier on the search path, in another package's build: it would shadow the one read.
        self.write("tests/diff/.lake/build/lib/lean/Lib/A.olean", "olean")
        self.assertFalse(self.records().matches(record))

    def test_a_new_file_where_a_unit_read_reruns_it_and_elsewhere_not(self):
        record = self.records().record(["tests/x/data.json"])
        self.write("Other/new.lean", "\n")
        self.assertTrue(self.records().matches(record))
        self.write("tests/x/new.json", "{}\n")
        self.assertFalse(self.records().matches(record))

    def test_a_record_is_of_its_snapshot(self):
        records = self.records()
        self.write("tests/x/data.json", '{"edited": true}\n')  # after the snapshot the unit ran on
        record = records.record(["tests/x/data.json"])
        self.assertFalse(self.records().matches(record))
        self.write("tests/x/data.json", "{}\n")
        self.assertTrue(self.records().matches(record))

    def test_the_store_finds_a_matching_record_with_its_files(self):
        with tempfile.TemporaryDirectory() as cas, mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": cas}):
            self.write("gen/out.json", "{}\n")
            records = self.records()
            self.assertIsNone(records.lookup("p"))
            self.assertIsNone(records.changed("p"))
            records.publish("p", records.record(["tests/x/data.json"]), {"unit": "u"}, outputs=["gen/out.json"])
            entry = records.lookup("p")
            self.assertEqual(entry.parent.name, CR.LOCAL_KIND)  # an entry of scripts/cas.py's store
            self.assertEqual((entry / "files/gen/out.json").read_text(), "{}\n")
            self.write("tests/x/data.json", "[]\n")
            self.assertIsNone(self.records().lookup("p"))
            self.assertEqual(self.records().changed("p"), ["tests/x/data.json"])
            for i in range(10):
                records.publish("p", {"x%d" % i: None}, {"unit": "u"}, keep=3)
            self.assertEqual(len(records.entries("p")), 3)


class Trace(unittest.TestCase):
    def setUp(self):
        self.tmp, self.repo = repo({"a.txt": "a\n", "b.txt": "b\n", "sub/c.txt": "c\n"})
        self.addCleanup(self.tmp.cleanup)
        self.outside = CR.Outside(self.repo)

    def run_traced(self, argv, sandbox=True):
        private = Path(tempfile.mkdtemp(dir=self.tmp.name))
        spec = private / "spec.json"
        spec.write_text(json.dumps({
            "root": str(self.repo), "argv": argv, "env": self.outside.environment()[0], "dest": str(private / "tree"),
            "private": str(private), "commit": CR.snapshot(self.repo), "clone": [], "trace": str(private / "trace.json"),
            "profile": self.outside.profile(private) if sandbox and self.outside.available() else None}))
        code = CR.trace(spec)
        self.assertFalse((private / "tree").exists())
        return code, json.loads((private / "trace.json").read_text())

    @unittest.skipUnless(atime_moves(), "reads move no access time here (noatime)")
    def test_what_the_command_read_and_nothing_else(self):
        _, trace = self.run_traced(["cat", "a.txt"])
        self.assertIn("a.txt", trace["reads"])
        self.assertNotIn("b.txt", trace["reads"])
        self.assertNotIn("sub/c.txt", trace["reads"])
        _, trace = self.run_traced(["ls", "sub"])
        self.assertIn("sub/", trace["reads"])
        self.assertNotIn("sub/c.txt", trace["reads"])

    @unittest.skipUnless(SANDBOX, "no sandbox here: no record")
    def test_a_file_outside_every_root_reads_as_absent_although_it_exists(self):
        secret = Path(self.tmp.name).resolve() / "outside.txt"
        secret.write_text("secret\n")
        self.assertNotEqual(self.run_traced(["cat", str(secret)])[0], 0)
        self.assertEqual(self.run_traced(["test", "-e", str(secret)])[0], 1)
        self.assertEqual(self.run_traced(["test", "-e", str(self.repo / "a.txt")])[0], 1)  # the checkout too
        self.assertEqual(self.run_traced(["test", "-e", "a.txt"])[0], 0)  # its tree's copy is there

    @unittest.skipUnless(SANDBOX, "no sandbox here: no record")
    def test_a_unit_that_only_probes_a_file_reruns_when_it_is_created(self):
        # A lookup in order (as a golden or a Lean module is looked up): the absent first choice
        # is only probed (a stat moves no access time), the second is read.
        code, trace = self.run_traced(["sh", "-c", "test -e sub/flag || cat sub/c.txt"])
        self.assertEqual(code, 0)
        self.assertNotIn("sub/", trace["reads"])
        self.assertTrue(CR.Records(self.repo, CR.snapshot(self.repo)).matches(trace["record"]))
        (self.repo / "sub/flag").write_text("")
        self.assertFalse(CR.Records(self.repo, CR.snapshot(self.repo)).matches(trace["record"]))

    @unittest.skipUnless(atime_moves(), "reads move no access time here (noatime)")
    def test_the_base_ref_is_the_trees_one_ref_and_a_read_of_it_is_keyed(self):
        git = ["git", "-C", str(self.repo)]
        subprocess.run(git + ["update-ref", CR.BASE_REF, "HEAD"], check=True)
        code, trace = self.run_traced(["git", "rev-parse", "--verify", "origin/main"])
        self.assertEqual(code, 0)
        self.assertIn(".git/" + CR.BASE_REF, trace["reads"])
        _, listing = self.run_traced(["git", "branch", "--list"])  # a listing of the refs counts too
        self.assertIn(".git/" + CR.BASE_REF, CR.Records(self.repo, CR.snapshot(self.repo)).record(listing["reads"]))
        record = CR.Records(self.repo, CR.snapshot(self.repo)).record(trace["reads"])
        self.assertEqual(record[".git/" + CR.BASE_REF], CR.base_ref(self.repo))
        self.assertNotIn(".git/" + CR.BASE_REF, CR.Records(self.repo, CR.snapshot(self.repo)).record(["a.txt"]))
        (self.repo / "a.txt").write_text("a, edited\n")
        subprocess.run(git + ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qam", "y"], check=True)
        subprocess.run(git + ["update-ref", CR.BASE_REF, "HEAD"], check=True)  # main moved
        self.assertFalse(CR.Records(self.repo, CR.snapshot(self.repo)).matches(
            {".git/" + CR.BASE_REF: record[".git/" + CR.BASE_REF]}))
        self.assertEqual(self.run_traced(["git", "rev-parse", "--verify", "HEAD~1"])[0], 128)  # no history

    @unittest.skipUnless(atime_moves(), "reads move no access time here (noatime)")
    def test_git_status_reads_no_unchanged_file(self):
        _, trace = self.run_traced(["git", "status", "--porcelain", "--untracked-files=no"])
        self.assertNotIn("a.txt", trace["reads"])
        self.assertNotIn("sub/c.txt", trace["reads"])

    def test_nothing_is_left_behind_and_the_checkout_is_untouched(self):
        self.run_traced(["true"])
        git = ["git", "-C", str(self.repo)]
        self.assertEqual(len(subprocess.run(git + ["worktree", "list"], capture_output=True, text=True,
                                            check=True).stdout.splitlines()), 1)
        self.assertEqual(subprocess.run(git + ["status", "--porcelain"], capture_output=True, text=True,
                                        check=True).stdout, "")

    def test_no_record_without_the_sandbox_or_when_a_clone_changed(self):
        _, trace = self.run_traced(["true"], sandbox=False)
        self.assertIsNone(trace["record"])
        self.assertIn("no sandbox", trace["reason"])
        if self.outside.available():
            with mock.patch.object(CR, "clone_state", side_effect=[{"x": "1"}, {"x": "2"}]):
                _, trace = self.run_traced(["true"])
            self.assertIsNone(trace["record"])
            self.assertIn("changed during the run", trace["reason"])


class Outside(unittest.TestCase):
    def setUp(self):
        self.tmp, self.repo = repo({"a.txt": "a\n"})
        self.addCleanup(self.tmp.cleanup)

    def test_a_change_inside_a_keyed_root_changes_the_pre_key(self):
        root = Path(self.tmp.name).resolve() / "toolchain"
        (root / "lib").mkdir(parents=True)
        (root / "lib/std.zig").write_text("one\n")
        records = CR.Records(self.repo, CR.snapshot(self.repo))
        before = records.prekey(CR.Outside(self.repo, keyed={root: "tree"}), {"argv": ["true"]})
        self.assertEqual(before, records.prekey(CR.Outside(self.repo, keyed={root: "tree"}), {"argv": ["true"]}))
        (root / "lib/std.zig").write_text("two, longer\n")
        outside = CR.Outside(self.repo, keyed={root: "tree"})
        self.assertNotEqual(before, records.prekey(outside, {"argv": ["true"]}))
        (root / "lib/new.zig").write_text("")  # an absent path appearing there too
        self.assertNotEqual(outside.identity(), outside.identity(fresh=True))

    def test_the_environment_keeps_the_listed_variables_and_readable_path_entries(self):
        with mock.patch.dict(os.environ, {"FOO": "1", "AIR2LEAN_X": "2", "AIR2LEAN_JOBS": "4",
                                          "PATH": "/nowhere/bin:/usr/bin:%s" % self.tmp.name}):
            env, keyed = CR.Outside(self.repo).environment()
        self.assertNotIn("FOO", env)
        self.assertEqual((env["AIR2LEAN_X"], keyed["AIR2LEAN_X"]), ("2", "2"))
        self.assertEqual(env["AIR2LEAN_JOBS"], "4")
        self.assertNotIn("AIR2LEAN_JOBS", keyed)  # scheduling
        self.assertEqual(env["PATH"], "/usr/bin")

    def test_the_machinery_is_in_every_pre_key(self):
        records = CR.Records(self.repo, CR.snapshot(self.repo))
        outside = CR.Outside(self.repo)
        before = records.prekey(outside, {"argv": ["true"]})
        with mock.patch.object(CR, "MACHINERY_KEY", "another"):
            self.assertNotEqual(before, records.prekey(outside, {"argv": ["true"]}))
        text = (ROOT / "scripts/ci-reuse.py").read_text()
        region = text[text.index("# ---- key-relevant: begin"):text.index("# ---- key-relevant: end")]
        for name in ("class Outside", "def trace(", "class Records", "def watch(", "def cloned_entries("):
            self.assertIn(name, region)


if __name__ == "__main__":
    unittest.main()
