#!/usr/bin/env python3
"""scripts/tree-rename.py: the dry run changes nothing, an apply moves and rewrites every kind of
reference, the check finds a stale one, and a stale or ambiguous map is an error."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("tree_rename", ROOT / "scripts/tree-rename.py")
tr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tr)

MAP = {
    "schema_version": 1,
    "lean_roots": ["ZigLean", "Proofs"],
    "drop_prefix": ["ZigLean/"],
    "never_rewrite": ["map.json"],
    "groups": [
        {"id": "G1", "title": "drop Full", "rules": [
            {"kind": "dir", "from": "ZigLean/Sep/Full", "to": "ZigLean/Sep"},
            {"kind": "file", "from": "ZigLean/Sep/Heap.lean", "to": "ZigLean/Sep/Base/Heap.lean"}]},
        {"id": "G2", "title": "families", "rules": [
            {"kind": "family", "dir": "ZigLean/Sep", "name": "Lock"}]},
        {"id": "G3", "title": "fixtures", "rules": [
            {"kind": "dir", "from": "tests/roadmap", "to": "tests/fixtures"}]},
        {"id": "G4", "title": "docs", "rules": [
            {"kind": "files", "from_dir": "docs", "to_dir": "docs/logic", "names": ["a.md", "b.md"]}]},
    ],
}

FILES = {
    "map.json": json.dumps(MAP),
    "ZigLean/Sep/Heap.lean": "namespace H\n",
    "ZigLean/Sep/Full/A.lean": "import ZigLean.Sep.Heap\nimport ZigLean.Sep.Full.Lock\nimport ZigLean.Sep.Full.AutoArith\n",
    "ZigLean/Sep/Full/Auto.lean": "-- ZigLean.Sep.Full.Auto.\n",
    "ZigLean/Sep/Full/AutoArith.lean": "import ZigLean.Sep.Full.Auto\n",
    "ZigLean/Sep/Full/Lock.lean": "import ZigLean.Sep.Full.LockX\n",
    "ZigLean/Sep/Full/LockX.lean": "-- Locker is not a family member\n",
    "ZigLean/Sep/Full/Locker.lean": "-- lower case after Lock: stays beside\n",
    "Proofs/Foo/Gen.lean": "import ZigLean.Sep.Full.A\n",
    "lakefile.toml": 'roots = ["ZigLean.Sep.Full.A"]\nglobs = ["ZigLean.Sep.Heap", "ZigLean.Sep.Full.Lock"]\n',
    "assurance/x.json": json.dumps({"path": "ZigLean/Sep/Full/A.lean", "short": "Sep/Full/Lock.lean",
                                    "dir": "tests/roadmap/f", "other": "tests/roadmap-other/x"}),
    "docs/a.md": "[b](b.md) [src](../ZigLean/Sep/Full/A.lean) [web](https://h/docs/a.md) docs/b.md\n"
                 "[ext]: ../tests/roadmap/f/check.sh\n[anchor](#top) [missing](nope.md)\n",
    "docs/b.md": "[a](a.md#sec) [fixture](../tests/roadmap/f/)\n",
    "docs/getting-started.md": "[a](a.md) `docs/a.md` ZigLean.Sep.Full.A\n",
    "scripts/s.py": "ROOT / 'tests' / 'roadmap' / 'x'\nROOT/\"docs\"/\"a.md\"\nPath('tests/roadmap/f')\n",
    "tests/roadmap/f/check.sh": "run tests/roadmap/f/x\nsource ../../scripts/s.sh\n",
    "tests/roadmap/f/lakefile.toml": 'path = "../.."\n',
    "tests/roadmap/f/X.lean": "import ZigLean.Sep.Full.A\n",
    ".github/workflows/ci.yml": "lake build ZigLean.Sep.Full.A\n  run: tests/roadmap/f/check.sh\n",
}


def sh(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, text=True).stdout


def run(repo, *args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = tr.main(["--root", str(repo), "--map", "map.json", *args])
    return code, out.getvalue() + err.getvalue()


class Repo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        sh(self.repo, "init", "-q")
        sh(self.repo, "config", "user.email", "t@example.com")
        sh(self.repo, "config", "user.name", "t")
        for path, text in FILES.items():
            (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / path).write_text(text)
        sh(self.repo, "add", "-A")
        sh(self.repo, "commit", "-qm", "base")

    def text(self, path):
        return (self.repo / path).read_text()

    def apply_and_commit(self, groups):
        code, out = run(self.repo, "--apply", "--groups", groups)
        self.assertEqual(code, 0, out)
        sh(self.repo, "add", "-A")
        sh(self.repo, "commit", "-qm", groups)


class DryRun(Repo):
    def test_changes_nothing(self):
        before = sh(self.repo, "ls-files", "-s")
        code, out = run(self.repo, "--dry-run")
        self.assertEqual(code, 0, out)
        self.assertEqual(sh(self.repo, "status", "--porcelain"), "")
        self.assertEqual(sh(self.repo, "ls-files", "-s"), before)
        self.assertTrue((self.repo / "ZigLean/Sep/Full/A.lean").is_file())
        self.assertIn("git mv ZigLean/Sep/Full/A.lean ZigLean/Sep/A.lean", out)
        self.assertIn("git mv tests/roadmap tests/fixtures   (3 files)", out)
        self.assertIn("== total:", out)

    def test_default_is_a_dry_run(self):
        code, out = run(self.repo)
        self.assertEqual(code, 0, out)
        self.assertTrue((self.repo / "tests/roadmap").is_dir())

    def test_groups_compose_in_memory(self):
        code, out = run(self.repo, "--groups", "G1,G2", "--diff", "ZigLean/Sep/Full/A.lean")
        self.assertEqual(code, 0, out)
        self.assertIn("+import ZigLean.Sep.Base.Heap", out)
        self.assertIn("+import ZigLean.Sep.Lock\n", out)  # Lock.lean stays beside its directory
        self.assertIn("+import ZigLean.Sep.AutoArith", out)

    def test_tree_option_reads_a_revision(self):
        (self.repo / "ZigLean/Sep/Full/A.lean").write_text("dirty\n")
        code, out = run(self.repo, "--groups", "G1", "--tree", "HEAD", "--diff", "ZigLean/Sep/Full/A.lean")
        self.assertEqual(code, 0, out)
        self.assertIn("+import ZigLean.Sep.Base.Heap", out)  # the committed text, not the dirty one

    def test_apply_with_tree_is_refused(self):
        code, out = run(self.repo, "--apply", "--groups", "G1", "--tree", "HEAD")
        self.assertEqual(code, 1)
        self.assertIn("--apply works on the working tree", out)


class Apply(Repo):
    def test_g1_moves_and_rewrites(self):
        self.apply_and_commit("G1")
        self.assertTrue((self.repo / "ZigLean/Sep/A.lean").is_file())
        self.assertTrue((self.repo / "ZigLean/Sep/Base/Heap.lean").is_file())
        self.assertFalse((self.repo / "ZigLean/Sep/Full").exists())
        self.assertEqual(self.text("ZigLean/Sep/A.lean"),
                         "import ZigLean.Sep.Base.Heap\nimport ZigLean.Sep.Lock\nimport ZigLean.Sep.AutoArith\n")
        # `Auto` and `AutoArith` are different modules; a sentence-final dot ends the module
        self.assertEqual(self.text("ZigLean/Sep/Auto.lean"), "-- ZigLean.Sep.Auto.\n")
        self.assertEqual(self.text("ZigLean/Sep/AutoArith.lean"), "import ZigLean.Sep.Auto\n")
        self.assertEqual(self.text("Proofs/Foo/Gen.lean"), "import ZigLean.Sep.A\n")
        self.assertEqual(self.text("lakefile.toml"),
                         'roots = ["ZigLean.Sep.A"]\nglobs = ["ZigLean.Sep.Base.Heap", "ZigLean.Sep.Lock"]\n')
        self.assertEqual(json.loads(self.text("assurance/x.json")),
                         {"path": "ZigLean/Sep/A.lean", "short": "Sep/Lock.lean",
                          "dir": "tests/roadmap/f", "other": "tests/roadmap-other/x"})
        self.assertEqual(self.text("tests/roadmap/f/X.lean"), "import ZigLean.Sep.A\n")
        self.assertEqual(self.text(".github/workflows/ci.yml"),
                         "lake build ZigLean.Sep.A\n  run: tests/roadmap/f/check.sh\n")
        self.assertEqual(self.text("map.json"), FILES["map.json"])  # never rewritten
        code, out = run(self.repo, "--check", "--groups", "G1", "--old", "HEAD~1")
        self.assertEqual(code, 0, out)

    def test_g3_directory_move_keeps_relative_paths_and_boundaries(self):
        self.apply_and_commit("G3")
        self.assertFalse((self.repo / "tests/roadmap").exists())
        self.assertEqual(self.text("tests/fixtures/f/check.sh"), "run tests/fixtures/f/x\nsource ../../scripts/s.sh\n")
        self.assertEqual(self.text("tests/fixtures/f/lakefile.toml"), 'path = "../.."\n')
        self.assertEqual(self.text("scripts/s.py"),
                         "ROOT / 'tests' / 'fixtures' / 'x'\nROOT/\"docs\"/\"a.md\"\nPath('tests/fixtures/f')\n")
        self.assertIn('"other": "tests/roadmap-other/x"', self.text("assurance/x.json"))
        self.assertIn("tests/fixtures/f", self.text("assurance/x.json"))
        self.assertIn("[ext]: ../tests/fixtures/f/check.sh", self.text("docs/a.md"))
        self.assertIn("[fixture](../tests/fixtures/f/)", self.text("docs/b.md"))
        code, out = run(self.repo, "--check", "--groups", "G3", "--old", "HEAD~1")
        self.assertEqual(code, 0, out)

    def test_g4_markdown_links_follow_both_ends(self):
        self.apply_and_commit("G4")
        self.assertEqual(self.text("docs/logic/a.md"),
                         "[b](b.md) [src](../../ZigLean/Sep/Full/A.lean) [web](https://h/docs/logic/a.md) docs/logic/b.md\n"
                         "[ext]: ../../tests/roadmap/f/check.sh\n[anchor](#top) [missing](nope.md)\n")
        self.assertEqual(self.text("docs/logic/b.md"), "[a](a.md#sec) [fixture](../../tests/roadmap/f/)\n")
        # an unmoved file points at the moved one, in a link and in a path
        self.assertEqual(self.text("docs/getting-started.md"),
                         "[a](logic/a.md) `docs/logic/a.md` ZigLean.Sep.Full.A\n")
        # the pathlib join that changes length is a manual hit, and the check keeps failing on it
        code, out = run(self.repo, "--check", "--groups", "G4", "--old", "HEAD~1")
        self.assertEqual(code, 1)
        self.assertIn("scripts/s.py: 1 reference", out)
        (self.repo / "scripts/s.py").write_text("ROOT / 'docs' / 'logic' / 'a.md'\n")
        sh(self.repo, "add", "-A")
        code, out = run(self.repo, "--check", "--groups", "G4", "--old", "HEAD~1")
        self.assertEqual(code, 0, out)

    def test_one_group_per_apply(self):
        code, out = run(self.repo, "--apply", "--groups", "G1,G2")
        self.assertEqual(code, 1)
        self.assertIn("--allow-multi", out)
        code, out = run(self.repo, "--apply", "--groups", "G1,G2", "--allow-multi")
        self.assertEqual(code, 0, out)
        self.assertTrue((self.repo / "ZigLean/Sep/Lock/X.lean").is_file())
        self.assertTrue((self.repo / "ZigLean/Sep/Lock.lean").is_file())
        self.assertTrue((self.repo / "ZigLean/Sep/Locker.lean").is_file())
        self.assertEqual(self.text("ZigLean/Sep/Lock.lean"), "import ZigLean.Sep.Lock.X\n")

    def test_family_into_another_directory(self):
        (self.repo / "ZigLean/Sep/Full/RwProdStart.lean").write_text("import ZigLean.Sep.Full.RwLock\n")
        (self.repo / "ZigLean/Sep/Full/RwLock.lean").write_text("--\n")
        data = dict(MAP, groups=[{"id": "X", "rules": [
            {"kind": "family", "dir": "ZigLean/Sep/Full", "name": "RwProd", "into": "RwLock", "as": "Prod"}]}])
        (self.repo / "map.json").write_text(json.dumps(data))
        sh(self.repo, "add", "-A")
        sh(self.repo, "commit", "-qm", "rw")
        self.apply_and_commit("X")
        self.assertTrue((self.repo / "ZigLean/Sep/Full/RwLock/ProdStart.lean").is_file())
        self.assertEqual(self.text("ZigLean/Sep/Full/RwLock/ProdStart.lean"), "import ZigLean.Sep.Full.RwLock\n")

    def test_dirty_tree_is_refused(self):
        (self.repo / "docs/a.md").write_text("changed\n")
        code, out = run(self.repo, "--apply", "--groups", "G1")
        self.assertEqual(code, 1)
        self.assertIn("uncommitted", out)
        self.assertTrue((self.repo / "ZigLean/Sep/Full/A.lean").is_file())


class Check(Repo):
    def test_fails_on_a_stale_reference_a_stale_file_and_a_stale_link(self):
        self.apply_and_commit("G1")
        (self.repo / "docs/stale.md").write_text("see ZigLean.Sep.Full.A and `ZigLean/Sep/Full/Lock.lean`\n")
        (self.repo / "scripts/t.py").write_text("p = ROOT / 'ZigLean' / 'Sep' / 'Heap.lean'\n")
        (self.repo / "docs/link.md").write_text("[x](../ZigLean/Sep/Heap.lean)\n")
        sh(self.repo, "add", "-A")
        code, out = run(self.repo, "--check", "--groups", "G1", "--old", "HEAD~1")
        self.assertEqual(code, 1)
        self.assertIn("docs/stale.md: 2 reference", out)
        self.assertIn("scripts/t.py: 1 reference", out)
        self.assertIn("docs/link.md: relative link", out)
        (self.repo / "ZigLean/Sep/Full").mkdir(exist_ok=True)
        (self.repo / "ZigLean/Sep/Full/A.lean").write_text("x\n")
        sh(self.repo, "add", "-A")
        code, out = run(self.repo, "--check", "--groups", "G1", "--old", "HEAD~1")
        self.assertIn("old file remains: ZigLean/Sep/Full/A.lean", out)


class Manual(Repo):
    def test_join_that_changes_length_and_depth_changes_are_reported(self):
        code, out = run(self.repo, "--groups", "G4")
        self.assertEqual(code, 0, out)
        self.assertIn("scripts/s.py: docs/a.md", out)
        code, out = run(self.repo, "--groups", "G1,G2")
        self.assertIn("ZigLean", out)


class BadMap(Repo):
    def write_map(self, groups):
        data = dict(MAP, groups=groups)
        (self.repo / "map.json").write_text(json.dumps(data))
        sh(self.repo, "add", "-A")
        sh(self.repo, "commit", "-qm", "map")

    def test_rule_that_matches_nothing(self):
        self.write_map([{"id": "X", "rules": [{"kind": "dir", "from": "nowhere", "to": "else"}]}])
        code, out = run(self.repo)
        self.assertEqual(code, 1)
        self.assertIn("matches no tracked file", out)

    def test_missing_name_in_files_rule(self):
        self.write_map([{"id": "X", "rules": [{"kind": "files", "from_dir": "docs", "to_dir": "d2", "names": ["a.md", "zzz.md"]}]}])
        code, out = run(self.repo)
        self.assertEqual(code, 1)
        self.assertIn("docs/zzz.md is not tracked", out)

    def test_two_targets_of_one_specificity(self):
        self.write_map([{"id": "X", "rules": [
            {"kind": "file", "from": "docs/a.md", "to": "d1/a.md"},
            {"kind": "files", "from_dir": "docs", "to_dir": "d2", "names": ["a.md"]}]}])
        code, out = run(self.repo)
        self.assertEqual(code, 1)
        self.assertIn("two targets", out)

    def test_most_specific_rule_wins(self):
        self.write_map([{"id": "X", "rules": [
            {"kind": "dir", "from": "docs", "to": "d1"},
            {"kind": "file", "from": "docs/a.md", "to": "d2/a.md"}]}])
        code, out = run(self.repo, "--diff", "docs/b.md")
        self.assertEqual(code, 0, out)
        code, out = run(self.repo)
        self.assertIn("git mv docs/a.md d2/a.md", out)
        self.assertIn("git mv docs/b.md d1/b.md", out)

    def test_collisions(self):
        self.write_map([{"id": "X", "rules": [{"kind": "file", "from": "docs/a.md", "to": "docs/b.md"}]}])
        code, out = run(self.repo)
        self.assertEqual(code, 1)
        self.assertIn("moves onto the tracked file", out)
        self.write_map([{"id": "X", "rules": [
            {"kind": "file", "from": "docs/a.md", "to": "z/c.md"}, {"kind": "file", "from": "docs/b.md", "to": "z/c.md"}]}])
        code, out = run(self.repo)
        self.assertIn("both move to z/c.md", out)
        self.write_map([{"id": "X", "rules": [{"kind": "file", "from": "docs/a.md", "to": "lakefile.toml/a.md"}]}])
        code, out = run(self.repo)
        self.assertIn("would sit below the file", out)


class RepoMap(unittest.TestCase):
    def test_committed_map_is_well_formed(self):
        data = tr.load_map(ROOT)
        self.assertTrue(data["groups"])
        for g in data["groups"]:
            self.assertTrue(g["rules"], g["id"])
            for r in g["rules"]:
                self.assertIn(r["kind"], tr.SPECIFICITY)


if __name__ == "__main__":
    unittest.main()
