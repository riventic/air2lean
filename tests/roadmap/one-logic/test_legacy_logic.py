"""scripts/legacy-logic.py: a new legacy user fails, a stale entry fails, the list only shrinks."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("legacy_logic", ROOT / "scripts/legacy-logic.py")
ll = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ll)


def git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)


class Detection(unittest.TestCase):
    def test_import(self):
        self.assertEqual(ll.uses_legacy("import ZigLean.Sep.Total\n"), "imports ZigLean.Sep.Total")
        self.assertEqual(ll.uses_legacy("import ZigLean.Sep\n"), "imports ZigLean.Sep")
        self.assertIsNone(ll.uses_legacy("import ZigLean.Sep.Full.Auto\nimport ZigLean.Sep.Heap\n"))

    def test_names(self):
        self.assertEqual(ll.uses_legacy("theorem t : TotalTriple P c Q := x"), "names TotalTriple")
        self.assertIsNone(ll.uses_legacy("theorem t : FTriple P c Q := FTriple.ofTriple h"))
        self.assertIsNone(ll.uses_legacy("-- Triple\n/- a /- nested Triple -/ -/\ndef s := \"Triple\""))


class Ratchet(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "t@example.com")
        git(self.repo, "config", "user.name", "t")
        (self.repo / "scripts").mkdir()
        (self.repo / "Old.lean").write_text("theorem a : Triple P c Q := h\n")
        (self.repo / "New.lean").write_text("theorem b : FTriple P c Q := h\n")
        git(self.repo, "add", ".")
        self.assertEqual(ll.main(["--root", str(self.repo), "--write"]), 0)
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "base")

    def tearDown(self):
        self.tmp.cleanup()

    def run_check(self):
        return ll.main(["--root", str(self.repo), "--base", "HEAD"])

    def test_clean(self):
        self.assertEqual(self.run_check(), 0)

    def test_new_user_fails(self):
        (self.repo / "New.lean").write_text("import ZigLean.Sep.Loop\n")
        self.assertEqual(self.run_check(), 1)

    def test_stale_entry_fails(self):
        (self.repo / "Old.lean").write_text("theorem a : FTriple P c Q := h\n")
        self.assertEqual(self.run_check(), 1)

    def test_list_only_shrinks(self):
        (self.repo / "New.lean").write_text("theorem b : TTriple P c Q := h\n")
        ll.main(["--root", str(self.repo), "--write"])
        self.assertEqual(self.run_check(), 1)
        self.assertEqual(ll.main(["--root", str(self.repo)]), 0)  # without a base: exact only


if __name__ == "__main__":
    unittest.main()
