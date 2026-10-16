"""scripts/proof-framework.py: new judgments, tactics and legacy users fail; the file only shrinks."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("proof_framework", ROOT / "scripts/proof-framework.py")
pf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pf)


def git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True)


class Scan(unittest.TestCase):
    def test_judgments(self):
        js, _, _ = pf.scan_file("A.lean", "def FooTriple (P : Assn) : Prop := True\n"
                                          "structure BarTemplate where\n  x : Nat\n"
                                          "def applyTemplate : Nat := 0\n-- def NotTriple := 0\n")
        self.assertEqual(js, {"FooTriple", "BarTemplate"})

    def test_structural_judgments(self):
        js, _, _ = pf.scan_file("A.lean", (
            # suffix-less judgments: a program with a postcondition, a contract, a step relation
            "def Holds {α : Type} (x : ConcM Tgt α) (Q : α → Mem → Prop) : Prop :=\n  True\n"
            "def Post (c : MemM α) (P : FAssn) (Q : α → FAssn) : Prop := True\n"
            "structure LockImpl (Tgt : Type) where\n  lock : Ptr → ConcM Tgt Unit\n"
            "  lock_ok : ∀ P : Nat → Prop, True\n"
            "structure Ledger2 (I : Nat) where\n  B : Nat → FAssn\n"
            "structure Moves (m m' : Mem) : Prop where\n  same : m'.current = m.current\n"
            # plain lemmas and data: not judgments
            "theorem t (c : MemM α) (Q : α → Prop) : True := trivial\n"
            "def size (c : MemM α) : Nat := 0\n"
            "def Pure (n : Nat) (Q : Nat → Prop) : Prop := Q n\n"
            "def Same (m m' : Mem) : Prop := m = m'\n"
            "structure Config where\n  n : Nat\n  run : Nat → MemM Nat\n"))
        self.assertEqual(js, {"Holds", "Post", "LockImpl", "Ledger2", "Moves"})

    def test_tactics(self):
        _, ts, _ = pf.scan_file("A.lean", 'syntax (name := s) "my_step"\n  term : tactic\n'
                                          'macro "my_norm" : tactic => `(tactic| simp)\n'
                                          'macro_rules\n  | `(tactic| fsym_fact) => `(tactic| omega)\n'
                                          'macro_rules\n  | `(tactic| my_step $t) => `(tactic| exact $t)\n'
                                          'syntax foo := "x"\n')
        self.assertEqual(ts, {("syntax", "my_step"), ("syntax", "my_norm"), ("rules", "fsym_fact")})

    def test_commands(self):
        _, ts, _ = pf.scan_file("A.lean", 'elab "if_decl " id:ident " in " cmds:command* " end_if" : command => do\n'
                                          '  if found then cmds.forM elabCommand\n'
                                          'macro "gen_specs" : command => `(tactic| simp)\n'
                                          'macro_rules\n  | `(command| when_defined $i $c*) => `(command| skip)\n'
                                          'elab_rules : command\n  | `(if_decl $i in $c* end_if) => pure ()\n'
                                          'macro_rules\n  | `(my_term $t) => `($t)\n')
        self.assertEqual(ts, {("command", "if_decl"), ("command", "gen_specs"),
                              ("command-rules", "when_defined")})

    def test_legacy(self):
        self.assertEqual(pf.scan_file("A.lean", "import ZigLean.Sep.Total\n")[2], "imports ZigLean.Sep.Total")
        self.assertEqual(pf.scan_file("A.lean", "theorem t : TTriple P c Q := h\n")[2], "names TTriple")
        # An import line is not a use of the name `Triple`; a Conc-cluster import is a legacy use.
        self.assertIsNone(pf.scan_file("A.lean", "import ZigLean.Sep.Full.Triple\ndef x := 1\n")[2])
        self.assertEqual(pf.scan_file("A.lean", "import ZigLean.Conc.Csl\n")[2], "imports ZigLean.Conc.Csl")
        self.assertEqual(pf.scan_file("A.lean", "import ZigLean.Conc.TlsLemmas\n")[2],
                         "imports ZigLean.Conc.TlsLemmas")
        self.assertIsNone(pf.scan_file("A.lean", "import ZigLean.Conc.Logic\n")[2])
        self.assertIsNone(pf.scan_file("A.lean", "import ZigLean.Sep.Full.Logic\n"
                                                  "theorem t : FTriple P c Q := FTriple.ofTriple h\n"
                                                  "-- Triple\ndef s := \"Triple\"\n")[2])


class Ratchet(unittest.TestCase):
    def setUp(self):
        # The scratch repository has no `origin`: without --base, CI would fetch its base branch.
        env = mock.patch.dict(os.environ)
        env.start()
        self.addCleanup(env.stop)
        os.environ.pop("GITHUB_ACTIONS", None)
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "t@example.com")
        git(self.repo, "config", "user.name", "t")
        (self.repo / "assurance").mkdir()
        (self.repo / "Old.lean").write_text("theorem a : Triple P c Q := h\ndef OldTriple : Prop := True\n")
        (self.repo / "New.lean").write_text("theorem b : FTriple P c Q := h\n")
        git(self.repo, "add", ".")
        self.assertEqual(pf.main(["--root", str(self.repo), "--write"]), 0)
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "base")

    def tearDown(self):
        self.tmp.cleanup()

    def check(self):
        return pf.main(["--root", str(self.repo), "--base", "HEAD"])

    def test_clean(self):
        self.assertEqual(self.check(), 0)

    def test_new_judgment_fails(self):
        (self.repo / "New.lean").write_text("def NewReturns : Prop := True\n")
        self.assertEqual(self.check(), 1)

    def test_new_suffixless_judgment_fails(self):
        (self.repo / "New.lean").write_text("def Holds (x : ConcM Tgt α) (Q : α → Prop) : Prop := True\n")
        self.assertEqual(self.check(), 1)

    def test_new_lemma_passes(self):
        (self.repo / "New.lean").write_text("theorem l (x : MemM α) (Q : α → Prop) : True := trivial\n"
                                            "def helper (x : MemM α) : Nat := 0\n")
        self.assertEqual(self.check(), 0)

    def test_new_tactic_fails(self):
        (self.repo / "New.lean").write_text('macro "my_tac" : tactic => `(tactic| rfl)\n')
        self.assertEqual(self.check(), 1)

    def test_new_command_fails(self):
        (self.repo / "New.lean").write_text('elab "skip_unless " id:ident cmds:command* : command => pure ()\n')
        self.assertEqual(self.check(), 1)

    def test_new_legacy_user_fails(self):
        (self.repo / "New.lean").write_text("import ZigLean.Sep.Loop\n")
        self.assertEqual(self.check(), 1)

    def test_stale_entry_fails(self):
        (self.repo / "Old.lean").write_text("theorem a : FTriple P c Q := h\n")
        self.assertEqual(self.check(), 1)

    def test_only_shrinks_unless_approved(self):
        (self.repo / "New.lean").write_text("def NewReturns : Prop := True\n")
        pf.main(["--root", str(self.repo), "--write"])
        self.assertEqual(self.check(), 1)
        path = self.repo / pf.FILE
        data = json.loads(path.read_text())
        for e in data["judgments"]:
            if e["name"] == "NewReturns":
                e["approved"] = "coordinator, 2026-10-12, test"
        path.write_text(json.dumps(data))
        self.assertEqual(self.check(), 0)


if __name__ == "__main__":
    unittest.main()
