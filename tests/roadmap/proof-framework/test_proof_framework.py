"""scripts/proof-framework.py: new judgments, tactics, registries and legacy users fail; the file only
shrinks."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

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

    def test_simp_like_tactic(self):
        _, ts, _ = pf.scan_file("A.lean", 'declare_simp_like_tactic (all := true) simpAllX "simp_all_x " (autoUnfold := true)\n'
                                          '/-- doc -/\ndeclare_simp_like_tactic simpX "simp_x " (autoUnfold := true)\n'
                                          'def kw := "declare_simp_like_tactic"\n')
        self.assertEqual(ts, {("syntax", "simp_all_x"), ("syntax", "simp_x")})

    def test_registries(self):
        found = pf.scan_registries(
            "register_simp_attr my_set\n"
            "/-- doc -/\nregister_label_attr my_label\n"
            "register_grind_attr my_grind\n"
            "initialize registerBuiltinAttribute {\n  name := `my_rule\n  descr := \"d\"\n"
            "  add := fun decl _ kind => ext.add decl kind\n}\n"
            "initialize tagExt : TagAttribute ← registerTagAttribute `my_tag \"d\"\n"
            "builtin_initialize Lean.registerParametricAttribute { name := `my_param, descr := \"d\" }\n"
            "initialize registerEnumAttributes\n  [(`a_one, \"d\", 1), (`a_two, \"d\", 2)]\n"
            "initialize registerSimpAttr `my_simp \"d\"\n"
            "initialize ext ← Lean.KeyedDeclsAttribute.init { builtinName := `b, name := `my_keyed }\n"
            "initialize registerBuiltinAttribute <| mkImpl\n"
            "declare_aesop_rule_sets [RuleA, RuleB]\n")
        self.assertEqual(found, {
            ("simp-set", "my_set"), ("attribute", "my_label"), ("attribute", "my_grind"),
            ("attribute", "my_rule"), ("attribute", "my_tag"), ("attribute", "my_param"),
            ("attribute", "a_one"), ("attribute", "a_two"), ("simp-set", "my_simp"),
            ("attribute", "my_keyed"), ("attribute", "mkImpl"),
            ("rule-set", "RuleA"), ("rule-set", "RuleB")})
        # An attribute that the file cannot name is recorded by its argument, for the reviewer.
        self.assertEqual(pf.scan_registries("initialize registerBuiltinAttribute { name := n, descr := d }\n"),
                         {("attribute", "n")})
        self.assertEqual(pf.scan_registries("initialize registerBuiltinAttribute impl\n"),
                         {("attribute", "impl")})
        self.assertEqual(pf.scan_registries("initialize registerSimpleTagAttr `t\ninitialize registerSimprocAttr `s\n"),
                         {("attribute", "t"), ("simp-set", "s")})

    def test_registry_applications_are_not_declarations(self):
        self.assertEqual(pf.scan_registries(
            "@[fsym] theorem a : True := trivial\n@[fsym_norm, simp] theorem b : True := trivial\n"
            "attribute [fsym_atom] Junk\nattribute [local simp] foo\n"
            "example : True := by simp [fsym_norm]\n"
            "simproc [fsym_norm] reduceFoo (foo _) := fun e => pure .continue\n"
            "dsimproc [fsym_norm, fsym_arith] reduceBar (_) := fun e => pure .continue\n"
            # comments and strings are not code; a definition of a registration function registers nothing
            "-- register_simp_attr in_comment\n/- initialize registerBuiltinAttribute { name := `in_block } -/\n"
            'def kws := ["register_simp_attr", "builtin_initialize", "declare_simp_like_tactic"]\n'
            "def registerFooAttr (n : Name) : IO Unit := pure ()\n"
            # extensions, trace classes and options add no attribute
            "initialize fooExt : SimpleScopedEnvExtension Name (Array Name) ←\n"
            "  registerSimpleScopedEnvExtension { addEntry := fun s n => s.push n, initial := #[] }\n"
            "initialize registerTraceClass `fsym\n"), set())

    def test_registry_status(self):
        self.assertEqual(pf.default_status({"registry": "fsym_run", "kind": "attribute", "module": "A"}), "target")
        self.assertEqual(pf.default_status({"registry": "my_set", "kind": "simp-set", "module": "A"}),
                         "legacy-to-retire")

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
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "t@example.com")
        git(self.repo, "config", "user.name", "t")
        (self.repo / "assurance").mkdir()
        (self.repo / "Old.lean").write_text("theorem a : Triple P c Q := h\ndef OldTriple : Prop := True\n")
        (self.repo / "New.lean").write_text("theorem b : FTriple P c Q := h\n")
        (self.repo / "Attr.lean").write_text("register_simp_attr base_set\n"
                                             "initialize registerBuiltinAttribute {\n  name := `base_attr\n"
                                             "  add := fun decl _ kind => baseExt.add decl kind\n}\n")
        git(self.repo, "add", ".")
        self.assertEqual(pf.main(["--root", str(self.repo), "--write"]), 0)
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-qm", "base")

    def tearDown(self):
        self.tmp.cleanup()

    def check(self):
        return pf.main(["--root", str(self.repo), "--base", "HEAD"])

    def diagnostics(self):
        """(exit code, stderr) of the check."""
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            return self.check(), err.getvalue()

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

    def test_new_simp_set_fails(self):
        (self.repo / "New.lean").write_text("register_simp_attr my_set\n")
        code, err = self.diagnostics()
        self.assertEqual(code, 1)
        self.assertIn("New: new simp-set declaration `my_set`", err)

    def test_new_attribute_initializer_fails(self):
        (self.repo / "New.lean").write_text('initialize tagExt : TagAttribute ← registerTagAttribute `my_tag "d"\n')
        code, err = self.diagnostics()
        self.assertEqual(code, 1)
        self.assertIn("New: new attribute declaration `my_tag`", err)

    def test_new_registry_in_an_existing_module_fails(self):
        (self.repo / "Attr.lean").write_text((self.repo / "Attr.lean").read_text() + "register_label_attr my_label\n")
        code, err = self.diagnostics()
        self.assertEqual(code, 1)
        self.assertIn("Attr: new attribute declaration `my_label`", err)

    def test_applying_a_registry_passes(self):
        (self.repo / "New.lean").write_text("@[base_attr] theorem t : True := trivial\n"
                                            "attribute [base_attr] foo\nattribute [local base_set] bar\n"
                                            "example : True := by simp [base_set]\n"
                                            "simproc [base_set] reduceFoo (foo _) := fun e => pure .continue\n")
        self.assertEqual(pf.scan_registries((self.repo / "New.lean").read_text()), set())
        self.assertEqual(self.diagnostics(), (0, ""))

    def test_removed_registry_must_be_deleted_from_the_file(self):
        (self.repo / "Attr.lean").write_text("register_simp_attr base_set\n")
        code, err = self.diagnostics()
        self.assertEqual(code, 1)
        self.assertIn("attribute declaration `base_attr` (Attr) is gone; delete its entry", err)
        pf.main(["--root", str(self.repo), "--write"])  # the entry is deleted
        self.assertEqual(self.check(), 0)

    def test_registry_only_shrinks_unless_approved(self):
        (self.repo / "New.lean").write_text("register_simp_attr fsym_new\n")
        pf.main(["--root", str(self.repo), "--write"])
        code, err = self.diagnostics()
        self.assertEqual(code, 1)
        self.assertIn("is not in HEAD's file", err)
        git(self.repo, "checkout", "--", pf.FILE)
        pf.main(["--root", str(self.repo), "--write", "--approve", "coordinator, 2026-10-16, test"])
        entry = next(e for e in json.loads((self.repo / pf.FILE).read_text())["registries"]
                     if e["registry"] == "fsym_new")
        self.assertEqual(entry, {"registry": "fsym_new", "kind": "simp-set", "module": "New", "status": "target",
                                 "approved": "coordinator, 2026-10-16, test"})
        self.assertEqual(self.check(), 0)

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
