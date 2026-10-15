#!/usr/bin/env python3
"""D03 premise reference regressions: the real index and synthetic fail-closed fixtures."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import textwrap
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("premises", ROOT / "scripts/premises.py")
premises = importlib.util.module_from_spec(SPEC)
sys.modules["premises"] = premises
SPEC.loader.exec_module(premises)
MARKERS_SPEC = importlib.util.spec_from_file_location("premise_markers", ROOT / "scripts/premise_markers.py")
markers = importlib.util.module_from_spec(MARKERS_SPEC)
MARKERS_SPEC.loader.exec_module(markers)

CATALOG = """\
# Fixture premises

{entries}

## Reports

| Report | Premises |
|---|---|
| Fixture audit | TRU-01 |
"""

ENTRY = """\
<a id="{lower}"></a>
### {pid} — {title}

- Kind: trusted.
- Statement: fixture premise {pid}.
- Derived from: fixture rules.
- Sources: [fixture](fixture.md).
"""

TITLES = {"PRF-01": "Legacy", "PRF-02": "Recorded", "PRF-03": "Gate", "ASM-01": "Opaque asm",
          "ASM-02": "Asm hypothesis", "THR-01": "Scheduler", "SEM-01": "Semantics",
          "EXT-02": "Axiom", "TRU-01": "Kernel", "TRU-02": "Translator",
          "ALC-09": "Caller allocator", "IOM-01": "Caller Io", "ORD-06": "Memory-model adequacy",
          "MTH-05": "No libc"}

PROFILE = ('-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee",'
           '"profile":{"name":"abi64-le-v1","schema":12}}\n')


def fixture_config():
    return {
        "schema_version": 1, "catalog": "docs/premises.md", "index": "docs/premise-index.md",
        "universal": ["TRU-01"], "theorem_roots": ["Proofs"], "import_roots": [],
        "excluded": {"Proofs/Bad/": "negative fixture"},
        "generated_imports": {"Fresh.Gen": "gate-time"},
        "generated_premises": ["TRU-02"],
        "generated_markers": {"ALC-09": "allocator parameter", "IOM-01": "Io parameter"},
        "profiles": {"absent": "PRF-01", "legacy-abi64-le": "PRF-01", "abi64-le-v1": "PRF-02",
                     "gate-time": "PRF-03"},
        "float_semantics": {"ieee": []}, "admissions": {"no-libc": ["MTH-05"]},
        "source_axiom": ["EXT-02"],
        "runtime_modules": {"ZigLean.Basic": ["SEM-01"], "ZigLean.Sched": ["THR-01"]},
        "rules": [{"premise": "ASM-01", "scope": "closure", "pattern": "(?:^|\\.)airAsm_[0-9]+$"},
                  {"premise": "ASM-02", "scope": "statement", "pattern": "(?:^|\\.)airAsm_[0-9]+$"}],
        "implies": {"ASM-02": ["ASM-01"], "TRU-02": ["SEM-01"], "THR-01": ["ORD-06"]},
        "memory_model": {"premise": "ORD-06", "concurrency": ["THR-01"],
                         "targets": {"x86_64-linux": {"hardware": "x86-TSO", "argument": "fixture",
                                                      "evidence": ["ZigLean/Sched.lean"]}},
                         "unqualified": {"wasm32-freestanding": "fixture"}},
    }


class Fixture:
    def __init__(self, directory: Path):
        self.root = directory
        self.config = fixture_config()
        self.titles = dict(TITLES)
        self.files = {
            "ZigLean/Basic.lean": """\
                namespace Zig
                def Result (α : Type) := Option α
                def add (a b : Nat) : Result Nat := some (a + b)
                end Zig
                """,
            "ZigLean/Sched.lean": """\
                import ZigLean.Basic
                namespace Zig.Sched
                def run (n : Nat) : Nat := n
                end Zig.Sched
                """,
            "Proofs/Asm/Gen.lean": """\
                import ZigLean.Basic
                namespace Asm
                opaque airAsm_17 (x : Nat) : Nat
                def wrap (x : Nat) : Zig.Result Nat := some (airAsm_17 x)
                def plain (x : Nat) : Zig.Result Nat := Zig.add x 1
                end Asm
                """,
            "Proofs/Asm/Proofs.lean": """\
                import Proofs.Asm.Gen
                open Asm
                -- wrap uses airAsm_17 and Sched.run, but comments are not dependencies.
                theorem wrap_spec (h : ∀ x, airAsm_17 x = x) (x : Nat) : wrap x = some x := by
                  simp [wrap, h]
                theorem plain_spec (x : Nat) : plain x = some (x + 1) := rfl
                theorem pure_fact (n : Nat) : n + 0 = n := rfl
                theorem via_helper (x : Nat) : True := by
                  have := plain_spec x
                  trivial
                example : 1 + 1 = 2 := rfl
                """,
            "Proofs/Conc/Proofs.lean": """\
                import ZigLean.Sched
                open Zig
                theorem run_id (n : Nat) : Sched.run n = n := rfl
                """,
            "Proofs/Bad/Proofs.lean": """\
                axiom bad : False
                theorem uses_bad : False := bad
                """,
        }

    def write(self):
        for rel, text in self.files.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(textwrap.dedent(text))
        (self.root / "assurance").mkdir(exist_ok=True)
        (self.root / "assurance/premises.json").write_text(json.dumps(self.config, indent=2))
        entries = "\n".join(ENTRY.format(lower=p.lower(), pid=p, title=t) for p, t in self.titles.items())
        (self.root / "docs").mkdir(exist_ok=True)
        (self.root / "docs/premises.md").write_text(CATALOG.format(entries=entries))

    def check(self, write=False):
        self.write()
        return premises.check(self.root, write=write)


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fixture = Fixture(Path(self.temp.name))

    def tearDown(self):
        self.temp.cleanup()

    def written(self):
        errors, entries = self.fixture.check(write=True)
        self.assertEqual(errors, [])
        return {e["theorem"]: e for e in entries}

    def test_mechanical_derivation(self):
        entries = self.written()
        wrap = entries["wrap_spec"]["premises"]
        self.assertEqual(wrap, ["PRF-01", "ASM-01", "ASM-02", "SEM-01", "TRU-01", "TRU-02"])
        # Transitively through a generated function, not through the statement.
        self.assertEqual(entries["plain_spec"]["premises"], ["PRF-01", "SEM-01", "TRU-01", "TRU-02"])
        self.assertEqual(entries["via_helper"]["premises"], ["PRF-01", "SEM-01", "TRU-01", "TRU-02"])
        self.assertEqual(entries["pure_fact"]["premises"], ["TRU-01"])
        self.assertEqual(entries["example@L11"]["premises"], ["TRU-01"])
        self.assertEqual(entries["run_id"]["premises"], ["THR-01", "ORD-06", "SEM-01", "TRU-01"])
        self.assertNotIn("uses_bad", entries, "excluded fixtures are not indexed")
        self.assertEqual(premises.check(self.fixture.root)[0], [])

    def test_statement_rule_ignores_proof_and_comments(self):
        self.fixture.files["Proofs/Asm/Proofs.lean"] = """\
            import Proofs.Asm.Gen
            open Asm
            /- airAsm_17 in a block comment -/
            theorem body_only (x : Nat) : True := by
              have := airAsm_17 x -- airAsm_17
              trivial
            """
        entries = self.written()
        self.assertIn("ASM-01", entries["body_only"]["premises"])
        self.assertNotIn("ASM-02", entries["body_only"]["premises"])
        self.assertEqual(entries["body_only"]["via"]["ASM-01"], ["closure token Asm.airAsm_17"])

    def test_tactic_applies_runtime_modules(self):
        """A tactic token reaches the runtime modules its lemmas live in (`tactic_modules`)."""
        self.fixture.files["Proofs/Tac/Proofs.lean"] = """\
            import ZigLean.Sched
            theorem by_tactic : True := by fsym
            theorem by_hand : True := trivial
            """
        self.fixture.config["tactic_modules"] = {"fsym": ["ZigLean.Sched"]}
        entries = self.written()
        self.assertEqual(entries["by_tactic"]["premises"], ["THR-01", "ORD-06", "SEM-01", "TRU-01"])
        self.assertEqual(entries["by_tactic"]["via"]["THR-01"], ["runtime module ZigLean.Sched"])
        self.assertEqual(entries["by_hand"]["premises"], ["TRU-01"])
        self.fixture.config["tactic_modules"] = {"fsym": ["ZigLean.Missing"]}
        self.assertIn("tactic_modules.fsym names ZigLean.Missing, which is not a mapped runtime module",
                      self.fixture.check()[0])

    def test_unfolding_a_runtime_definition_exposes_its_body(self):
        self.fixture.files["ZigLean/Basic.lean"] = """\
            namespace Zig
            def Result (α : Type) := Option α
            def add (a b : Nat) : Result Nat := some (a + b)
            def exposes (x : Nat) : Nat := airAsm_5 x
            inductive Err where
              | airAsm_6
            end Zig
            """
        self.fixture.files["Proofs/Unf/Proofs.lean"] = """\
            import ZigLean.Basic
            theorem unfolds : True := by simp only [Zig.exposes]
            theorem only_calls (x : Nat) : Zig.add x 1 = Zig.add x 1 := rfl
            theorem names_type (e : Zig.Err) : e = e := rfl
            def wraps (x : Nat) : Nat := Zig.exposes x
            theorem applies_in_def : wraps 1 = wraps 1 := rfl
            theorem applies_in_statement : Zig.exposes 1 = Zig.exposes 1 := rfl
            """
        entries = self.written()
        self.assertEqual(entries["unfolds"]["via"]["ASM-01"], ["closure token airAsm_5"])
        self.assertNotIn("ASM-01", entries["only_calls"]["premises"])
        # Naming an inductive type does not unfold its constructors.
        self.assertNotIn("ASM-01", entries["names_type"]["premises"])
        # A definition that applies it, or a statement that names it, keeps the constant.
        self.assertNotIn("ASM-01", entries["applies_in_def"]["premises"])
        self.assertNotIn("ASM-01", entries["applies_in_statement"]["premises"])

    def test_extern_binding_premise(self):
        """A model binding's extern premise follows the use of one of its declarations."""
        binding = {"symbol": "extern:ext_visit", "trust": "assumed", "proof": None, "implementation": "Model.visit",
                   "contract": "Model.contract", "extern": {"library": None, "premise": "EXT-03"}}
        self.fixture.titles["EXT-03"] = "Extern"
        self.fixture.config["implies"]["EXT-03"] = ["SEM-01"]
        self.fixture.files["Proofs/Ext/Gen.lean"] = (
            PROFILE + "-- air2lean-models: " + json.dumps({"schema": 1, "assumptions": [], "bindings": [binding]})
            + "\nnamespace Ext\naxiom air2lean_model_0_evidence : True\ndef other : Nat := 1\nend Ext\n")
        self.fixture.files["Proofs/Ext/Proofs.lean"] = """\
            import Proofs.Ext.Gen
            theorem uses_evidence : True := Ext.air2lean_model_0_evidence
            theorem uses_other : Ext.other = 1 := rfl
            """
        entries = self.written()
        self.assertIn("EXT-03", entries["uses_evidence"]["premises"])
        self.assertNotIn("EXT-03", entries["uses_other"]["premises"])

    def test_implicit_dependencies(self):
        """Field notation on typed binders, unique `.ctor` names and instances resolve in source."""
        self.fixture.files["ZigLean/Basic.lean"] += """\
            namespace Zig
            class Enc (α : Type) where size : Nat
            def Tid := Nat
            end Zig
            """
        self.fixture.files["ZigLean/Sched.lean"] = """\
            import ZigLean.Basic
            namespace Zig.Sched
            def run (n : Nat) : Nat := n
            structure Box where n : Nat
            def Box.get (b : Box) : Nat := b.n
            inductive Mode where | strict | lax
            inductive Phase where | done
            instance : Zig.Enc Zig.Tid where size := 8
            end Zig.Sched
            """
        self.fixture.files["Proofs/Conc/Field.lean"] = """\
            import ZigLean.Sched
            inductive Local where | done
            theorem field_binder (b : Zig.Sched.Box) : b.get = b.get := rfl
            section
            variable (c : Zig.Sched.Box)
            theorem field_variable : c.get = c.get := rfl
            end
            theorem field_unbound : x.get = x.get := rfl
            structure Holder where n : Nat
            def Holder.run (h : Holder) : Nat := Zig.Sched.run h.n
            def holder0 : Holder := ⟨0⟩
            theorem field_constant : holder0.run = holder0.run := rfl
            theorem dot_unique : True := by have := (.lax, 1); trivial
            theorem dot_ambiguous : True := by have := (.done, 1); trivial
            open Zig in
            theorem instance_used : Enc.size Tid = 8 := rfl
            open Zig in
            theorem instance_unused : Enc.size Nat = 8 := rfl
            """
        entries = self.written()
        for name in ("field_binder", "field_variable", "field_constant", "dot_unique", "instance_used"):
            self.assertIn("THR-01", entries[name]["premises"], name)
        for name in ("field_unbound", "dot_ambiguous", "instance_unused"):
            self.assertNotIn("THR-01", entries[name]["premises"], name)
        self.assertIn("SEM-01", entries["instance_unused"]["premises"])

    def test_ambient_variable_type_arguments_reach_the_source_closure(self):
        self.fixture.files["Proofs/Ambient/Gen.lean"] = "namespace Ambient\ndef target : Nat := 1\nend Ambient\n"
        self.fixture.files["Proofs/Ambient/Proofs.lean"] = """\
            import Proofs.Ambient.Gen
            namespace Ambient
            structure Proto (n : Nat) where value : Nat
            section
            variable (P : Proto target)
            theorem ambient : P.value = P.value := rfl
            end
            theorem outside : True := trivial
            end Ambient
            """
        entries = self.written()
        self.assertIn("TRU-02", entries["Ambient.ambient"]["premises"])
        self.assertNotIn("TRU-02", entries["Ambient.outside"]["premises"])

    def test_nested_field_result_type_reaches_runtime_rule(self):
        self.fixture.files["ZigLean/Sched.lean"] = """\
            import ZigLean.Basic
            namespace Zig.Sched
            structure Word where value : Nat
            def Word.In (w : Word) : Prop := True
            end Zig.Sched
            """
        self.fixture.files["Proofs/Field/Proofs.lean"] = """\
            import ZigLean.Sched
            structure Layout where value : Nat
            def Layout.word (lo : Layout) : Zig.Sched.Word := ⟨lo.value⟩
            theorem nested (lo : Layout) : lo.word.In := trivial
            """
        entries = self.written()
        self.assertIn("THR-01", entries["nested"]["premises"])

    def test_stack_error_constructor_is_inert_but_stack_operations_retain_premise(self):
        config = premises.load_config(ROOT / "assurance/premises.json")
        patterns = [r["regex"] for r in config["rules"] if r["premise"] == "STK-01"]
        self.assertFalse(any(p.search("Zig.Error.stackOverflow") for p in patterns))
        for name in ("Zig.allocStack", "Zig.alloc", "Zig.enterFrame", "partial_fixpoint"):
            self.assertTrue(any(p.search(name) for p in patterns), name)

    def test_profile_header_and_gate_import(self):
        self.fixture.files["Proofs/Asm/Gen.lean"] = PROFILE + textwrap.dedent(self.fixture.files["Proofs/Asm/Gen.lean"])
        self.fixture.files["Proofs/Fresh/Proofs.lean"] = """\
            import Fresh.Gen
            theorem fresh_spec : True := trivial
            """
        entries = self.written()
        self.assertIn("PRF-02", entries["plain_spec"]["premises"])
        self.assertNotIn("PRF-01", entries["plain_spec"]["premises"])
        self.assertIn("PRF-03", entries["fresh_spec"]["premises"])
        self.assertIn("TRU-02", entries["fresh_spec"]["premises"])

    def marked(self, marker='{"ALC-09":[0]}', before="def wrap"):
        gen = textwrap.dedent(self.fixture.files["Proofs/Asm/Gen.lean"])
        self.fixture.files["Proofs/Asm/Gen.lean"] = gen.replace(
            before, f"-- air2lean-premises: {marker}\n{before}", 1)

    def test_interface_marker_reaches_theorems(self):
        """W1: a generated def's Allocator/Io parameter is a premise of every theorem reaching it."""
        self.marked('{"ALC-09":[0],"IOM-01":[1]}')
        entries = self.written()
        self.assertIn("ALC-09", entries["wrap_spec"]["premises"])
        self.assertIn("IOM-01", entries["wrap_spec"]["premises"])
        self.assertEqual(entries["wrap_spec"]["via"]["ALC-09"], ["marker on Asm.wrap (parameters 0)"])
        # A sibling definition without a marker, and theorems not reaching `wrap`, stay clean.
        for name in ("plain_spec", "via_helper", "pure_fact"):
            self.assertNotIn("ALC-09", entries[name]["premises"], name)

    def test_interface_marker_fails_closed(self):
        for marker, before, message in [
                ('{"ALC-09":[]}', "def wrap", "malformed air2lean-premises marker"),
                ('{"ALC-09":[true]}', "def wrap", "malformed air2lean-premises marker"),
                ('ALC-09', "def wrap", "malformed air2lean-premises marker"),
                ('{"ASM-01":[0]}', "def wrap", "marker names ASM-01, not a generated_markers premise"),
                ('{"ALC-09":[0]}', "opaque airAsm_17", "air2lean-premises marker does not precede a def"),
                ('{"ALC-09":[0]}', "end Asm", "air2lean-premises marker does not precede a def")]:
            with self.subTest(marker=marker, before=before):
                temp = tempfile.TemporaryDirectory()
                self.addCleanup(temp.cleanup)
                self.fixture = Fixture(Path(temp.name))
                self.marked(marker, before)
                errors, _ = self.fixture.check(write=True)
                self.assertTrue(any(message in e for e in errors), errors)

    def test_admission_is_a_premise(self):
        """An `--assume-no-libc` translation: every theorem over it lists MTH-05."""
        self.fixture.files["Proofs/Asm/Gen.lean"] = PROFILE.replace(
            '"float_semantics":"ieee"', '"admission":"no-libc","float_semantics":"ieee"') + \
            textwrap.dedent(self.fixture.files["Proofs/Asm/Gen.lean"])
        entries = self.written()
        self.assertIn("MTH-05", entries["plain_spec"]["premises"])
        self.assertIn("PRF-02", entries["plain_spec"]["premises"])
        self.assertNotIn("MTH-05", entries["pure_fact"]["premises"])

    def test_example_translate_args_admission(self):
        """A committed (headerless) example translation takes the opt-ins of its translate.args."""
        self.fixture.files["examples/asm/translate.args"] = "--float-semantics compiler-rt --assume-no-libc\n"
        entries = self.written()
        self.assertIn("MTH-05", entries["plain_spec"]["premises"])
        self.assertIn("PRF-01", entries["plain_spec"]["premises"])

    def test_unmapped_admission_fails(self):
        self.fixture.files["Proofs/Asm/Gen.lean"] = PROFILE.replace(
            '"float_semantics":"ieee"', '"admission":"no-libc,new-opt-in","float_semantics":"ieee"') + \
            textwrap.dedent(self.fixture.files["Proofs/Asm/Gen.lean"])
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("admission 'new-opt-in' has no premise mapping" in e for e in errors), errors)

    def test_unknown_profile_fails(self):
        self.fixture.files["Proofs/Asm/Gen.lean"] = PROFILE.replace("abi64-le-v1", "wasm32") + \
            textwrap.dedent(self.fixture.files["Proofs/Asm/Gen.lean"])
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("profile 'wasm32' has no premise mapping" in e for e in errors), errors)

    def test_source_axiom(self):
        self.fixture.config["excluded"] = {}
        entries = self.written()
        self.assertIn("EXT-02", entries["uses_bad"]["premises"])

    def test_unmapped_runtime_module_fails(self):
        self.fixture.files["ZigLean/Timer.lean"] = "namespace Zig\ndef now : Nat := 0\nend Zig\n"
        errors, _ = self.fixture.check(write=True)
        self.assertIn("runtime module ZigLean.Timer has declarations but no premise mapping", errors)

    def test_missing_runtime_module_fails(self):
        self.fixture.config["runtime_modules"]["ZigLean.Gone"] = ["SEM-01"]
        errors, _ = self.fixture.check(write=True)
        self.assertIn("runtime_modules names missing module ZigLean.Gone", errors)

    def test_concurrency_theorem_without_adequacy_premise_fails(self):
        """C12: a concurrency claim never omits the memory-model adequacy premise."""
        del self.fixture.config["implies"]["THR-01"]
        errors, _ = self.fixture.check(write=True)
        self.assertIn("Proofs/Conc/Proofs.lean: run_id makes a concurrency claim without the "
                      "memory-model adequacy premise ORD-06", errors)

    def test_concurrency_report_without_adequacy_premise_fails(self):
        self.fixture.titles["THR-01"] = "Scheduler"
        self.fixture.write()
        catalog = self.fixture.root / "docs/premises.md"
        catalog.write_text(catalog.read_text() + "| Fixture schedule search | THR-01 |\n")
        errors, _ = premises.check(self.fixture.root, write=True)
        self.assertIn("report 'Fixture schedule search' rests on a concurrency premise but does not list ORD-06",
                      errors)

    def test_adequacy_evidence_must_exist(self):
        self.fixture.config["memory_model"]["targets"]["x86_64-linux"]["evidence"] = ["tests/gone.zig"]
        errors, _ = self.fixture.check(write=True)
        self.assertIn("memory_model.targets.x86_64-linux: evidence tests/gone.zig does not exist", errors)

    def test_undefined_premise_fails(self):
        self.fixture.config["rules"].append({"premise": "ZZZ-99", "scope": "closure", "pattern": "x"})
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("undefined premise ZZZ-99" in e for e in errors), errors)

    def test_undefined_catalog_mention_fails(self):
        self.fixture.titles["TRU-02"] = "Translator, see QQQ-01"
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("undefined premise ID QQQ-01" in e for e in errors), errors)

    def test_orphan_premise_fails(self):
        self.fixture.titles["TMR-01"] = "Unused"
        errors, _ = self.fixture.check(write=True)
        self.assertIn("premise TMR-01 is referenced by no rule, runtime module or report", errors)

    def test_catalog_requires_fields_and_anchor(self):
        self.fixture.write()
        path = self.fixture.root / "docs/premises.md"
        text = path.read_text().replace("- Sources: [fixture](fixture.md).\n", "", 1)
        path.write_text(text.replace('<a id="tru-01"></a>\n', ""))
        _, _, errors = premises.load_catalog(path)
        self.assertTrue(any("lacks '- Sources:'" in e for e in errors), errors)
        self.assertTrue(any("TRU-01 lacks anchor" in e for e in errors), errors)

    def test_stale_index_fails(self):
        self.written()
        self.fixture.files["Proofs/Asm/Proofs.lean"] += "theorem added : True := trivial\n"
        errors, _ = self.fixture.check()
        self.assertIn("docs/premise-index.md is stale; run python3 scripts/premises.py write", errors)

    def test_unresolved_import_fails(self):
        self.fixture.files["Proofs/Conc/Proofs.lean"] = "import Missing.Module\n" + \
            textwrap.dedent(self.fixture.files["Proofs/Conc/Proofs.lean"])
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("import Missing.Module is unresolved" in e for e in errors), errors)

    def test_duplicate_theorem_fails(self):
        self.fixture.files["Proofs/Conc/Proofs.lean"] += "theorem run_id : True := trivial\n"
        errors, _ = self.fixture.check(write=True)
        self.assertTrue(any("duplicate theorem run_id" in e for e in errors), errors)

    def test_cli_exit_codes(self):
        self.written()
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(premises.main(["--root", str(self.fixture.root), "check"]), 0)
            (self.fixture.root / "docs/premise-index.md").write_text("stale\n")
            self.assertEqual(premises.main(["--root", str(self.fixture.root), "check"]), 1)
            (self.fixture.root / "assurance/premises.json").write_text("{}")
            self.assertEqual(premises.main(["--root", str(self.fixture.root), "check"]), 2)

    def test_explain(self):
        self.written()
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(premises.main(["--root", str(self.fixture.root), "explain", "wrap_spec"]), 0)
        self.assertIn("ASM-02: statement token airAsm_17", out.getvalue())


class CompiledTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fixture = Fixture(Path(self.temp.name))
        self.fixture.check(write=True)
        self.config = premises.load_config(self.fixture.root / "assurance/premises.json")

    def tearDown(self):
        self.temp.cleanup()

    @staticmethod
    def node(name, module, kind="definition", deps=()):
        return {"name": name, "module": module, "kind": kind, "dependencies": list(deps)}

    def report(self, extra_dep=None, axioms=()):
        deps = ["Asm.wrap"] + ([extra_dep] if extra_dep else [])
        nodes = [self.node("wrap_spec", "Proofs.Asm.Proofs", "theorem", deps),
                 self.node("Asm.wrap", "Proofs.Asm.Gen", deps=["Asm.airAsm_17", "Zig.Result"]),
                 self.node("Asm.airAsm_17", "Proofs.Asm.Gen", "opaque"),
                 self.node("Zig.Result", "ZigLean.Basic", deps=["Zig.Inner"]),
                 self.node("Zig.Inner", "ZigLean.Sched"),
                 self.node("Zig.now", "ZigLean.Timer"),
                 self.node("Nat.add", "Init.Prelude"),
                 self.node("Zig.lemma", "ZigLean.Basic", "theorem")]
        return {"schema_version": 1, "status": "pass", "nodes": nodes,
                "theorems": [{"name": "wrap_spec", "module": "Proofs.Asm.Proofs", "axioms": list(axioms)},
                             {"name": "Zig.lemma", "module": "ZigLean.Basic", "axioms": []}]}

    def test_compiled_closure_stops_at_runtime(self):
        result = premises.compiled(self.report(), self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "pass")
        self.assertEqual(result["runtime_theorems_skipped"], 1)
        theorem = result["theorems"][0]
        # Zig.Result's body reaches ZigLean.Sched, but runtime bodies are not followed.
        self.assertEqual(theorem["premises"], ["PRF-01", "ASM-01", "SEM-01", "TRU-01", "TRU-02"])

    def precise_report(self, used=False):
        self.config["declaration_carriers"] = {
            "THR-01": {"modules": ["ZigLean.Sched"], "declarations": [],
                       "namespaces": ["Zig.Sched.run"], "reason": "fixture scheduler primitive"}}
        report = self.report("Zig.helper")
        report["nodes"].append(self.node("Zig.helper", "ZigLean.Sched",
                                         deps=["Zig.Sched.run.eq_1"] if used else []))
        report["nodes"] += [self.node("Zig.Sched.run.eq_1", "ZigLean.Basic", deps=["Zig.Sched.run"]),
                            self.node("Zig.Sched.run", "ZigLean.Sched")]
        return report

    def test_precise_premises_are_a_subset_of_module_baseline(self):
        result = premises.compiled(self.precise_report(), self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "pass")
        for theorem in result["theorems"]:
            self.assertLessEqual(set(theorem["premises"]), set(theorem["module_premises"]))
        self.assertEqual(result["theorems"][0]["dropped"], ["THR-01", "ORD-06"])
        self.assertEqual(result["drop_counts"], {"THR-01": 1, "ORD-06": 1})

    def test_used_carrier_remains_through_runtime_body_and_equation(self):
        result = premises.compiled(self.precise_report(used=True), self.fixture.root, self.config, None)
        theorem = result["theorems"][0]
        self.assertIn("THR-01", theorem["premises"])
        self.assertIn("ORD-06", theorem["premises"])
        self.assertEqual(theorem["dropped"], [])
        self.assertIn("declaration Zig.Sched.run", theorem["via"]["THR-01"])

    def test_native_target_and_pointer_helpers_retain_real_carriers(self):
        config = premises.load_config(ROOT / "assurance/premises.json")
        for pid, helper_module, carrier, primitive in (
                ("OSM-01", "ZigLean.Sep.Full.Mmap", "Zig.Os.Target", "ZigLean.Os.Mmap"),
                ("ORD-05", "ZigLean.Sep.Full.AtomicPtr", "Zig.Mem.ptrAddr?", "ZigLean.Mem.AtomicPtr")):
            report = self.report("Zig.helper")
            report["nodes"] += [self.node("Zig.helper", helper_module, deps=[carrier]),
                                self.node(carrier, primitive)]
            result = premises.compiled(report, ROOT, config, None)
            self.assertEqual(result["status"], "pass")
            self.assertIn(pid, result["theorems"][0]["premises"])
            self.assertIn(f"declaration {carrier}", result["theorems"][0]["via"][pid])

    def test_real_primitive_model_families_have_complete_carrier_roots(self):
        config = premises.load_config(ROOT / "assurance/premises.json")
        for pid, rel in (("OSM-01", "ZigLean/Os/Mmap.lean"), ("ORD-05", "ZigLean/Mem/AtomicPtr.lean")):
            model = premises.parse_file(ROOT / rel, ROOT)
            names = {d.name for d in model.decls if d.name and d.kind in
                     {"def", "abbrev", "class", "structure", "inductive"}}
            self.assertEqual(set(premises.declaration_hits(config, names)[pid]), names)

    def test_unreviewed_runtime_module_keeps_fallback(self):
        report = self.precise_report()
        self.config["runtime_modules"]["ZigLean.Other"] = ["THR-01"]
        report["nodes"][0]["dependencies"].append("Zig.other")
        report["nodes"].append(self.node("Zig.other", "ZigLean.Other"))
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertIn("THR-01", result["theorems"][0]["premises"])
        self.assertIn("runtime module ZigLean.Other", result["theorems"][0]["via"]["THR-01"])

    def test_precise_walk_rejects_a_missing_runtime_body_dependency(self):
        report = self.precise_report()
        report["nodes"][1]["dependencies"].append("Missing.runtime")
        with self.assertRaisesRegex(ValueError, "incomplete declaration graph"):
            premises.compiled(report, self.fixture.root, self.config, None)

    def test_namespace_carriers_observe_component_boundaries(self):
        self.precise_report()
        hits = premises.declaration_hits(self.config, {"Zig.Sched.runner", "Else.Zig.Sched.run"})
        self.assertEqual(hits["THR-01"], [])
        self.assertEqual(premises.declaration_hits(self.config, {"Zig.Sched.run.eq_1"})["THR-01"],
                         ["Zig.Sched.run.eq_1"])

    def test_carrier_reachability_handles_cycles_and_private_names(self):
        report = self.precise_report()
        report["nodes"] += [dict(self.node("_private.Fixture.0.Zig.Sched.run", "ZigLean.Sched"),
                                  user_name="Zig.Sched.run")]
        helper = next(n for n in report["nodes"] if n["name"] == "Zig.helper")
        helper["dependencies"] += ["Zig.cycle"]
        report["nodes"].append(self.node("Zig.cycle", "ZigLean.Sched",
                                         deps=["Zig.helper", "_private.Fixture.0.Zig.Sched.run"]))
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "pass")
        self.assertIn("THR-01", result["theorems"][0]["premises"])

    def test_coverage_edit_fails_closed(self):
        report = self.precise_report()
        path = self.fixture.root / "ZigLean/Sched.lean"
        self.config["carrier_coverage"] = {
            "ZigLean/Sched.lean": premises.hashlib.sha256(path.read_bytes()).hexdigest()}
        self.assertEqual(premises.compiled(report, self.fixture.root, self.config, None)["status"], "pass")
        path.write_text(path.read_text() + "\ndef anotherNativeOperation := 0\n")
        changed = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertEqual(changed["status"], "fail")
        self.assertIn("coverage is stale", changed["errors"][0])

    def test_refinement_retains_source_fallback_without_checked_theorem(self):
        from unittest.mock import patch
        repo = premises.load_repository(self.fixture.root, self.config)
        entries, _ = premises.build_index(repo)
        old = {e["theorem"]: list(e["premises"]) for e in entries}
        with patch.object(premises, "kernel_reports", return_value=[]):
            self.assertEqual(premises.refine_index(repo, entries), [])
        for entry in entries:
            self.assertEqual(entry["premises"], old[entry["theorem"]])
            self.assertIn("source fallback", entry["derivation"])

    def test_cached_audit_requires_matching_inputs_bytes_and_freshness(self):
        from unittest.mock import patch
        repo = premises.load_repository(self.fixture.root, self.config)
        directory = self.fixture.root / ".lake/premise-index"
        directory.mkdir(parents=True)
        binding = "0" * 64
        report = dict(self.report(), kernel_replay={"status": "pass"},
                      freshness={"toolchain_runtime_sha256": binding},
                      extractor={"toolchain_runtime_sha256": binding})
        report_path = directory / "shipped.json"
        report_path.write_text(json.dumps(report))
        manifest = {"inputs": "current", "reports": [{"report": "shipped.json", "sources": {},
                    "sha256": premises.hashlib.sha256(report_path.read_bytes()).hexdigest()}]}
        (directory / "manifest.json").write_text(json.dumps(manifest))
        with patch.object(premises, "kernel_inputs", return_value="current"), \
                patch("assumptions.artifact_batch") as batch, \
                patch.object(premises.subprocess, "run", side_effect=RuntimeError("must rebuild")) as run:
            fresh = batch.return_value.__enter__.return_value
            self.assertEqual(list(premises.kernel_reports(repo)), [(report, {})])
            fresh.assert_called_once_with(report)
            run.assert_not_called()
            report_path.write_text(json.dumps(dict(report, status="fail")))
            with self.assertRaisesRegex(RuntimeError, "must rebuild"):
                list(premises.kernel_reports(repo))
            self.assertFalse((directory / "manifest.json").exists())
        report_path.write_text(json.dumps(report))
        (directory / "manifest.json").write_text(json.dumps(manifest))
        with patch.object(premises, "kernel_inputs", return_value="changed"), \
                patch.object(premises.subprocess, "run", side_effect=RuntimeError("must rebuild")):
            with self.assertRaisesRegex(RuntimeError, "must rebuild"):
                list(premises.kernel_reports(repo))

    def test_cached_audit_without_runtime_binding_is_regenerated(self):
        from unittest.mock import patch
        repo = premises.load_repository(self.fixture.root, self.config)
        directory = self.fixture.root / ".lake/premise-index"
        directory.mkdir(parents=True)
        report = dict(self.report(), kernel_replay={"status": "pass"})
        path = directory / "shipped.json"
        path.write_text(json.dumps(report))
        manifest = {"inputs": "current", "reports": [{"report": "shipped.json", "sources": {},
                    "sha256": premises.file_sha256(path)}]}
        (directory / "manifest.json").write_text(json.dumps(manifest))
        with patch.object(premises, "kernel_inputs", return_value="current"), \
                patch.object(premises.subprocess, "run", side_effect=RuntimeError("must rebuild")):
            with self.assertRaisesRegex(RuntimeError, "must rebuild"):
                list(premises.kernel_reports(repo))
            self.assertFalse((directory / "manifest.json").exists())
    def test_cached_audit_rehashes_actual_compiled_artifacts(self):
        from unittest.mock import patch
        repo = premises.load_repository(self.fixture.root, self.config)
        directory = self.fixture.root / ".lake/premise-index"
        directory.mkdir(parents=True)
        olean = directory / "Fixture.olean"
        olean.write_bytes(b"checked fixture artifact")
        source = self.fixture.root / "ZigLean/Basic.lean"
        toolchain = self.fixture.root / "toolchain"
        (toolchain / "bin").mkdir(parents=True)
        for name in ("lean", "leanchecker"):
            (toolchain / "bin" / name).write_bytes(name.encode())
        binding = premises.toolchain_runtime_sha256(toolchain)
        report = dict(self.report(), kernel_replay={"status": "pass"}, freshness={
            "toolchain_runtime_sha256": binding,
            "lake_trace_check": {"status": "up-to-date"}, "artifacts": [{"module": "Fixture",
                "olean": str(olean), "olean_sha256": premises.file_sha256(olean),
                "source": str(source), "source_sha256": premises.file_sha256(source)}]},
            extractor={"toolchain_runtime_sha256": binding})
        path = directory / "shipped.json"
        path.write_text(json.dumps(report))
        manifest = {"inputs": "current", "reports": [{"report": "shipped.json", "sources": {},
                    "sha256": premises.file_sha256(path)}]}
        (directory / "manifest.json").write_text(json.dumps(manifest))
        with patch.object(premises, "kernel_inputs", return_value="current"), \
                patch("assumptions.lake_env", return_value=str(toolchain)), \
                patch.object(premises.subprocess, "run", side_effect=RuntimeError("must rebuild")):
            self.assertEqual(list(premises.kernel_reports(repo)), [(report, {})])
            olean.write_bytes(b"changed behind the report")
            with self.assertRaisesRegex(RuntimeError, "must rebuild"):
                list(premises.kernel_reports(repo))
            self.assertFalse((directory / "manifest.json").exists())
    def test_compiled_equation_lemma_belongs_to_its_definition(self):
        """Lean realizes `d.eq_1` in the module that unfolds `d`; it keeps `d`'s module."""
        report = self.report()
        report["nodes"] += [self.node("Zig.add", "ZigLean.Basic"),
                            self.node("Zig.add.eq_1", "ZigLean.Sched"),
                            self.node("Proofs.Asm.Proofs.eq_1", "Proofs.Asm.Proofs")]
        report["nodes"][0]["dependencies"].append("Zig.add.eq_1")
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertNotIn("THR-01", result["theorems"][0]["premises"])

    def test_compiled_concurrency_needs_adequacy_premise(self):
        report = self.report()
        report["theorems"].append({"name": "run_spec", "module": "Proofs.Conc.Proofs", "axioms": []})
        report["nodes"] += [self.node("run_spec", "Proofs.Conc.Proofs", "theorem", ["Zig.Inner"])]
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertIn("ORD-06", next(t for t in result["theorems"] if t["name"] == "run_spec")["premises"])
        del self.config["implies"]["THR-01"]
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertIn("run_spec makes a concurrency claim without the memory-model adequacy premise ORD-06",
                      result["errors"])

    def test_compiled_unmapped_module_and_axiom(self):
        result = premises.compiled(self.report("Zig.now", ["Fixture.extra"]), self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "fail")
        self.assertIn("wrap_spec: runtime module ZigLean.Timer has no premise mapping", result["errors"])
        self.assertIn("EXT-02", result["theorems"][0]["premises"])

    def test_compiled_source_gaps(self):
        source = [{"file": "Proofs/Asm/Proofs.lean", "theorem": "wrap_spec", "premises": ["TRU-01"]},
                  {"file": "tests/roadmap/x/Other.lean", "theorem": "wrap_spec", "premises": ["ASM-01"]}]
        result = premises.compiled(self.report(), self.fixture.root, self.config, source)
        self.assertEqual(result["source_gap_count"], 1)
        # A same-named theorem in another module does not mask the gap.
        self.assertIn("ASM-01", result["theorems"][0]["source_gaps"])
        self.assertEqual(result["theorems"][0]["gap_via"]["ASM-01"], ["closure token Asm.airAsm_17"])

    def test_compiled_private_names_use_user_name(self):
        self.config["rules"].append({"premise": "THR-01", "scope": "closure", "pattern": "Futex",
                                     "regex": premises.re.compile("Futex")})
        report = self.report("_private.Proofs.Futex.Proofs.0.helper")
        report["nodes"].append(dict(self.node("_private.Proofs.Futex.Proofs.0.helper", "Proofs.Futex.Proofs"),
                                    user_name="helper"))
        result = premises.compiled(report, self.fixture.root, self.config, None)
        # The module path inside the private prefix must not trigger a token rule.
        self.assertNotIn("THR-01", result["theorems"][0]["premises"])

    def test_compiled_unresolved_dependency_fails(self):
        report = self.report("Gone.decl")
        report["nodes"].append(self.node("Gone.decl", "", "unresolved"))
        result = premises.compiled(report, self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "fail")
        self.assertIn("wrap_spec: dependency Gone.decl is unresolved in the checked environment", result["errors"])

    def test_compiled_interface_marker(self):
        gen = self.fixture.root / "Proofs/Asm/Gen.lean"
        gen.write_text(gen.read_text().replace("def wrap", '-- air2lean-premises: {"IOM-01":[0]}\ndef wrap'))
        result = premises.compiled(self.report(), self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "pass")
        self.assertIn("IOM-01", result["theorems"][0]["premises"])

    def test_compiled_misplaced_marker_fails(self):
        gen = self.fixture.root / "Proofs/Asm/Gen.lean"
        gen.write_text(gen.read_text().replace("opaque airAsm_17", '-- air2lean-premises: {"ALC-09":[0]}\nopaque airAsm_17'))
        result = premises.compiled(self.report(), self.fixture.root, self.config, None)
        self.assertEqual(result["status"], "fail")
        self.assertTrue(any("marker does not precede a def" in e for e in result["errors"]), result["errors"])

    def test_caller_obligations_reach_users_transitively(self):
        gen = self.fixture.root / "Proofs/Asm/Gen.lean"
        gen.write_text(gen.read_text().replace("def wrap", '-- air2lean-premises: {"ALC-09":[0],"IOM-01":[0]}\ndef wrap'))
        report = self.report()
        report["theorems"].append({"name": "other", "module": "Proofs.Asm.Proofs", "axioms": []})
        report["nodes"].append(self.node("other", "Proofs.Asm.Proofs", "theorem", ["Asm.airAsm_17"]))
        found = markers.caller_obligations(report, self.fixture.root)
        self.assertEqual(found, {"wrap_spec": ["ALC-09", "IOM-01"]})
        named, _ = markers.definitions('namespace Ns\n-- air2lean-premises: {"ALC-09":[0]}\ndef «at» (p0 : X) := 0\n', "Gen.lean")
        self.assertEqual(named, {"Ns.at": {"ALC-09": [0]}})
        gen.write_text(gen.read_text().replace('{"ALC-09":[0],"IOM-01":[0]}', '{"ALC-09":[]}'))
        with self.assertRaisesRegex(ValueError, "malformed air2lean-premises marker"):
            markers.caller_obligations(report, self.fixture.root)
        gen.write_text(gen.read_text().replace('{"ALC-09":[]}\ndef wrap', '{"ALC-09":[0]}\n\ndef wrap'))
        with self.assertRaisesRegex(ValueError, "marker does not precede a def"):
            markers.caller_obligations(report, self.fixture.root)

    def test_compiled_rejects_error_report(self):
        with self.assertRaises(ValueError):
            premises.compiled({"schema_version": 1, "status": "error"}, self.fixture.root, self.config, None)
        report = self.report()
        report["status"] = "fail"
        with self.assertRaisesRegex(ValueError, "not a passing"):
            premises.compiled(report, self.fixture.root, self.config, None)
        report["status"] = "pass"
        report["nodes"][1]["dependencies"].append("Missing.decl")
        with self.assertRaises(ValueError):
            premises.compiled(report, self.fixture.root, self.config, None)


class RepositoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.errors, entries = premises.check(ROOT)
        cls.entries = {(e["file"], e["theorem"]): e for e in entries}
        cls.catalog, cls.reports, _ = premises.load_catalog(ROOT / "docs/premises.md")

    def premises_of(self, file, theorem):
        return self.entries[(file, theorem)]["premises"]

    def test_committed_index_is_current(self):
        self.assertEqual(self.errors, [])

    def test_required_categories(self):
        prefixes = {pid.split("-")[0] for pid in self.catalog}
        self.assertLessEqual({"PRF", "ALC", "THR", "ORD", "TMR", "MTH", "ASM", "TRU"}, prefixes)

    def test_every_shipped_proof_module_is_indexed(self):
        files = {f for f, _ in self.entries}
        for path in sorted((ROOT / "Proofs").rglob("*.lean")):
            text = path.read_text()
            if "\ntheorem " in text or text.startswith("theorem "):
                self.assertIn(path.relative_to(ROOT).as_posix(), files)

    def test_known_premises(self):
        self.assertIn("ASM-02", self.premises_of("Proofs/Asm/Proofs.lean", "bswap32_involutive"))
        self.assertIn("MTH-02", self.premises_of("Proofs/Floatops/Proofs.lean", "op64_spec"))
        self.assertEqual(self.premises_of("Proofs/Floatops/Proofs.lean", "sel_ne"), ["TRU-01"])
        counter = self.premises_of("Proofs/Threads/Counter.lean", "Threads.Counter.parallelCounter_spec")
        self.assertLessEqual({"THR-01", "THR-02", "THR-08", "ORD-01", "ORD-02", "ORD-06", "TRU-02", "PRF-01"},
                             set(counter))
        self.assertIn("TMR-01", self.premises_of("Proofs/Threadsync/Deadline.lean", "Threadsync.dl0_size"))
        # The committed Linux translation selects FutexImpl; the DarwinImpl block is not elaborated.
        lock = self.premises_of("Proofs/Threadsync/Lock.lean", "Threadsync.ThreadMutexOps.lock_spec")
        self.assertIn("THR-05", lock)
        self.assertNotIn("THR-06", lock)
        self.assertIn("PRF-02", self.premises_of("Proofs/Sync/RwLock.lean", "Sync.RwLockRead.rwLockRead_spec"))
        self.assertIn("ALC-04", self.premises_of("tests/roadmap/byte-sentinel/Check.lean", "example@L19"))
        self.assertIn("EXT-01", self.premises_of("tests/roadmap/models/Model.lean", "RegistryExample.evidence"))
        self.assertIn("TMR-02", {p for (f, _), e in self.entries.items()
                                 if f == "tests/roadmap/deadline-futex/Kernel.lean" for p in e["premises"]})

    def test_kernel_reviewed_gaps_are_indexed(self):
        """Premises that the compiled graph showed and the source index once missed."""
        semaphore = "Proofs/Sync/Semaphore.lean"
        # Field notation on `S : Sem X` / `hP : S.Fits P U` reaches Sem.R (pts) and the translation.
        self.assertLessEqual({"PRF-02", "SEM-03", "ORD-01", "TRU-02"},
                             set(self.premises_of(semaphore, "Sync.Sem.Fits.cur")))
        # `Enc ThreadId` is an instance of ZigLean.Mem.Thread.
        self.assertIn("ORD-01", self.premises_of("Proofs/Threads/Counter.lean", "Threads.Counter.decode_tid"))
        # `.relaxed` is the unique AtomicOrder constructor; `throw .unspecified` is a Zig.Error.
        self.assertIn("ORD-01", self.premises_of("Proofs/Atomics/Stack.lean", "Atomics.Stack.growsAt_loadM"))
        self.assertIn("SEM-01", self.premises_of("Proofs/Floatconv/Proofs.lean", "Zig.Float.toInt_of_isNaN"))
        # A `{ m with .. }` update carries Mem.allocPolicy without allocating: no allocator premise.
        self.assertFalse({"ALC-01", "ALC-02"} & set(self.premises_of(semaphore, "Sync.Sem.Step.refl")))

    def test_assurance_fixtures_are_excluded(self):
        self.assertFalse(any(f.startswith("tests/roadmap/assurance/") for f, _ in self.entries))


if __name__ == "__main__":
    unittest.main()
