"""Offline regressions for the A03 asm-wrapper harness (no Lean run)."""
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(f"asm_wrappers_{name}", HERE / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


harness, audit = load("harness"), load("audit")


class Rebinding(unittest.TestCase):
    def setUp(self):
        self.gen, self.ops = harness.GEN.read_text(), harness.asm_ops()

    def test_every_definition_has_its_translator_hash(self):
        self.assertEqual(set(harness.isa_defs(self.gen, self.ops)), set(self.ops))
        self.assertEqual(sorted(op["function"] for op in self.ops.values()), sorted(harness.FUNCTIONS))

    def test_only_namespace_and_import_lines_change(self):
        rebound = harness.rebind(self.gen, self.ops)
        kept = [line for line in self.gen.split("\n")
                if not line.startswith("import ") and line not in ("namespace Asm", "end Asm")]
        self.assertEqual(rebound.split("\n"),
                         [f"namespace {harness.NAMESPACE}" if line == "namespace Asm"
                          else f"end {harness.NAMESPACE}" if line == "end Asm" else line
                          for line in self.gen.split("\n") if not line.startswith("import ")])
        self.assertTrue(all(line in rebound for line in kept))
        self.assertNotIn("opaque", rebound)

    def test_rejects_unbound_or_uninterpreted_asm(self):
        extra = self.gen.replace("namespace Asm\n", "namespace Asm\n\nopaque airAsm_1 (i0 : BitVec 8) : BitVec 8\n")
        with self.assertRaises(ValueError):
            harness.rebind(extra, self.ops)
        unbound = self.gen.replace("namespace Asm\n", "namespace Asm\n\ndef airIsa_1 (i0 : BitVec 8) : BitVec 8 :=\n  i0\n")
        with self.assertRaises(ValueError):
            harness.rebind(unbound, self.ops)
        with self.assertRaises(ValueError):
            harness.rebind(self.gen.replace("import ZigLean", "import ZigLean\nimport Proofs.Asm.Gen"), self.ops)
        with self.assertRaises(ValueError):
            harness.rebind(self.gen, {**self.ops, "airIsa_0": next(iter(self.ops.values()))})

    def test_cross_check_binds_each_definition_to_its_template(self):
        text = harness.cross(self.gen, self.ops)
        for name, op in self.ops.items():
            self.assertIn(f"def {name} ", text)
            self.assertIn(f"MISMATCH model {name} ", text)
            self.assertIn(harness.lean_string(op["source"]), text)
        # A faulting block is compared only where the model reports no fault.
        divmod = next(n for n, op in self.ops.items() if op["function"] == "divmod")
        self.assertIn(f"({harness.NAMESPACE}.{divmod}_fault i0 i1).isSome ||", text)
        # A definition whose parameters differ from the AIR operand widths is refused.
        narrowed = self.gen.replace(f"def {divmod} (i0 : BitVec 32)", f"def {divmod} (i0 : BitVec 16)")
        self.assertNotEqual(narrowed, self.gen)
        with self.assertRaises(ValueError):
            harness.cross(narrowed, self.ops)

    def test_mutants_are_exact_and_distinct(self):
        variants = harness.mutants(self.gen, self.ops)
        self.assertGreaterEqual(set(variants), {"operand_order", "result_placement", "store_dropped", "store_misplaced"})
        texts = [text for text, _ in variants.values()]
        self.assertEqual(len(set(texts + [self.gen])), len(texts) + 1)
        for text, _ in variants.values():
            harness.rebind(text, self.ops)  # mutants keep every asm definition intact
        with self.assertRaises(ValueError):
            harness.alter(self.gen, "divmod", "no such text", "x")

    def test_inputs_cover_diff_inputs_and_avoid_zero_divisors(self):
        inputs = harness.sampled_inputs()
        self.assertTrue(all(a and b for a, b in inputs["divmod"]))
        for fn in harness.FUNCTIONS:
            self.assertGreaterEqual(len(inputs[fn]), 600)
        diff = [json.loads(line)[0] for line in (harness.DIFF_INPUTS / "bswap32.jsonl").read_text().splitlines()]
        self.assertTrue(set(diff) <= set(inputs["bswap32"]))


class Classification(unittest.TestCase):
    def test_control(self):
        harness.classify(0, "PASS asm-wrappers [(x, 1)]\n", None)
        for status, log in [(1, "PASS asm-wrappers []\n"), (0, "FAIL asm-wrappers: 1 failures\n"), (0, "")]:
            with self.assertRaises(ValueError):
                harness.classify(status, log, None)

    def test_mutant_needs_named_wrapper_mismatch(self):
        good = "MISMATCH wrapper divmod (1, 2): ok 7\nFAIL asm-wrappers: 1 failures\n"
        harness.classify(1, good, "divmod")
        for status, log in [(0, good), (2, good), (-6, good),
                            (1, "x.lean:1:0: error: unknown identifier\n"),
                            (1, good.replace("wrapper divmod", "wrapper bswap32")),
                            (1, good.replace("wrapper", "model")),
                            (1, "MISMATCH model airIsa_1 0\n" + good),
                            (1, "PANIC at AsmHarness.Interp.run\n" + good)]:
            with self.assertRaises(ValueError):
                harness.classify(status, log, "divmod")


class Audit(unittest.TestCase):
    def test_repository_is_separated(self):
        self.assertEqual(audit.static_issues(), [])

    def test_detects_leaks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ("lakefile.toml", "ZigLean.lean"):
                shutil.copy(audit.ROOT / name, root / name)
            for directory in audit.SHIPPED:
                (root / directory).mkdir()
            harness_dir = root / "harness"
            shutil.copytree(HERE, harness_dir, ignore=shutil.ignore_patterns("__pycache__"))
            self.assertEqual(audit.static_issues(root, harness_dir), [])
            leak = root / "Proofs/Leak.lean"
            leak.write_text("import tests.roadmap.asm_wrappers.Interp\n")
            self.assertEqual(len(audit.static_issues(root, harness_dir)), 1)
            leak.unlink()
            with (root / "lakefile.toml").open("a") as config:
                config.write('\n[[lean_lib]]\nname = "Harness"\nroots = ["tests.roadmap.Interp"]\n')
            self.assertEqual(len(audit.static_issues(root, harness_dir)), 1)
            shutil.copy(audit.ROOT / "lakefile.toml", root / "lakefile.toml")
            interp = harness_dir / "Interp.lean"
            interp.write_text(interp.read_text() + "\n@[csimp] theorem leak : True := trivial\n")
            self.assertEqual(len(audit.static_issues(root, harness_dir)), 1)

    def report(self, **change):
        definition = {"name": "Asm.airIsa_1", "kind": "definition", "module": "Proofs.Asm.Gen"}
        theorem = {"name": "bswap32_involutive", "kind": "theorem", "module": "Proofs.Asm.Proofs"}
        nodes = [definition, theorem] + change.get("nodes", [])
        return {"schema_version": 1, "nodes": nodes,
                "theorems": [{"name": "bswap32_involutive", "opaque_dependencies": change.get("opaques", []),
                              "compiler_redirections": change.get("redirections", []), "extern_dependencies": []}]}

    def test_report(self):
        self.assertEqual(audit.report_issues(self.report()), [])
        self.assertEqual(audit.report_issues(self.report(redirections=["Nat.repr"])), [])
        self.assertTrue(audit.report_issues(self.report(nodes=[{"name": "AsmHarness.Interp.run", "kind": "def", "module": "x"}])))
        self.assertTrue(audit.report_issues(self.report(redirections=["Asm.airIsa_1"])))
        # An uninterpreted asm function back in Proofs.Asm, as a node or as a theorem dependency.
        opaque = {"name": "Asm.airAsm_2", "kind": "opaque", "module": "Proofs.Asm.Gen"}
        self.assertTrue(audit.report_issues(self.report(nodes=[opaque])))
        self.assertEqual(len(audit.report_issues(self.report(nodes=[opaque], opaques=["Asm.airAsm_2"]))), 2)
        bad = self.report()
        bad["nodes"][0]["implemented_by"] = "AsmHarness.Interp.run"
        self.assertTrue(audit.report_issues(bad))
        bad = self.report()
        bad["nodes"][0]["kind"] = "opaque"
        self.assertTrue(audit.report_issues(bad))
        self.assertTrue(audit.report_issues({"schema_version": 1, "status": "error"}))


if __name__ == "__main__":
    unittest.main()
