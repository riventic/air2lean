#!/usr/bin/env python3
"""Offline checks of the qualification gate; no toolchain is invoked."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


native = load("native_checks")
mutations = load("mutations")


class HarnessTests(unittest.TestCase):
    def write_air(self, root):
        for name in sorted(native.REQUIRED):
            body = [{"tag": "arg"}]
            if name in native.INDIRECT:
                body.append({"tag": "block", "body": [{"tag": "call", "callee": {"inst": 0}}]})
            raw = {"name": name, "zig_version": "0.16.0", "body": body}
            if name == "source.viaTable":
                raw["globals"] = [{"init": {"func": t}} for t in sorted(native.TARGETS)]
            (root / (name + ".json")).write_text(json.dumps(raw))

    def test_requires_fresh_inventory_and_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.write_air(root)
            native.check_inventory(root, "0.16.0")
            with self.assertRaises(AssertionError): native.check_inventory(root, "0.15.2")
            (root / "source.twice.json").unlink()
            with self.assertRaises(AssertionError): native.check_inventory(root, "0.16.0")

    def test_devirtualized_call_or_missing_target_fails(self):
        for name in native.INDIRECT + ["targets"]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.write_air(root)
                path = root / ((name if name != "targets" else "source.viaTable") + ".json")
                raw = json.loads(path.read_text())
                if name == "targets":
                    raw["globals"] = raw["globals"][1:]
                else:
                    raw["body"][1]["body"][0]["callee"] = {"func": "source.double"}
                path.write_text(json.dumps(raw))
                with self.assertRaises(AssertionError): native.check_inventory(root, "0.16.0")

    def test_semantic_checks(self):
        checks = native.checks()
        self.assertEqual(checks.count(":= by decide +kernel"), 36)
        self.assertIn("IndirectCallsNative.viaParam true 4294967295", checks)
        self.assertIn("IndirectCallsNative.memoryCaller 3)).map BitVec.toNat = some 10", checks)

    def test_mutation_anchors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Calls.lean").write_text(
                "\ndef table (p0 : BitVec 64) := (if i2 == (⟨some 2, 0⟩ : Zig.Ptr) then x)\n\n"
                "\ndef callOnce (p0 : Zig.Ptr) := (if p0 == q then Zig.callR (square p1) else throw .illegal)\n\n")
            outputs = list(mutations.mutants(root))
            self.assertEqual([name for name, _ in outputs], ["lost_target", "unknown_admitted", "wrong_target"])
            self.assertIn("some 9", outputs[0][1])
            (root / "Calls.lean").write_text("missing")
            with self.assertRaises(ValueError): list(mutations.mutants(root))

    def test_only_semantic_refutations_count(self):
        false = "mutant.lean:1:1: error: Tactic `decide` proved that the proposition\n  a = b\nis false\n"
        self.assertTrue(mutations.classifier.is_semantic_rejection(1, false))
        stuck = "mutant.lean:1:1: error: Tactic `decide` failed for proposition\n  a = b\n"
        for code, message in [(0, false), (137, false), (1, "syntax error"), (1, stuck),
                              (1, false + "mutant.lean:2:1: error: unknown identifier\n")]:
            self.assertFalse(mutations.classifier.is_semantic_rejection(code, message))


if __name__ == "__main__":
    unittest.main()
