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
    def test_shared_nested_traversal(self):
        self.assertIs(native.nested_insts, native.dispatch.nested_insts)
        body = [{"tag": "block", "body": [{"tag": "inside"}]},
                {"tag": "switch", "cases": [{"body": [{"tag": "case"}]}],
                 "then": [{"tag": "yes"}], "else": [{"tag": "no"}]}]
        self.assertEqual([i["tag"] for i in native.nested_insts(body)],
                         ["block", "inside", "switch", "yes", "no", "case"])

    def write_air(self, root):
        for name in ["direct", "nested", "castAlias", "escaped", "write", "arrayItem"]:
            body = [{"tag": "alloc"}, {"tag": "struct_field_ptr_index_0"}, {"tag": "field_parent_ptr"}]
            if name == "nested": body.append({"tag": "block", "body": [{"tag": "field_parent_ptr"}]})
            if name == "castAlias": body.append({"tag": "bitcast"})
            if name == "escaped": body.append({"tag": "call"})
            if name == "arrayItem": body += [{"tag": "ptr_elem_ptr"}, {"tag": "field_parent_ptr"}]
            (root / (name + ".json")).write_text(json.dumps({"name": "source." + name,
                "zig_version": "0.16.0", "body": body}))

    def test_requires_fresh_inventory_and_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.write_air(root)
            native.check_inventory(root, "0.16.0")
            with self.assertRaises(AssertionError): native.check_inventory(root, "0.15.2")
            (root / "write.json").unlink()
            with self.assertRaises(AssertionError): native.check_inventory(root, "0.16.0")

    def test_missing_parent_and_nested_recovery_fail(self):
        for name, tag in [("direct", "field_parent_ptr"), ("nested", "block"),
                          ("castAlias", "bitcast"), ("escaped", "call"),
                          ("arrayItem", "ptr_elem_ptr"), ("arrayItem", "field_parent_ptr")]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self.write_air(root)
                path = root / (name + ".json")
                raw = json.loads(path.read_text())
                raw["body"] = [i for i in raw["body"] if i["tag"] != tag]
                path.write_text(json.dumps(raw))
                with self.assertRaises(AssertionError): native.check_inventory(root, "0.16.0")

    def test_semantic_checks_and_mutation_anchors(self):
        checks = native.checks()
        self.assertEqual(checks.count(":= by decide +kernel"), 28)
        self.assertIn("memoryValue (LocalParentNative.escaped 4294967295)", checks)
        self.assertIn("= some 41", checks)
        self.assertIn("successful (LocalParentNative.nested 3)", checks)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "direct.lean").write_text("modify (fun s => { s with local10 := { s.local10 with y := (42 : BitVec 32) } })")
            (root / "nested.lean").write_text("modify (fun s => { s with local10 := { s.local10 with tag := (6 : BitVec 32) } })")
            outputs = list(mutations.mutants(root))
            self.assertEqual([name for name, _ in outputs], ["wrong_parent_field", "lost_outer_alias"])
            self.assertIn("with x :=", outputs[0][1])
            (root / "direct.lean").write_text("missing")
            with self.assertRaises(AssertionError): list(mutations.mutants(root))

    def test_only_semantic_refutations_count(self):
        false = "mutant.lean:1:1: error: Tactic `decide` proved that the proposition\n  a = b\nis false\n"
        self.assertTrue(mutations.classifier.is_semantic_rejection(1, false))
        for code, message in [(0, false), (137, false), (1, "syntax error"),
                              (1, "Killed\n" + false), (1, false + "mutant.lean:2:1: error: unknown identifier\n")]:
            self.assertFalse(mutations.classifier.is_semantic_rejection(code, message))


if __name__ == "__main__":
    unittest.main()
