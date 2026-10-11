#!/usr/bin/env python3
"""Fast policy regressions; actual Lean environment regressions are in check.sh."""
import importlib.util
from pathlib import Path
import unittest
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("assumptions", ROOT / "scripts/assumptions.py")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def replay(modules, rejected=()):
    """A kernel-replay record as scripts/assumptions.py writes it after running leanchecker."""
    modules = sorted(set(modules))
    rejected = [{"module": m, "output": "leanchecker found a problem in " + m} for m in rejected]
    return {"schema_version": 1, "tool": "leanchecker", "tool_sha256": "0" * 64, "lean_sha256": "1" * 64,
            "toolchain": "leanprover/lean4:test", "modules": modules, "modules_sha256": audit.modules_digest(modules),
            "reused": [], "rejected": rejected, "status": "fail" if rejected else "pass"}


def apply_policy(raw, *args):
    """Policy over a graph whose every project module was replayed (unless the test sets a record)."""
    if "kernel_replay" not in raw:
        raw = dict(raw, kernel_replay=replay([*raw["modules"], *(n["module"] for n in raw["nodes"]
                                                                 if audit.needs_replay(n["module"]))]))
    return audit.apply_policy(raw, *args)


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.policy = audit.load_policy(ROOT / "assurance/policy.json")

    def node(self, name, kind, dependencies=(), module="Proofs.Fixture", **extra):
        return {"name": name, "user_name": name, "module": module, "kind": kind,
                "dependencies": list(dependencies), "unsafe": False, **extra}

    def raw(self, dependencies, extra_nodes, axioms=()):
        return {"schema_version": 1, "modules": ["Proofs.Fixture"], "project_declarations": [],
                "theorems": [{"name": "fixture", "module": "Proofs.Fixture", "axioms": list(axioms)}],
                "nodes": [self.node("fixture", "theorem", dependencies), *extra_nodes]}

    def test_standard_axioms_are_separate(self):
        raw = self.raw(["Classical.choice"], [self.node("Classical.choice", "axiom", module="Init.Classical")], ["Classical.choice"])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["nodes"][0]["trust_class"], "standard-logical-axiom")

    def test_transitive_hidden_sorry(self):
        raw = self.raw(["imported"], [self.node("imported", "theorem", ["sorryAx"], module="Other.Hidden"),
                                    self.node("sorryAx", "axiom", module="Init.Prelude")], ["sorryAx"])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["theorems"][0]["violations"], ["sorryAx"])
        self.assertEqual(report["violations"][0]["trust_class"], "sorry")

    def test_violation_transfers_through_dependencies(self):
        # Not an axiom, so collectAxioms cannot report it: only the dependency closure can.
        raw = self.raw(["imported"], [self.node("imported", "theorem", ["hidden"], module="Other.Hidden"),
                                    self.node("hidden", "definition", module="Other.Hidden", unsafe=True)])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["theorems"][0]["violations"], ["hidden"])
        self.assertFalse(report["theorems"][0]["allowed"])

    def test_new_axiom_and_unused_axiom_fail(self):
        raw = self.raw([], [self.node("newAxiom", "axiom")])
        self.assertEqual(apply_policy(raw, self.policy)["status"], "fail")

    def test_compiler_proof_axiom_is_not_standard(self):
        raw = self.raw(["Lean.ofReduceBool"], [self.node("Lean.ofReduceBool", "axiom", module="Lean.Elab")], ["Lean.ofReduceBool"])
        self.assertEqual(apply_policy(raw, self.policy)["violations"][0]["trust_class"], "compiler-proof-axiom")

    def test_generated_native_axiom_is_compiler_dependent(self):
        name = "fixture._native.native_decide.ax_1_1"
        raw = self.raw([name], [self.node(name, "axiom")], [name])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["violations"][0]["trust_class"], "compiler-proof-axiom")
        self.assertTrue(audit.is_compiler_axiom("fixture._native.bv_decide.ax_3_2"))

    def test_opaque_body_does_not_make_an_axiom(self):
        opaque = self.node("Asm.airAsm_3500345798", "opaque", module="Proofs.Asm.Gen")
        report = apply_policy(self.raw([opaque["name"]], [opaque]), self.policy)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["theorems"][0]["axioms"], [])
        opaque["module"] = "Untrusted.Import"
        self.assertEqual(apply_policy(self.raw([opaque["name"]], [opaque]), self.policy)["status"], "fail")

    def test_simp_extension_policy_is_exact(self):
        name = "ext._@.ZigLean.SimpAttr.2786263690._hygCtx._hyg.3"
        handle = self.node(name, "opaque", module="ZigLean.SimpAttr")
        self.assertEqual(apply_policy(self.raw([], [handle]), self.policy)["status"], "pass")
        handle["name"] = handle["user_name"] = name.replace("2786263690", "2786263691")
        self.assertEqual(apply_policy(self.raw([], [handle]), self.policy)["status"], "fail")

    def test_sep_frame_collector_policy_is_exact(self):
        name = "_private.ZigLean.Sep.Automation.0.Zig.SepAutomation.atoms.collect"
        user = "Zig.SepAutomation.atoms.collect"
        collector = self.node(name, "opaque", module="ZigLean.Sep.Automation",
                              user_name=user, partial=True)
        report = apply_policy(self.raw([name], [collector]), self.policy)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["theorems"][0]["opaque_dependencies"], [name])
        self.assertEqual(report["theorems"][0]["axioms"], [])
        for changed in [dict(collector, user_name=user + ".other"),
                        dict(collector, module="Untrusted.Import")]:
            with self.subTest(changed=changed):
                result = apply_policy(self.raw([], [changed]), self.policy)
                self.assertEqual(result["status"], "fail")
                self.assertEqual(result["violations"][0]["trust_class"], "unexpected-opaque")

    def test_sep_frame_collector_policy_does_not_allow_other_trust_boundaries(self):
        name = "_private.ZigLean.Sep.Automation.0.Zig.SepAutomation.atoms.collect"
        collector = self.node(name, "opaque", module="ZigLean.Sep.Automation",
                              user_name="Zig.SepAutomation.atoms.collect", partial=True)
        for changed in [dict(collector, kind="axiom"), dict(collector, unsafe=True),
                        dict(collector, implemented_by="unreviewed.replacement"),
                        dict(collector, extern=[{
                            "kind": "standard", "backend": "all", "target": "unreviewed"}])]:
            with self.subTest(changed=changed):
                self.assertEqual(apply_policy(self.raw([], [changed]), self.policy)["status"], "fail")
        collector["dependencies"] = ["sorryAx"]
        raw = self.raw([name], [collector, self.node("sorryAx", "axiom", module="Init.Prelude")], ["sorryAx"])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["theorems"][0]["violations"], ["sorryAx"])

    def test_libm_replacement_requires_exact_private_target(self):
        libm = self.node("Zig.Float.libm", "opaque", module="ZigLean.Float.Libm",
                         implemented_by="_private.ZigLean.Float.Libm.0.Zig.Float.libmImpl")
        raw = self.raw([libm["name"]], [libm])
        # The fixture reaches the float model, so it also needs a float-semantics label.
        self.assertEqual(apply_policy(raw, self.policy)["status"], "fail")
        labels = audit.float_semantics().load_registry(root=ROOT)
        labels["theorems"]["Proofs.Fixture::fixture"] = {"semantics": "ieee", "targets": ["aarch64-macos", "x86_64-linux"], "correspondence": "model"}
        self.assertEqual(apply_policy(raw, self.policy, labels)["status"], "pass")
        libm["implemented_by"] = "_private.ZigLean.Float.Libm.1.Zig.Float.libmImpl"
        self.assertEqual(apply_policy(raw, self.policy, labels)["status"], "fail")

    def test_unknown_imported_redirection_fails(self):
        redirected = self.node("redirected", "definition", module="TestOnly.Import", implemented_by="replacement")
        report = apply_policy(self.raw(["redirected"], [redirected]), self.policy)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["violations"][0]["trust_class"], "unexpected-compiler-redirection")

    def test_exact_extern_contract_required_for_definitions(self):
        target = {"kind": "standard", "backend": "all", "target": "fixture_c_symbol"}
        external = self.node("external", "definition", extern=[target])
        raw = self.raw(["external"], [external])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["violations"][0]["trust_class"], "unexpected-project-extern")
        self.policy["project_externs"]["Proofs.Fixture::external"] = {
            "targets": [target], "reason": "Reviewed test contract."}
        self.assertEqual(apply_policy(raw, self.policy)["status"], "pass")
        external["extern"] = [{**target, "target": "changed_symbol"}]
        self.assertEqual(apply_policy(raw, self.policy)["status"], "fail")
        external["extern"] = [{**target, "backend": "llvm"}]
        self.assertEqual(apply_policy(raw, self.policy)["status"], "fail")

    def test_unused_extern_definition_is_checked(self):
        external = self.node("unusedExternal", "definition", extern=[{
            "kind": "inline", "backend": "all", "target": "wrong_computation"}])
        self.assertEqual(apply_policy(self.raw([], [external]), self.policy)["status"], "fail")

    def test_statement_dependencies_pass_through_and_are_checked(self):
        root = self.node("root", "definition")
        raw = self.raw(["root", "True"], [root, self.node("True", "inductive", module="Init.Prelude")])
        raw["theorems"][0].update(statement_dependencies=["True", "root"], conclusion_dependencies=["True"])
        theorem = apply_policy(raw, self.policy)["theorems"][0]
        self.assertEqual((theorem["statement_dependencies"], theorem["conclusion_dependencies"]), (["True", "root"], ["True"]))
        for statement, conclusion in ((["True"], ["root"]), (["unrelated"], []), (["True"], None), ("root", "root")):
            raw["theorems"][0].update(statement_dependencies=statement, conclusion_dependencies=conclusion)
            with self.assertRaisesRegex(ValueError, "statement dependencies"):
                apply_policy(raw, self.policy)

    def test_kernel_replay_rejection_fails_dependent_theorems(self):
        # S1: an olean written with debug.skipKernelTC passes collectAxioms; only replay rejects it.
        raw = self.raw(["imported"], [self.node("imported", "theorem", module="Other.Unchecked")])
        raw["kernel_replay"] = replay(["Proofs.Fixture", "Other.Unchecked"], rejected=["Other.Unchecked"])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["theorems"][0]["violations"], ["imported"])
        self.assertEqual(report["violations"][0]["trust_class"], "kernel-replay-rejected")
        self.assertEqual(report["kernel_replay"], raw["kernel_replay"])

    def test_module_outside_replay_is_not_trusted(self):
        raw = self.raw(["imported"], [self.node("imported", "theorem", module="Other.Import"),
                                      self.node("Nat", "inductive", module="Init.Prelude")])
        raw["kernel_replay"] = replay(["Proofs.Fixture"])
        report = apply_policy(raw, self.policy)
        self.assertEqual([(v["name"], v["trust_class"]) for v in report["violations"]],
                         [("imported", "kernel-replay-missing")])

    def test_replay_record_is_required_and_consistent(self):
        raw = self.raw([], [])
        with self.assertRaisesRegex(ValueError, "kernel replay"):
            audit.apply_policy(raw, self.policy)
        for broken in (dict(replay(["Proofs.Fixture"]), status="fail"),
                       dict(replay(["Proofs.Fixture"]), modules_sha256="0" * 64),
                       dict(replay(["Proofs.Fixture"]), tool="other"),
                       dict(replay(["Proofs.Fixture"]), reused=["Other"]),
                       replay(["Other.Module"]),
                       {k: v for k, v in replay(["Proofs.Fixture"]).items() if k != "reused"}):
            with self.subTest(broken=broken), self.assertRaisesRegex(ValueError, "kernel replay"):
                apply_policy(dict(raw, kernel_replay=broken), self.policy)

    def test_incomplete_graph_and_empty_scope_fail_closed(self):
        with self.assertRaises(ValueError):
            apply_policy(self.raw(["missing"], []), self.policy)
        with self.assertRaises(ValueError):
            apply_policy({"schema_version": 1, "modules": [], "nodes": [], "theorems": []}, self.policy)


if __name__ == "__main__":
    unittest.main()
