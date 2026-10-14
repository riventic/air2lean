#!/usr/bin/env python3
"""Fast policy regressions; actual Lean environment regressions are in check.sh."""
import importlib.util
import json
from pathlib import Path
import tempfile
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
        handle = self.node(name, "opaque", module="ZigLean.SimpAttr", backing="init")
        self.assertNotIn(f"ZigLean.SimpAttr::{name}", self.policy["project_opaques"])
        report = apply_policy(self.raw([], [handle]), self.policy)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["nodes"][0]["trust_class"], "meta-code-opaque")
        # Classified by property, not by name: a handle a theorem reaches, or one without
        # `initialize` backing, is not meta code.
        self.assertEqual(apply_policy(self.raw([name], [handle]), self.policy)["status"], "fail")
        self.assertEqual(apply_policy(self.raw([], [dict(handle, backing=None)]), self.policy)["status"], "fail")

    def test_sep_frame_collector_policy_is_exact(self):
        name = "_private.ZigLean.Sep.Automation.0.Zig.SepAutomation.atoms.collect"
        user = "Zig.SepAutomation.atoms.collect"
        collector = self.node(name, "opaque", module="ZigLean.Sep.Automation",
                              user_name=user, partial=True, backing="partial")
        self.assertNotIn(f"ZigLean.Sep.Automation::{user}", self.policy["project_opaques"])
        report = apply_policy(self.raw([], [collector]), self.policy)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["nodes"][0]["trust_class"], "meta-code-opaque")
        # Reached by a theorem it is no longer meta code, whatever its name.
        reached = apply_policy(self.raw([name], [collector]), self.policy)
        self.assertEqual(reached["status"], "fail")
        self.assertEqual(reached["violations"][0]["trust_class"], "unexpected-opaque")

    def engine(self, name="Zig.Full.Auto.wpWalk", backing="partial", **extra):
        return self.node(name, "opaque", module="ZigLean.Sep.Full.Auto", backing=backing, **extra)

    def test_engine_code_opaque_needs_no_policy_entry(self):
        for backing in ("partial", "init"):
            with self.subTest(backing=backing):
                report = apply_policy(self.raw([], [self.engine(backing=backing)]), self.policy)
                self.assertEqual(report["status"], "pass")
                self.assertEqual(report["nodes"][0]["trust_class"], "meta-code-opaque")

    def test_opaque_a_theorem_uses_is_not_engine_code(self):
        # Same name and backing as engine code; the theorem reaches it, directly or through a lemma.
        for dependencies, nodes in [
                (["Zig.Full.Auto.wpWalk"], [self.engine()]),
                (["lemma"], [self.node("lemma", "theorem", ["Zig.Full.Auto.wpWalk"]), self.engine()])]:
            with self.subTest(dependencies=dependencies):
                report = apply_policy(self.raw(dependencies, nodes), self.policy)
                self.assertEqual(report["status"], "fail")
                self.assertEqual(report["theorems"][0]["violations"], ["Zig.Full.Auto.wpWalk"])
                self.assertEqual(report["violations"][0]["trust_class"], "unexpected-opaque")

    def test_only_compiled_code_is_engine_code(self):
        # Named like engine code, unreached, but a logical opaque (no `partial`/`initialize`
        # backing), or one with a redirection or extern of its own: still needs a premise.
        for changed in [self.engine(backing=None), self.engine(implemented_by="unreviewed.replacement"),
                        self.engine(extern=[{"kind": "standard", "backend": "all", "target": "unreviewed"}]),
                        self.engine(unsafe=True), dict(self.engine(), kind="axiom")]:
            with self.subTest(changed=changed):
                self.assertEqual(apply_policy(self.raw([], [changed]), self.policy)["status"], "fail")

    def test_sep_frame_collector_policy_does_not_allow_other_trust_boundaries(self):
        name = "_private.ZigLean.Sep.Automation.0.Zig.SepAutomation.atoms.collect"
        collector = self.node(name, "opaque", module="ZigLean.Sep.Automation",
                              user_name="Zig.SepAutomation.atoms.collect", partial=True, backing="partial")
        reached = apply_policy(self.raw([name], [collector]), self.policy)
        self.assertEqual(reached["violations"][0]["trust_class"], "unexpected-opaque")
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
        self.assertIn("sorryAx", report["theorems"][0]["violations"])

    def test_engine_code_does_not_hide_a_sorry_dependency(self):
        engine = self.engine(dependencies=["sorryAx"])
        raw = self.raw([engine["name"]], [engine, self.node("sorryAx", "axiom", module="Init.Prelude")], ["sorryAx"])
        report = apply_policy(raw, self.policy)
        self.assertEqual(report["status"], "fail")
        self.assertIn("sorryAx", report["theorems"][0]["violations"])

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


PROFILE = '-- air2lean-profile: {"correspondence":"model","profile":{"name":"abi64-le-v1"}}\n'


def models(*bindings):
    return "-- air2lean-models: " + json.dumps({"schema": 1, "assumptions": [], "bindings": list(bindings)}) + "\n"


ASSUMED = {"symbol": "extern:ext_visit", "trust": "assumed", "proof": None, "implementation": "Model.visit",
           "contract": "Model.contract", "extern": {"library": None, "premise": "EXT-03"}}
GENERATED = (PROFILE + models(ASSUMED) + "import ZigLean\n\nnamespace Fix\n\n"
             "opaque airAsm_7 (i0 : BitVec 64) : BitVec 64\n\nopaque airAsmFx_8 (i0 : BitVec 8) : BitVec 8\n\n"
             "axiom air2lean_model_0_evidence : True\n\naxiom stray : True\n\nend Fix\n")


class GeneratedDeclarationTests(unittest.TestCase):
    """Generated axioms and opaques are classified by the premise the translator's metadata
    records (policy `generated_declarations`); anything else stays a violation."""

    def setUp(self):
        self.policy = audit.load_policy(ROOT / "assurance/policy.json")
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.write("Fix/Gen.lean", GENERATED)
        self.write("Model.lean", "opaque Model.visit : Nat → Nat\nopaque Model.other : Nat\n")
        self.sources = {"Fix.Gen": "Fix/Gen.lean", "Model": "Model.lean"}
        # The modules scripts/gen-integrity.py retranslates (`assumptions.retranslated`).
        self.translated = {"Fix/Gen.lean"}

    def tearDown(self):
        self.temp.cleanup()

    def write(self, rel, text):
        (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
        (self.root / rel).write_text(text)

    def classify(self, *nodes):
        nodes = {n["name"]: n for n in nodes}
        return audit.generated_premises(nodes, self.policy, self.sources, self.root, frozenset(self.translated))

    @staticmethod
    def node(name, kind, module="Fix.Gen"):
        return {"name": name, "user_name": name, "module": module, "kind": kind, "dependencies": []}

    def test_generated_declarations_get_their_premises(self):
        found = self.classify(self.node("Fix.air2lean_model_0_evidence", "axiom"),
                              self.node("Fix.airAsm_7", "opaque"), self.node("Fix.airAsmFx_8", "opaque"),
                              self.node("Model.visit", "opaque", "Model"))
        self.assertEqual(found, {"Fix.air2lean_model_0_evidence": ["EXT-02", "EXT-03"],
                                 "Fix.airAsm_7": ["ASM-01"], "Fix.airAsmFx_8": ["ASM-03"],
                                 "Model.visit": ["EXT-01", "EXT-03"]})

    def test_unknown_axioms_and_opaques_stay_unclassified(self):
        self.assertEqual(self.classify(self.node("Fix.stray", "axiom"), self.node("Model.other", "opaque", "Model"),
                                       # Named like generated code, but not declared by the source.
                                       self.node("Fix.airAsm_9", "opaque"),
                                       self.node("Fix.air2lean_model_1_evidence", "axiom"),
                                       # A generated name of the other kind.
                                       self.node("Fix.airAsm_7", "axiom")), {})

    def test_hand_written_axiom_under_a_generated_name_is_unclassified(self):
        # The same text outside a generated module (no profile record, not named Gen.lean).
        self.write("Hand/Evidence.lean", GENERATED[len(PROFILE):])
        self.sources["Hand.Evidence"] = "Hand/Evidence.lean"
        hand = [self.node("Fix.air2lean_model_0_evidence", "axiom", "Hand.Evidence"),
                self.node("Fix.airAsm_7", "opaque", "Hand.Evidence")]
        self.assertEqual(self.classify(*hand), {})
        # A hand-written copy that keeps the profile record (or is named Gen.lean): it looks
        # generated, but gen-integrity retranslates no such module, so its declarations are not
        # the translator's.
        for rel, module in (("Hand/Copy.lean", "Hand.Copy"), ("Hand2/Gen.lean", "Hand2.Gen")):
            with self.subTest(copy=rel):
                self.write(rel, GENERATED)
                self.sources[module] = rel
                copied = [self.node("Fix.air2lean_model_0_evidence", "axiom", module),
                          self.node("Fix.airAsm_7", "opaque", module)]
                self.assertEqual(self.classify(*copied), {})
                # Its binding names no implementation the audit trusts either.
                self.translated.discard("Fix/Gen.lean")
                self.assertEqual(self.classify(self.node("Model.visit", "opaque", "Model"), *copied), {})
                self.translated.add("Fix/Gen.lean")
        # Under the architecture-audit stand-ins, which gen-integrity does not hold to translator output.
        self.write("tests/roadmap/architecture-audit/x/Gen.lean", GENERATED)
        self.sources["Audit.Gen"] = "tests/roadmap/architecture-audit/x/Gen.lean"
        self.assertEqual(self.classify(self.node("Fix.air2lean_model_0_evidence", "axiom", "Audit.Gen")), {})
        # A module without a known source.
        self.assertEqual(self.classify(self.node("Fix.air2lean_model_0_evidence", "axiom", "Unknown.Gen")), {})
        # A generated module whose binding is proved: its evidence is a theorem, never an axiom.
        self.write("Fix/Gen.lean", GENERATED.replace('"trust": "assumed"', '"trust": "proved-obligation"'))
        self.assertEqual(self.classify(self.node("Fix.air2lean_model_0_evidence", "axiom")), {})

    def test_audit_passes_classified_and_fails_unknown(self):
        sources = {"Callbacks.Gen": "tests/roadmap/callbacks/Callbacks/Gen.lean"}
        evidence = "Callbacks.air2lean_model_0_evidence"
        raw = {"schema_version": 1, "modules": ["Proofs.Fixture"], "project_declarations": [],
               "theorems": [{"name": "fixture", "module": "Proofs.Fixture", "axioms": [evidence]}],
               "nodes": [dict(self.node("fixture", "theorem", "Proofs.Fixture"), dependencies=[evidence], unsafe=False),
                         dict(self.node(evidence, "axiom", "Callbacks.Gen"), unsafe=False)]}
        report = apply_policy(raw, self.policy, None, True, sources)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["theorems"][0]["declaration_premises"], ["EXT-02", "EXT-03"])
        self.assertEqual(next(n for n in report["nodes"] if n["name"] == evidence)["trust_class"],
                         "generated-premise-axiom")
        # Without the generated module's source, and for a hand-written module, it fails closed.
        for changed in ({}, {"Callbacks.Gen": "tests/roadmap/callbacks/CallbackModel.lean"}):
            with self.subTest(sources=changed):
                report = apply_policy(raw, self.policy, None, True, changed)
                self.assertEqual(report["status"], "fail")
                self.assertEqual(report["violations"][0]["trust_class"], "unexpected-axiom")

    def test_policy_rules_never_name_one_declaration(self):
        for rule in [{"kind": "axiom", "name": "air2lean_model_0_evidence", "premises": ["EXT-02"], "reason": "x"},
                     {"kind": "opaque", "name": "airAsm_<n>", "premises": [], "reason": "x"},
                     {"kind": "opaque", "name": "airAsm_<n>", "premises": ["ASM-01"], "reason": "x", "trust": "assumed"},
                     {"kind": "theorem", "name": "x_<n>", "premises": ["ASM-01"], "reason": "x"}]:
            with self.subTest(rule=rule), self.assertRaises(ValueError):
                audit.generated_rules(dict(self.policy, generated_declarations=[rule]))

    def test_policy_premises_are_catalogued(self):
        catalog = (ROOT / "docs/premises.md").read_text()
        for rule, _ in audit.generated_rules(self.policy):
            for premise in rule["premises"]:
                self.assertIn(f'<a id="{premise.lower()}"></a>', catalog)


if __name__ == "__main__":
    unittest.main()
