#!/usr/bin/env python3
"""Bounded adversarial fixtures and actual CI invocation checks; no compiler calls."""
from pathlib import Path
import tempfile
import unittest
from classify_mutant import is_semantic_rejection

class MutationClassifier(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.source = Path(self.temp.name) / "Mutated.lean"
        self.source.write_text("example (a b c : BitVec 8) : TuplePipeline.dispatch (.worker (a,b,c)) = discard (TuplePipeline.worker a b c) := by rfl\n")
        self.error = (f"{self.source}:1:150: error: Tactic `rfl` failed: The left-hand side\n"
                      "  TuplePipeline.dispatch (.worker (a, b, c))\n"
                      "is not definitionally equal to the right-hand side\n"
                      "  discard (TuplePipeline.worker a b c)\n"
                      "a b c : BitVec 8\n⊢ TuplePipeline.dispatch (.worker (a,b,c)) = discard (TuplePipeline.worker a b c)\n")

    def test_located_equality(self):
        self.assertTrue(is_semantic_rejection(1, self.error, self.source))

    def test_warning_then_refutation(self):
        self.assertTrue(is_semantic_rejection(1, f"{self.source}:2:1: warning: unused variable\n" + self.error, self.source))

    def test_exit_statuses(self):
        for code in (0, 2, -9, 137, 143):
            with self.subTest(code=code):
                self.assertFalse(is_semantic_rejection(code, self.error, self.source))

    def test_mixed_errors(self):
        for suffix in (f"{self.source}:2:1: error: unknown module prefix 'ZigLean'\n",
                       f"{self.source}:2:1: error: unexpected token\n", "error: I/O failure\n"):
            with self.subTest(suffix=suffix):
                self.assertFalse(is_semantic_rejection(1, self.error + suffix, self.source))

    def test_unrelated_type_mismatch(self):
        self.assertFalse(is_semantic_rejection(1, self.error.replace("Tactic `rfl` failed: The left-hand side", "type mismatch"), self.source))

    def test_abnormal_text(self):
        for suffix in ("Killed\n", "uncaught exception: I/O error\n", "Segmentation fault\n", "I/O error\n", "failed to read file\n"):
            self.assertFalse(is_semantic_rejection(1, self.error + suffix, self.source))

    def test_wrong_location(self):
        self.assertFalse(is_semantic_rejection(1, self.error.replace(":1:150:", ":2:150:"), self.source))
        self.assertFalse(is_semantic_rejection(1, self.error.replace(str(self.source), str(self.source.with_name("Other.lean"))), self.source))

    def test_missing_or_echoed_diagnostic(self):
        self.assertFalse(is_semantic_rejection(1, "by rfl\n", self.source))
        self.assertFalse(is_semantic_rejection(1, self.error.split(": error: ",1)[1], self.source))

    def test_incomplete_goal(self):
        for part in ("⊢", "is not definitionally equal to the right-hand side", "TuplePipeline.worker"):
            self.assertFalse(is_semantic_rejection(1, self.error.replace(part, ""), self.source))

    def test_duplicate_assertions(self):
        self.source.write_text(self.source.read_text() * 2)
        self.assertFalse(is_semantic_rejection(1, self.error, self.source))

class CIInvocation(unittest.TestCase):
    def test_all_scoped_gate_invocations_use_bash(self):
        root = Path(__file__).resolve().parents[3]
        workflow = (root / ".github/workflows/ci.yml").read_text()
        invocations = [line.strip() for line in workflow.splitlines()
                       if "tests/roadmap/thread-tuples/check.sh " in line]
        self.assertEqual(len(invocations), 4)
        self.assertTrue(all(line.startswith("bash tests/roadmap/thread-tuples/check.sh ") for line in invocations))
        self.assertEqual({line.split()[2] for line in invocations},
                         {"--export", "--native", "--check-artifacts", "--adapter-contract"})

if __name__ == "__main__":
    unittest.main()
