#!/usr/bin/env python3
"""Offline adversarial diagnostic fixtures; never invokes a compiler."""
import unittest
from classify_mutant import is_semantic_rejection

FALSE = "mutant.lean:37:45: error: Tactic `decide` proved that the proposition\n  Zig.clz 4 1 = 7\nis false\n"
WARNING = "mutant.lean:1:1: warning: unused variable\nNote: consider removing it\n"


class ClassifierTests(unittest.TestCase):
    def test_false_proposition(self):
        self.assertTrue(is_semantic_rejection(1, FALSE))

    def test_warning_and_multiple_false_propositions(self):
        self.assertTrue(is_semantic_rejection(1, WARNING + FALSE + WARNING + FALSE + WARNING))

    def test_success_and_signal_statuses(self):
        for status in (0, 2, -9, 137, 143):
            with self.subTest(status=status):
                self.assertFalse(is_semantic_rejection(status, FALSE))

    def test_killed_process(self):
        self.assertFalse(is_semantic_rejection(1, "Killed\n"))
        self.assertFalse(is_semantic_rejection(1, FALSE + "Killed\n"))

    def test_import_error(self):
        self.assertFalse(is_semantic_rejection(1, "mutant.lean:1:0: error: unknown module prefix 'ZigLean'\n"))

    def test_mixed_diagnostics(self):
        self.assertFalse(is_semantic_rejection(1, FALSE + "mutant.lean:2:1: error: unexpected token\n"))
        self.assertFalse(is_semantic_rejection(1, FALSE + "error: unknown module prefix\n"))

    def test_other_tactic_failure(self):
        self.assertFalse(is_semantic_rejection(1, FALSE.replace("proved that the proposition", "failed for proposition")))

    def test_incomplete_refutation(self):
        self.assertFalse(is_semantic_rejection(1, FALSE.replace("is false", "")))
        self.assertFalse(is_semantic_rejection(1, FALSE.replace("  Zig.clz 4 1 = 7\n", "")))

    def test_echoed_assertion_text(self):
        self.assertFalse(is_semantic_rejection(1, "example : Zig.clz 4 1 = 7 := by decide\n"))
        self.assertFalse(is_semantic_rejection(1, "Tactic `decide` proved that the proposition\n  False\nis false\n"))
        self.assertFalse(is_semantic_rejection(1, "echo: error: Tactic `decide` proved that the proposition\n  False\nis false\n"))


if __name__ == "__main__":
    unittest.main()
