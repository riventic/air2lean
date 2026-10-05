"""Bounded synthetic diagnostic tests; no compiler, native executable or translator."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("nullable_classifier", HERE / "classify_mutant.py")
classifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(classifier)
BASELINE = ("import ZigLean\nnamespace Nullable\n"
            "def cNull (p : BitVec 64) : Zig.MemM Bool := do\n"
            "  Zig.ptrIsNull (← Zig.ptrFromAddrNullable p.toNat)\n"
            "end Nullable\nprivate def value (f : Zig.MemM α) : Option α := none\n" +
            "\n".join(classifier.PREFIX + p + classifier.SUFFIX
                      for p in classifier.ASSERTIONS) + "\n")


class ClassifierTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="nullable classifier spaces ")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / "mutant with spaces.lean"
        self.baseline_path = self.root / "baseline.lean"
        self.baseline_path.write_text(BASELINE)
        self.mutant = classifier.make_mutant(BASELINE)
        self.source.write_text(self.mutant)
        self.blocks = []
        for number, line in enumerate(self.mutant.splitlines(), 1):
            for proposition in classifier.ASSERTIONS:
                if line == classifier.PREFIX + proposition + classifier.SUFFIX:
                    self.blocks.append(f"{self.source}:{number}:{line.index('native_decide')}: "
                                       f"error: {classifier.MESSAGE}\n  {proposition}\nis false\n")
        self.output = "".join(self.blocks)

    def accepted(self, output=None, status=1, baseline=BASELINE, mutant=None, source=None):
        return classifier.is_semantic_rejection(
            status, self.output if output is None else output,
            self.source if source is None else source, baseline,
            self.mutant if mutant is None else mutant)

    def test_all_three_located_refutations_with_spaces(self):
        self.assertTrue(self.accepted())

    def test_printer_line_wrapping(self):
        self.assertTrue(self.accepted(self.output.replace(" = ", "\n    =\n ")))

    def test_diagnostic_order_is_not_semantic(self):
        self.assertTrue(self.accepted("".join(reversed(self.blocks))))

    def test_relative_source_path_identity(self):
        relative = os.path.relpath(self.source, Path.cwd())
        self.assertTrue(self.accepted(self.output.replace(str(self.source), relative)))

    def test_success_setup_and_signal_statuses(self):
        for status in (0, 2, 137, 139, -9):
            with self.subTest(status=status):
                self.assertFalse(self.accepted(status=status))

    def test_missing_refutation(self):
        self.assertFalse(self.accepted("".join(self.blocks[:2])))

    def test_duplicate_refutation(self):
        self.assertFalse(self.accepted(self.blocks[0] + self.blocks[0] + self.blocks[2]))

    def test_extra_semantic_error(self):
        self.assertFalse(self.accepted(self.output + self.blocks[0]))

    def test_extra_setup_error(self):
        self.assertFalse(self.accepted(self.output +
            f"{self.source}:2:0: error: unknown identifier missingSetup\n"))

    def test_crash_resource_and_truncation_markers(self):
        for marker in ("Segmentation fault", "Killed", "out of memory", "Traceback",
                       "[output truncated]", "timeout exceeded"):
            with self.subTest(marker=marker):
                self.assertFalse(self.accepted(self.output + marker + "\n"))

    def test_unlocated_wrong_path_and_missing_path(self):
        wrong = self.root / "different.lean"
        wrong.write_text(self.mutant)
        for target in (str(wrong), str(self.root / "absent.lean"), ""):
            with self.subTest(target=target):
                self.assertFalse(self.accepted(self.output.replace(str(self.source), target)))

    def test_wrong_line_and_column(self):
        first = self.blocks[0].split(": error:", 1)[0]
        path, line, column = first.rsplit(":", 2)
        for changed in (f"{path}:{int(line)+1}:{column}", f"{path}:{line}:{int(column)+1}"):
            self.assertFalse(self.accepted(self.output.replace(first, changed, 1)))

    def test_wrong_proposition_and_tactic(self):
        self.assertFalse(self.accepted(self.output.replace("= some true", "= some false", 1)))
        self.assertFalse(self.accepted(self.output.replace("`native_decide`", "`decide`", 1)))

    def test_missing_terminal_and_partial_header(self):
        self.assertFalse(self.accepted(self.output.rsplit("is false", 1)[0]))
        self.assertFalse(self.accepted(self.output + "mutant.lean:9:"))

    def test_false_decide_words_are_insufficient(self):
        self.assertFalse(self.accepted("error: unexpected token false while parsing native_decide\n"))

    def test_altered_mutant_source(self):
        for altered in (self.mutant + "-- changed\n",
                        self.mutant.replace("pure (!", "pure (", 1),
                        self.mutant.replace("some true", "some false", 1)):
            self.assertFalse(self.accepted(mutant=altered))

    def test_malformed_missing_and_duplicate_baseline_assertions(self):
        for altered in (BASELINE.replace(classifier.SUFFIX, " := by decide", 1),
                        BASELINE.replace(classifier.PREFIX + classifier.ASSERTIONS[0] +
                                         classifier.SUFFIX + "\n", ""),
                        BASELINE + classifier.PREFIX + classifier.ASSERTIONS[0] +
                                         classifier.SUFFIX + "\n"):
            with self.assertRaises(ValueError):
                classifier.make_mutant(altered)
            self.assertFalse(self.accepted(baseline=altered))

    def test_mutation_target_and_import_must_be_unique(self):
        for altered in (BASELINE + "-- Zig.ptrIsNull\n", BASELINE + "import ZigLean\n",
                        BASELINE.replace("Zig.ptrIsNull", "otherPredicate"),
                        BASELINE + "-- nullableMutation\n"):
            with self.assertRaises(ValueError):
                classifier.make_mutant(altered)

    def test_bounded_input(self):
        self.assertFalse(self.accepted("x" * (classifier.MAX_BYTES + 1)))
        large = self.root / "large.log"
        large.write_bytes(b"x" * (classifier.MAX_BYTES + 1))
        with self.assertRaises(ValueError):
            classifier.read_bounded(large)

    def test_invalid_unicode_api_input(self):
        self.assertFalse(self.accepted(self.output + "\ud800"))
        self.assertFalse(self.accepted(mutant=self.mutant + "\ud800"))
        self.assertFalse(self.accepted(baseline=BASELINE + "\ud800"))

    def test_invalid_utf8_input(self):
        bad = self.root / "bad.log"
        bad.write_bytes(b"\xff")
        with self.assertRaises(UnicodeError):
            classifier.read_bounded(bad)

    def test_cli_accepts_and_fails_closed_without_echoing_payload(self):
        log = self.root / "mutation.log"
        log.write_text(self.output)
        args = ["classify_mutant.py", "1", str(log), str(self.source), str(self.baseline_path)]
        with patch("sys.argv", args):
            classifier.main()
        log.write_text("PRIVATE MOCK CONTENT false decide")
        stderr = io.StringIO()
        with patch("sys.argv", args), contextlib.redirect_stderr(stderr):
            with self.assertRaises(SystemExit) as error:
                classifier.main()
        self.assertEqual(error.exception.code, 1)
        self.assertNotIn("PRIVATE MOCK CONTENT", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
