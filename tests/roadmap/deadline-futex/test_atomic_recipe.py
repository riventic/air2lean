"""Static and dry-plan checks; every subprocess is mocked."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("atomic_wrapper", Path(__file__).with_name("root-atomic-runtime.py"))
wrapper = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(wrapper)


class AtomicRecipeTests(unittest.TestCase):
    def test_dry_plan_retains_atomic_inputs_without_toolchains(self):
        output = io.StringIO()
        with patch("sys.argv", ["root-atomic-runtime.py"]), patch.object(wrapper.recipe.subprocess, "Popen") as process:
            with contextlib.redirect_stdout(output):
                self.assertEqual(wrapper.recipe.main(), 0)
        process.assert_not_called()
        report = json.loads(output.getvalue())
        self.assertEqual(report["status"], "prepared")
        self.assertEqual([name for name, _ in report["commands"]], [
            "build-time", "build-timed-scheduler", "build-atomic-laws", "kernel", "runtime",
            "atomic-kernel", "atomic-runtime"])
        for name in ("ZigLean/Conc/Lemmas.lean", "ZigLean/Mem/Lemmas.lean",
                     "tests/roadmap/deadline-futex/AtomicKernel.lean",
                     "tests/roadmap/deadline-futex/RuntimeAtomic.lean"):
            self.assertIn(name, report["source_hashes"])
        for _, argv in report["commands"]:
            self.assertNotIn("--version", argv)



if __name__ == "__main__":
    unittest.main()
