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
        # The scoped ownership proofs run before the general Proofs build in CI.
        start = workflow.index("      - name: Thread tuple source and ownership gate\n")
        end = workflow.index("      - name: Golden AIR, translate, build, differential test\n", start)
        gate = [line.strip() for line in workflow[start:end].splitlines()]
        prerequisite = "lake build ZigLean.Conc.Csl ZigLean.Sep"
        self.assertEqual(gate.count(prerequisite), 1)
        self.assertLess(gate.index(prerequisite),
                        gate.index("bash tests/roadmap/thread-tuples/check.sh --check-artifacts"))

class AdapterEnvironment(unittest.TestCase):
    def setUp(self):
        import shutil
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        fixture = self.root / "tests/roadmap/thread-tuples"
        fixture.mkdir(parents=True)
        original = Path(__file__).resolve().parent
        for name in ("check.sh", "check-export.py", "adapter-contract.zig"):
            shutil.copyfile(original / name, fixture / name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(original.parents[2] / "scripts/normalize-generated.py",
                        self.root / "scripts/normalize-generated.py")
        self.fixture = fixture
        self.bin = self.root / "bin"
        self.bin.mkdir()
        tools = {
            "fake-air": """import json,os
from pathlib import Path
for name in ('mutableCapture','strongCapture','weakCapture','sliceWorker'):
 (Path(os.environ['ZIG_AIR_JSON_DIR'])/(name+'.json')).write_text(json.dumps({'name':'thread_adapter_contract.'+name,'zig_version':'0.16.0','schema':11,'target_endian':'little'}))
""",
            "fake-translator": """import sys
from pathlib import Path
Path(sys.argv[sys.argv.index('-o')+1]).write_text('import ZigLean\\n')
""",
            "lean-override": """import json,os,sys
from pathlib import Path
Path(os.environ['ENV_CAPTURE']).write_text(json.dumps({'lean_path':os.environ.get('LEAN_PATH'),'args':sys.argv[1:]}))
""",
        }
        tools["lake"] = tools["lean-override"]
        for name, body in tools.items():
            tool = self.bin / name
            tool.write_text("#!/usr/bin/env python3\n" + body)
            tool.chmod(0o755)

    def check_branch(self, override):
        import os
        import subprocess
        for inherited in (None, "/inherited/lean"):
            with self.subTest(inherited=inherited, override=override):
                capture = self.root / "environment.json"
                output = self.root / ("unset" if inherited is None else "inherited")
                env = dict(os.environ, PATH=str(self.bin)+os.pathsep+os.environ["PATH"],
                           AIR2LEAN_ZIG_AIR=str(self.bin/"fake-air"),
                           AIR2LEAN_TRANSLATOR=str(self.bin/"fake-translator"),
                           ENV_CAPTURE=str(capture))
                env.pop("LEAN_PATH", None)
                env.pop("AIR2LEAN_LEAN", None)
                if inherited is not None:
                    env["LEAN_PATH"] = inherited
                if override:
                    env["AIR2LEAN_LEAN"] = str(self.bin/"lean-override")
                result = subprocess.run(["bash", str(self.fixture/"check.sh"), "--adapter-contract", str(output)],
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
                import json
                observed = json.loads(capture.read_text())
                paths = observed["lean_path"].split(os.pathsep)
                self.assertEqual(Path(paths[0]).resolve(), self.root.resolve()/".lake/build/lib/lean")
                self.assertEqual(paths[1:], [] if inherited is None else [inherited])
                self.assertEqual(observed["args"][:-1], [] if override else ["env", "lean"])

    def test_explicit_override_environment(self):
        self.check_branch(True)

    def test_default_lake_environment(self):
        self.check_branch(False)

if __name__ == "__main__":
    unittest.main()
