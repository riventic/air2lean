#!/usr/bin/env python3
"""E01 contract assumption report: classification with a fake Lean (no compiler executed)."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / "scripts/external-contracts.py"
spec = importlib.util.spec_from_file_location("external_contracts", SCRIPT)
contracts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contracts)


def binding(symbol: str, trust: str) -> dict:
    return {"symbol": symbol, "contract": "M.contract", "implementation": "M.impl", "trust": trust,
            "proof": "M.proof" if trust == "proved-obligation" else None, "termination": "total",
            "errors": [], "effects": "tracked", "footprint": {"reads": [], "writes": [0]}}


def generated(*bindings: dict) -> str:
    report = {"schema": 1, "bindings": list(bindings),
              "assumptions": [b["symbol"] for b in bindings if b["trust"] == "assumed"]}
    return ("-- air2lean-profile: {}\n-- air2lean-models: " + json.dumps(report) +
            "\nimport ZigLean\n\nnamespace My.Client\n\nend My.Client\n")


def fake_lean(directory: Path, output: str, status: int) -> Path:
    lean = directory / "lean"
    lean.write_text(f"#!/usr/bin/env bash\ncat <<'OUT'\n{output}\nOUT\nexit {status}\n")
    lean.chmod(0o755)
    return lean


def run(text: str, lean_output: str, lean_status: int = 0, check: bool = True,
        expect: str | None = None) -> tuple[int, dict | None]:
    """The CLI in a subprocess."""
    with tempfile.TemporaryDirectory(prefix="air2lean-contracts-test-") as tmp:
        lean = fake_lean(Path(tmp), lean_output, lean_status)
        source = Path(tmp) / "Gen.lean"
        source.write_text(text)
        command = [sys.executable, "-B", str(SCRIPT), str(source), "--lean", str(lean)]
        command += ["--check"] if check else []
        command += [f"--expect-assumptions={expect}"] if expect is not None else []
        result = subprocess.run(command, text=True, capture_output=True)
        return result.returncode, json.loads(result.stdout) if result.stdout else None


def report(text: str, lean_output: str, lean_status: int = 0, check: bool = True) -> dict:
    """The module's report in process (the module global `contracts`, which mutants replace)."""
    with tempfile.TemporaryDirectory(prefix="air2lean-contracts-test-") as tmp:
        lean = fake_lean(Path(tmp), lean_output, lean_status)
        source = Path(tmp) / "Gen.lean"
        source.write_text(text)
        return contracts.report([source], check, str(lean))


STANDARD = ("'My.Client.air2lean_model_0_evidence' depends on axioms: [propext, Quot.sound]\n"
            "'My.Client.air2lean_model_1_evidence' depends on axioms: [My.Client.air2lean_model_1_evidence]")
TWO = generated(binding("project.fill", "proved-obligation"), binding("project.read", "assumed"))
FILL = generated(binding("project.fill", "proved-obligation"))


class ContractReportTests(unittest.TestCase):
    def test_cli_proved_and_assumed(self):
        status, out = run(TWO, STANDARD, expect="project.read")
        self.assertEqual(status, 0, out)
        self.assertEqual([c["status"] for c in out["contracts"]], ["verified", "assumption"], out)
        self.assertEqual(out["contracts"][0]["footprint"], {"reads": [], "writes": [0]})
        self.assertEqual(out["assumptions"], ["project.read"])
        # Expectation mismatch and malformed input fail.
        self.assertEqual(run(TWO, STANDARD, expect="")[0], 1)
        self.assertEqual(run("import ZigLean\n", "")[0], 2)

    def test_nonstandard_axioms_stay_assumptions(self):
        # Proved but resting on sorry or a project axiom stays an assumption.
        status, out = run(FILL, "'My.Client.air2lean_model_0_evidence' depends on axioms: [propext, sorryAx]",
                          expect="project.fill")
        self.assertEqual(status, 0, out)
        self.assertIn("sorryAx", out["contracts"][0]["reason"])
        out = report(FILL, "'My.Client.air2lean_model_0_evidence' depends on axioms: [propext, sorryAx]")
        self.assertEqual((out["contracts"][0]["status"], out["assumptions"]), ("assumption", ["project.fill"]))
        out = report(TWO, STANDARD)
        self.assertEqual(out["assumptions"], ["project.read"])

    def test_axiom_free_evidence_is_verified(self):
        status, out = run(FILL, "'My.Client.air2lean_model_0_evidence' does not depend on any axioms", expect="")
        self.assertEqual(status, 0, out)
        self.assertEqual(out["contracts"][0]["axioms"], [])

    def test_failed_or_missing_kernel_check_never_verifies(self):
        status, out = run(FILL, "error: type mismatch", 1)
        self.assertEqual((status, out["assumptions"]), (0, ["project.fill"]), out)
        status, out = run(FILL, STANDARD, check=False)
        self.assertEqual(status, 0, out)
        self.assertIn("not kernel checked", out["contracts"][0]["reason"])
        for out in (report(FILL, "error: type mismatch", 1), report(FILL, STANDARD, check=False)):
            self.assertEqual((out["contracts"][0]["status"], out["assumptions"]), ("assumption", ["project.fill"]))

    def test_parse_axioms(self):
        self.assertEqual(contracts.parse_axioms(STANDARD)["My.Client.air2lean_model_0_evidence"],
                         ["propext", "Quot.sound"])


if __name__ == "__main__":
    result = unittest.main(exit=False).result
    if not result.wasSuccessful():
        sys.exit(1)
    print("external contract report tests passed (no compiler executed)")
