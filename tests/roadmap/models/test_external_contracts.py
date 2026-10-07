#!/usr/bin/env python3
"""E01 contract assumption report: classification with a fake Lean (no compiler executed)."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

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


def run(text: str, lean_output: str, lean_status: int = 0, check: bool = True,
        expect: str | None = None) -> tuple[int, dict | None]:
    with tempfile.TemporaryDirectory(prefix="air2lean-contracts-test-") as tmp:
        lean = Path(tmp) / "lean"
        lean.write_text(f"#!/usr/bin/env bash\ncat <<'OUT'\n{lean_output}\nOUT\nexit {lean_status}\n")
        lean.chmod(0o755)
        source = Path(tmp) / "Gen.lean"
        source.write_text(text)
        command = [sys.executable, "-B", str(SCRIPT), str(source), "--lean", str(lean)]
        command += ["--check"] if check else []
        command += [f"--expect-assumptions={expect}"] if expect is not None else []
        result = subprocess.run(command, text=True, capture_output=True)
        return result.returncode, json.loads(result.stdout) if result.stdout else None


standard = ("'My.Client.air2lean_model_0_evidence' depends on axioms: [propext, Quot.sound]\n"
            "'My.Client.air2lean_model_1_evidence' depends on axioms: [My.Client.air2lean_model_1_evidence]")
two = generated(binding("project.fill", "proved-obligation"), binding("project.read", "assumed"))
status, out = run(two, standard, expect="project.read")
assert status == 0, out
assert [c["status"] for c in out["contracts"]] == ["verified", "assumption"], out
assert out["contracts"][0]["footprint"] == {"reads": [], "writes": [0]}
assert out["assumptions"] == ["project.read"]

# Proved but resting on sorry or a project axiom stays an assumption.
status, out = run(generated(binding("project.fill", "proved-obligation")),
                  "'My.Client.air2lean_model_0_evidence' depends on axioms: [propext, sorryAx]",
                  expect="project.fill")
assert status == 0 and "sorryAx" in out["contracts"][0]["reason"], out

# Axiom-free evidence is verified.
status, out = run(generated(binding("project.fill", "proved-obligation")),
                  "'My.Client.air2lean_model_0_evidence' does not depend on any axioms", expect="")
assert status == 0 and out["contracts"][0]["axioms"] == [], out

# A failing kernel check or a missing check never verifies.
status, out = run(generated(binding("project.fill", "proved-obligation")), "error: type mismatch", 1)
assert status == 0 and out["assumptions"] == ["project.fill"], out
status, out = run(generated(binding("project.fill", "proved-obligation")), standard, check=False)
assert status == 0 and "not kernel checked" in out["contracts"][0]["reason"], out

# Expectation mismatch and malformed input fail.
assert run(two, standard, expect="")[0] == 1
assert run("import ZigLean\n", "")[0] == 2
assert contracts.parse_axioms(standard)["My.Client.air2lean_model_0_evidence"] == ["propext", "Quot.sound"]
print("external contract report tests passed (no compiler executed)")
