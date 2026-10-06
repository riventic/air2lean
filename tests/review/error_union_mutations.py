#!/usr/bin/env python3
"""ROOT-only serial semantic mutants: definition compilation must precede oracle failure."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MUTANTS = [
    ("equal_alignment", "else if align ≥ 2 then", "else if align > 2 then"),
    ("zero_offset", "if size = 0 then (0, 0)", "if size = 0 then (0, 2)"),
    ("zero_size", "(Nat.max align 2)\n\n/-- `E!T`", "(if size = 0 then 2 else Nat.max align 2)\n\n/-- `E!T`"),
]


def run(argv, cwd):
    return subprocess.run(argv, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)


def main():
    report_path = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else ROOT / "error-union-mutation-report.json"
    if len(sys.argv) > 2:
        raise SystemExit("usage: error_union_mutations.py [REPORT.json]")
    report = []
    baseline = run(["lake", "build", "ZigLean.Mem.Enc"], ROOT)
    if baseline.returncode:
        raise RuntimeError("baseline definitions did not compile")
    for name, _, _ in MUTANTS:
        positive = run(["lake", "env", "lean", "--run",
            str(ROOT / "tests/review/ErrorUnionMutationOracle.lean"), name], ROOT)
        if positive.returncode or f"ABI mutation oracle passed: {name}" not in positive.stdout:
            raise RuntimeError(f"{name}: baseline oracle failed")
    with tempfile.TemporaryDirectory(prefix="error-union-mutants-") as work:
        for name, anchor, replacement in MUTANTS:
            target = Path(work) / name
            target.mkdir()
            shutil.copytree(ROOT / "ZigLean", target / "ZigLean")
            for file in ("lakefile.toml", "lean-toolchain"):
                shutil.copyfile(ROOT / file, target / file)
            oracle = target / "Oracle.lean"
            shutil.copyfile(ROOT / "tests/review/ErrorUnionMutationOracle.lean", oracle)
            enc = target / "ZigLean/Mem/Enc.lean"
            text = enc.read_text()
            if text.count(anchor) != 1:
                raise RuntimeError(f"{name}: expected one mutation anchor")
            enc.write_text(text.replace(anchor, replacement))
            compiled = run(["lake", "build", "ZigLean.Mem.Enc"], target)
            entry = {"name": name, "definitions_exit": compiled.returncode, "definitions_output": compiled.stdout}
            report.append(entry)
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            if compiled.returncode:
                raise RuntimeError(f"{name}: changed definitions did not compile; this is not semantic detection")
            # Elaboration/runtime setup failures cannot count as detection: require the exact runtime marker.
            observed = run(["lake", "env", "lean", "--run", str(oracle), name], target)
            entry.update(oracle_exit=observed.returncode, oracle_output=observed.stdout)
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            if observed.returncode != 1 or f"ABI_MUTANT_DETECTED:{name}" not in observed.stdout:
                raise RuntimeError(f"{name}: missing strict semantic counterexample")
    print("Three typed error-union semantic mutants detected")


if __name__ == "__main__":
    main()
