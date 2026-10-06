#!/usr/bin/env python3
"""Mutate the emitted recovered-parent writes; require semantic false assertions."""
import importlib.util
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
# Reuse the strict located-error classifier, including infrastructure/warning rejection.
spec = importlib.util.spec_from_file_location("dispatch_mutations", Path(__file__).resolve().parent.parent / "dispatch" / "mutations.py")
classifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(classifier)
classifier.REFUTATION = "Tactic `decide` proved that the proposition"


def mutants(generated):
    direct = (generated / "direct.lean").read_text()
    yield "wrong_parent_field", classifier.changed_once(direct,
        r"with y := \(42 : BitVec 32\)", "with x := (42 : BitVec 32)")
    nested = (generated / "nested.lean").read_text()
    yield "lost_outer_alias", classifier.changed_once(nested,
        r"with tag := \(6 : BitVec 32\)", "with tag := (7 : BitVec 32)")


def main():
    generated, output = map(Path, sys.argv[1:])
    output.mkdir(parents=True, exist_ok=True)
    for name, source in mutants(generated):
        path = output / (name + ".lean")
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "-R", str(output), str(path)],
                                capture_output=True, text=True, timeout=60)
        if not classifier.is_semantic_rejection(result.returncode, result.stdout + result.stderr):
            raise AssertionError(f"mutant survived or failed outside semantic assertion: {name}\n{result.stdout}{result.stderr}")
        print(f"local parent semantic mutant rejected: {name}")


if __name__ == "__main__":
    main()
