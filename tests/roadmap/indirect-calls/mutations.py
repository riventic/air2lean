#!/usr/bin/env python3
"""Mutate the emitted indirect-call dispatch; require semantic false assertions."""
import importlib.util
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
# Reuse the strict located-error classifier, including infrastructure/warning rejection.
spec = importlib.util.spec_from_file_location("dispatch_mutations", Path(__file__).resolve().parent.parent / "dispatch" / "mutations.py")
classifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(classifier)
classifier.REFUTATION = "Tactic `decide` proved that the proposition"


def in_def(source, name, pattern, replacement):
    """Apply one replacement inside the emitted definition `name` only."""
    start = source.index(f"\ndef {name} ")
    end = source.index("\n\n", start + 1)
    return source[:start] + classifier.changed_once(source[start:end], pattern, replacement) + source[end:]


def mutants(generated):
    calls = (generated / "Calls.lean").read_text()
    # A declared target dropped from the table: its address no longer dispatches.
    yield "lost_target", in_def(calls, "table",
        r"\(⟨some 2, 0⟩ : Zig\.Ptr\) then", "(⟨some 9, 0⟩ : Zig.Ptr) then")
    # The unknown-address fallback calls a target instead of throwing `.illegal`.
    yield "unknown_admitted", in_def(calls, "callOnce",
        r"else throw \.illegal\)", "else Zig.callR (double p1))")
    # An address runs another target of the same signature.
    yield "wrong_target", in_def(calls, "callOnce",
        r"Zig\.callR \(square p1\)", "Zig.callR (double p1)")


def main():
    generated, output = map(Path, sys.argv[1:])
    output.mkdir(parents=True, exist_ok=True)
    for name, source in mutants(generated):
        path = output / (name + ".lean")
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "-R", str(output), str(path)],
                                capture_output=True, text=True, timeout=120)
        if not classifier.is_semantic_rejection(result.returncode, result.stdout + result.stderr):
            raise AssertionError(f"mutant survived or failed outside semantic assertion: {name}\n{result.stdout}{result.stderr}")
        print(f"indirect call semantic mutant rejected: {name}")


if __name__ == "__main__":
    main()
