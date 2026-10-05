#!/usr/bin/env python3
"""Reject semantic mutants of successfully elaborated generated code; no production edits."""
from pathlib import Path
import re
import subprocess
import sys


# Pinned Lean's located refutation format; parse errors independently of source text.
HEADER = re.compile(r"^(?:(.+?):([0-9]+):([0-9]+): )?(error(?:\([^)]*\))?|warning|information): (.*)$")
ERROR_MARKER = re.compile(r"(?:^\s*|:\s)error(?:\([^)]*\))?:")
INFRA_OR_ECHO = re.compile(r"^\s*(?:Killed\b|out of memory\b|OOM\b|memory allocation failed\b|echo:|example\s*:)", re.IGNORECASE)
REFUTATION = "Tactic `native_decide` evaluated that the proposition"
UNUSED_VARIABLE = re.compile(r"^(?:unused variable(?: `[^`]+`)?|Variable name `[^`]+` is not explicitly referenced\.)$")
UNUSED_HINT = "Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:"
UNUSED_NOTE = "Note: This linter can be disabled with `set_option linter.unusedVariables false`"
UNUSED_SUGGESTION = re.compile(r"^  \[apply\] _[A-Za-z0-9_]+$")


def is_semantic_rejection(exit_code, output):
    if exit_code != 1:
        return False
    lines = output.splitlines()
    headers = []
    for index, line in enumerate(lines):
        if INFRA_OR_ECHO.match(line):
            return False
        header = HEADER.fullmatch(line)
        if ERROR_MARKER.search(line) and header is None:
            return False
        if header is not None:
            if INFRA_OR_ECHO.match(header.group(5)) or not header.group(1) or not header.group(1).endswith(".lean"):
                return False
            headers.append((index, header))
    if not headers or any(line.strip() for line in lines[:headers[0][0]]):
        return False
    errors = 0
    for pos, (index, header) in enumerate(headers):
        end = headers[pos+1][0] if pos+1 < len(headers) else len(lines)
        body = [line for line in lines[index+1:end] if line.strip()]
        if header.group(4) == "warning":
            if not UNUSED_VARIABLE.fullmatch(header.group(5)):
                return False
            if any(line not in (UNUSED_HINT, UNUSED_NOTE) and not UNUSED_SUGGESTION.fullmatch(line)
                   for line in body):
                return False
            continue
        if header.group(4) != "error" or header.group(5) != REFUTATION:
            return False
        if len(body) < 2 or body[-1].strip() != "is false":
            return False
        if any(not line.startswith("  ") for line in body[:-1]):
            return False
        errors += 1
    return errors > 0


def changed_once(source, pattern, replacement):
    result, count = re.subn(pattern, replacement, source)
    if count != 1:
        raise AssertionError(f"mutation anchor must match once: {pattern!r}, got {count}")
    return result


def mutants(generated):
    step = (generated / "step.lean").read_text()
    target = re.search(r"\| dispatch([0-9]+) ", step).group(1)
    # A replacement selector is lost, causing a terminating but incorrect else-arm exit.
    yield "dropped_selector", changed_once(step,
        rf"(with dispatchValue{target} := )dispatchValue", r"\g<1>(2 : BitVec 8)")
    # Entry selection must use the argument, not a fixed different branch.
    yield "wrong_initial", changed_once(step,
        rf"(with dispatchValue{target} := )p0", r"\g<1>(2 : BitVec 8)")
    nested = (generated / "nested.lean").read_text()
    ids = re.findall(r"\| dispatch([0-9]+) ", nested)
    if len(ids) != 2:
        raise AssertionError("nested fixture must have exactly two typed dispatch exits")
    outer, inner = ids
    # Redirect the inner self-jump to the outer loop's exit-producing branch.
    yield "wrong_target", changed_once(nested,
        rf"pure \(.dispatch{inner} \(0 : BitVec 8\)\)",
        f"pure (.dispatch{outer} (2 : BitVec 8))")
    capture = (generated / "blockCapture.lean").read_text()
    # Drop an extracted block-result capture while keeping the emitted source well typed.
    yield "dropped_capture", changed_once(capture,
        r"pure \(.ret i([0-9]+)\)", "pure (.ret (BitVec.ofNat 8 11))")


def main():
    generated, output = map(Path, sys.argv[1:])
    output.mkdir(parents=True, exist_ok=True)
    for name, source in mutants(generated):
        path = output / (name+".lean")
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "-R", str(output), str(path)],
            capture_output=True, text=True, timeout=60)
        diagnostics = result.stdout+result.stderr
        if result.returncode == 0:
            raise AssertionError(f"semantic mutant survived: {name}")
        if not is_semantic_rejection(result.returncode, diagnostics):
            raise AssertionError(f"mutant failed for an unexpected reason: {name}\n{diagnostics}")
        print(f"dispatch semantic mutant rejected: {name}")


if __name__ == "__main__":
    main()
