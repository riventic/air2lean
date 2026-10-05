#!/usr/bin/env python3
"""Fail closed unless pinned Lean rejects the located dispatcher equality by rfl."""
import argparse
from pathlib import Path
import re

HEADER = re.compile(r"^(?:(.+?):(\d+):(\d+): )?(error(?:\([^)]*\))?|warning|information): (.*)$")
FAILURE = "Tactic `rfl` failed: The left-hand side"
ASSERTION = "example (a b c : BitVec 8) : TuplePipeline.dispatch"


def is_semantic_rejection(exit_code: int, output: str, source: Path) -> bool:
    if exit_code != 1:
        return False
    assertions = [i for i, line in enumerate(source.read_text().splitlines(), 1)
                  if line.startswith(ASSERTION)]
    if len(assertions) != 1:
        return False
    if re.search(r"Killed|Segmentation fault|Bus error|uncaught exception|Traceback|I/O error|input/output error|failed to (?:read|open|write)", output, re.I):
        return False
    lines = output.splitlines()
    headers = []
    for i, line in enumerate(lines):
        match = HEADER.fullmatch(line)
        if re.search(r"(?:^|:\s)error(?:\([^)]*\))?:", line) and match is None:
            return False
        if match:
            headers.append((i, match))
    if not headers or any(line.strip() for line in lines[:headers[0][0]]):
        return False
    errors = 0
    for pos, (i, header) in enumerate(headers):
        if not header.group(4).startswith("error"):
            continue
        if not header.group(1) or Path(header.group(1)).resolve() != source.resolve():
            return False
        if int(header.group(2)) != assertions[0] or header.group(5) != FAILURE:
            return False
        end = headers[pos + 1][0] if pos + 1 < len(headers) else len(lines)
        body = "\n".join(lines[i + 1:end])
        if not all(part in body for part in (
                "is not definitionally equal to the right-hand side", "⊢",
                "TuplePipeline.dispatch", "TuplePipeline.worker")):
            return False
        errors += 1
    return errors == 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exit_code", type=int)
    parser.add_argument("log", type=Path)
    parser.add_argument("source", type=Path)
    args = parser.parse_args()
    if not is_semantic_rejection(args.exit_code, args.log.read_text(), args.source):
        raise SystemExit(f"not a located dispatcher equality refutation: {args.log} (Lean exit {args.exit_code})")


if __name__ == "__main__":
    main()
