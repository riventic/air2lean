#!/usr/bin/env python3
"""Accept only Lean's located `decide` refutations as semantic mutant kills."""
import argparse
from pathlib import Path
import re

HEADER = re.compile(r"^(?:(.+?):(\d+):(\d+): )?(error|warning|information): (.*)$")
ERROR_MARKER = re.compile(r"(?:^|:\s)error:")
REFUTATION = "Tactic `decide` proved that the proposition"


def is_semantic_rejection(exit_code: int, output: str) -> bool:
    if exit_code != 1:
        return False
    lines = output.splitlines()
    headers = []
    for index, line in enumerate(lines):
        header = HEADER.fullmatch(line)
        if ERROR_MARKER.search(line) and header is None:
            return False
        if header is not None:
            headers.append((index, header))
    errors = 0
    for pos, (index, header) in enumerate(headers):
        if header.group(4) != "error":
            continue
        if not header.group(1) or not header.group(1).endswith(".lean"):
            return False
        if header.group(5) != REFUTATION:
            return False
        end = headers[pos + 1][0] if pos + 1 < len(headers) else len(lines)
        body = [line.strip() for line in lines[index + 1:end] if line.strip()]
        if len(body) < 2 or body[-1] != "is false":
            return False
        errors += 1
    return errors > 0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exit_code", type=int)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    if not is_semantic_rejection(args.exit_code, args.log.read_text()):
        raise SystemExit(f"not a semantic decide refutation: {args.log} (Lean exit {args.exit_code})")


if __name__ == "__main__":
    main()
