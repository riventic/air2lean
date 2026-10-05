#!/usr/bin/env python3
"""Classify located evaluation refutations, not kernel proof adequacy.

The caller must first check the unmodified generated cNull baseline. This helper
binds the mutant to that baseline and the three intended assertion sites.
"""
import argparse
from pathlib import Path
import re
import sys

MAX_BYTES = 65536
ASSERTIONS = (
    "value (Nullable.cNull 0) = some true",
    "value (Nullable.cNull 1) = some false",
    "value (Nullable.cNull 18446744073709551615) = some false",
)
PREFIX = "example : "
SUFFIX = " := by native_decide"
HEADER = re.compile(r"^(.+):(\d+):(\d+): error: (.*)$")
MESSAGE = "Tactic `native_decide` evaluated that the proposition"
HELPER = "private def nullableMutation (p : Zig.Ptr) : Zig.MemM Bool := do pure (!(← Zig.ptrIsNull p))"


def make_mutant(baseline: str) -> str:
    """Keep the existing predicate inversion and reject changed fixture shapes."""
    if len(baseline.encode("utf-8")) > MAX_BYTES:
        raise ValueError("baseline exceeds classifier bound")
    examples = [line for line in baseline.splitlines() if line.lstrip().startswith("example")]
    expected = [PREFIX + proposition + SUFFIX for proposition in ASSERTIONS]
    if examples != expected or baseline.count("native_decide") != 3:
        raise ValueError("baseline assertions differ from the three cNull fixtures")
    if baseline.count("Zig.ptrIsNull") != 1 or baseline.count("import ZigLean") != 1:
        raise ValueError("mutation must target exactly one emitted predicate and import")
    if "nullableMutation" in baseline:
        raise ValueError("baseline already contains the mutation helper")
    return baseline.replace("Zig.ptrIsNull", "nullableMutation").replace(
        "import ZigLean", "import ZigLean\n" + HELPER, 1)


def is_semantic_rejection(exit_code: int, output: str, source: Path, baseline: str,
                          mutant: str) -> bool:
    if exit_code != 1:
        return False
    try:
        if (len(output.encode("utf-8")) > MAX_BYTES or
                len(mutant.encode("utf-8")) > MAX_BYTES):
            return False
        if mutant != make_mutant(baseline):
            return False
        identity = source.resolve(strict=True)
        sites = {}
        for number, line in enumerate(mutant.splitlines(), 1):
            for proposition in ASSERTIONS:
                if line == PREFIX + proposition + SUFFIX:
                    # Lean's Position.column is zero based; these lines are ASCII.
                    sites[(number, line.index("native_decide"))] = proposition
        if len(sites) != 3:
            return False
        seen = set()
        lines = output.splitlines()
        index = 0
        while index < len(lines):
            if not lines[index].strip():
                index += 1
                continue
            header = HEADER.fullmatch(lines[index])
            if header is None or header[4] != MESSAGE:
                return False
            if Path(header[1]).resolve(strict=True) != identity:
                return False
            site = (int(header[2]), int(header[3]))
            if site not in sites or site in seen:
                return False
            index += 1
            body = []
            while index < len(lines) and HEADER.fullmatch(lines[index]) is None:
                body.append(lines[index])
                index += 1
            # Accept printer line wrapping, but no extra diagnostics or crash text.
            if " ".join("\n".join(body).split()) != sites[site] + " is false":
                return False
            seen.add(site)
        return seen == set(sites)
    except (OSError, ValueError, UnicodeError):
        return False


def read_bounded(path: Path) -> str:
    with path.open("rb") as stream:
        data = stream.read(MAX_BYTES + 1)
    if len(data) > MAX_BYTES:
        raise ValueError("classifier input exceeds byte bound")
    return data.decode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exit_code", type=int)
    parser.add_argument("log", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("baseline", type=Path)
    args = parser.parse_args()
    try:
        accepted = is_semantic_rejection(args.exit_code, read_bounded(args.log),
                                         args.source, read_bounded(args.baseline),
                                         read_bounded(args.source))
    except (OSError, ValueError, UnicodeError):
        accepted = False
    if not accepted:
        print("not exactly three located nullable evaluation refutations "
              f"(Lean exit {args.exit_code})", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
