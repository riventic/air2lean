#!/usr/bin/env python3
"""Select the committed AIR of the std I/O fixtures (E03) from a fresh export.

usage: refresh-air.py EXPORT_DIR OUTPUT_DIR ROOT... [--check]

Copies the direct-call closure of ROOT (panic handlers excluded: the translator normalizes
them) and drops the bound primitives `os.linux.{read,write,close}` with the raw `syscallN`
wrappers below them: those are the ENV-03 boundary, bound through the model registry.
`--check` compares with OUTPUT_DIR instead of writing it.
"""
import json
from pathlib import Path
import re
import shutil
import sys

sys.dont_write_bytecode = True

BOUND = {"os.linux.read", "os.linux.write", "os.linux.close"}
CALLEE = re.compile(r'"func": "((?:[^"\\]|\\.)*)"')


def panic(name: str) -> bool:
    return name.startswith("debug.FullPanic(") or name == "debug.defaultPanic"


def closure(export: Path, roots: list[str]) -> dict[str, Path]:
    files = {}
    for path in export.glob("*.json"):
        files[json.loads(path.read_text())["name"]] = path
    seen, pending = {}, list(roots)
    while pending:
        name = pending.pop()
        if name in seen or name in BOUND or panic(name):
            continue
        if name not in files:
            raise SystemExit(f"refresh-air: {name} was not exported")
        seen[name] = files[name]
        pending += CALLEE.findall(files[name].read_text())
    return seen


def main(argv: list[str]) -> int:
    check = "--check" in argv
    args = [a for a in argv if a != "--check"]
    if len(args) < 3:
        raise SystemExit(__doc__)
    export, output, roots = Path(args[0]), Path(args[1]), args[2:]
    selected = closure(export, roots)
    if check:
        have = {p.name: p.read_bytes() for p in output.glob("*.json")}
        want = {p.name: p.read_bytes() for p in selected.values()}
        if have != want:
            print(f"refresh-air: {output} differs from the fresh export: "
                  f"{sorted(set(have) ^ set(want)) or 'contents'}", file=sys.stderr)
            return 1
        return 0
    if output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True)
    for path in selected.values():
        shutil.copy(path, output / path.name)
    print(f"{output}: {len(selected)} functions")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
