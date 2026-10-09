#!/usr/bin/env python3
"""Select the committed AIR of the std I/O fixtures (E03) from a fresh export.

usage: refresh-air.py EXPORT_DIR OUTPUT_DIR SOURCE COMPILER ROOT... [--check]

Copies the direct-call closure of ROOT (panic handlers excluded: the translator normalizes
them) and drops the bound primitives `os.linux.{read,write,close}` with the raw `syscallN`
wrappers below them: those are the ENV-03 boundary, bound through the model registry.
`--check` compares with OUTPUT_DIR instead of writing it. The provenance record
`air/provenance.json` (keyed by the AIR's Zig version) holds the source, patched compiler and
AIR hashes; it is rewritten with OUTPUT_DIR and compared with `--check`.
"""
import hashlib
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
    if len(args) < 5:
        raise SystemExit(__doc__)
    export, output, source, compiler, roots = Path(args[0]), Path(args[1]), Path(args[2]), \
        Path(args[3]), args[4:]
    selected = closure(export, roots)
    def digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    # The installed patched compiler is a lock wrapper (zig-patch/lock.sh) around zig-unlocked.
    unlocked = compiler.resolve().parent / "zig-unlocked"
    binary = unlocked if unlocked.is_file() else compiler.resolve()
    version = json.loads(next(iter(selected.values())).read_text())["zig_version"]
    record = {"source": source.name, "source_sha256": digest(source),
              "patched_compiler_sha256": digest(binary),
              "export": "x86_64-linux -mcpu=baseline -OReleaseSafe -fno-error-tracing build-obj",
              "air_sha256": {p.name: digest(p) for p in sorted(selected.values())}}
    provenance_path = output.parent / "provenance.json"
    provenance = json.loads(provenance_path.read_text()) if provenance_path.exists() else {}
    if check:
        if provenance.get(version) != record:
            print(f"refresh-air: {provenance_path} [{version}] is stale", file=sys.stderr)
            return 1
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
    provenance[version] = record
    provenance_path.write_text(json.dumps(provenance, indent=1, sort_keys=True) + "\n")
    print(f"{output}: {len(selected)} functions")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
