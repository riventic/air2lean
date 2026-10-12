#!/usr/bin/env python3
"""CLI regressions for A01's environment reads, memory inputs and memory-region contracts.

`air-env/<version>` are fresh exports of `asm_env.zig` (provenance.json). The 0.17.0 translation
is the retained `AsmEnv/Gen.lean`; 0.16.0 and 0.15.2 translate to the same text apart from the
profile header. Mutations outside the reviewed allowlist entries (`Air2Lean/AsmAllowlist.lean`)
are rejected, and a device contract that declares `rdtsc` keeps it a device event (L13).
Never builds or invokes compilers.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ARGS = ["--namespace", "AsmEnv", "--prefix", "asm_env.", "--profile", "abi64-le-v1"]
TSC = HERE.parent / "volatile-effects" / "tsc.json"


def load(version):
    return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air-env" / version).glob("*.json"))}


def run(binary, documents, extra=()):
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-env-") as d:
        air = Path(d) / "air"
        air.mkdir()
        for name, document in documents.items():
            (air / name).write_text(json.dumps(document))
        out = Path(d) / "Gen.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS, *extra], text=True,
                                capture_output=True, check=False, timeout=120)
        return result, out.read_text()


def body(text):
    return "\n".join(text.splitlines()[1:])


def asm_inst(doc):
    stack = list(doc["body"])
    while stack:
        i = stack.pop()
        if i["tag"] == "assembly":
            return i
        for k in ("body", "then", "else"):
            stack.extend(i.get(k, []))
    raise AssertionError("no assembly")


def reject(binary, docs, name, mutate, marker):
    docs = json.loads(json.dumps(docs))
    mutate(asm_inst(docs[name]), docs[name])
    result, text = run(binary, {name: docs[name]})
    assert result.returncode == 1 and text == "sentinel\n", (name, marker, result.stderr)
    assert marker in result.stderr, (marker, result.stderr)
    return 1


def main(binary):
    checks = 0
    retained = (HERE / "AsmEnv" / "Gen.lean").read_text()
    for version in ("0.17.0", "0.16.0", "0.15.2"):
        result, text = run(binary, load(version))
        assert result.returncode == 0, (version, result.stderr)
        if version == "0.17.0":
            assert text == retained, "AsmEnv/Gen.lean is not the fresh 0.17.0 translation"
        assert body(text) == body(retained), version
        checks += 1
    docs = load("0.17.0")
    # Environment reads are oracle queries, never opaques; region contracts read and write.
    for token in ("Zig.Asm.envWord 64", "Zig.Asm.readRegion", "Zig.Asm.writeRegion", "Zig.Asm.movePtr"):
        assert token in retained, token
        checks += 1
    # A pointer operand whose block no allowlisted region names.
    checks += reject(binary, docs, "asm_env.fill.json",
                     lambda i, _: i.update(source="rep stosw"), "nor an allowlist entry declares its memory regions")
    # A `memory` clobber with pointer operands needs the region entry: dropping it is another block.
    checks += reject(binary, docs, "asm_env.copy.json",
                     lambda i, _: i.update(clobbers=[]), "nor a read-write pointer that an allowlisted memory region uses")
    # The region's base must be read-write: a write-only pointer output would make a pointer.
    def write_only(i, _):
        i["outputs"][0]["constraint"] = "={rdi}"
    checks += reject(binary, docs, "asm_env.fill.json", write_only,
                     "nor an allowlist entry declares its memory regions")
    # A memory clobber on an entry without regions stays rejected.
    def clobber(i, _):
        i["clobbers"] = ["cc", "memory"]
    checks += reject(binary, docs, "asm_env.random.json", clobber, "'memory' clobber is outside the subset")
    # An `m` input of a pointer (the operand itself, not a value) is no memory-value input.
    def ptr_input(i, d):
        i["inputs"][0]["ref"] = {"inst": 0}
    checks += reject(binary, docs, "asm_env.loadm.json", ptr_input, "not an integer register value")
    # A device contract that declares the rdtsc template keeps it a device event (L13).
    result, text = run(binary, {k: v for k, v in docs.items() if k in ("asm_env.ticks.json", "asm_env.elapsed.json")},
                       ("--device-contract", str(TSC)))
    assert result.returncode == 0, result.stderr
    assert "Zig.vasm air2lean_device" in text and "Zig.Asm.envWord" not in text, text
    checks += 1
    print(f"{checks} asm environment/region CLI checks passed")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
