#!/usr/bin/env python3
"""CLI regressions for comptime-resolved locals (Q01 fuzz seeds 18, 19, 39).

Sema leaves a `bitcast` of address 0 for the dead `alloc` and stores of a comptime-known local
whose value it moved to a constant global. The translator drops these placeholders when only
other placeholders and debug instructions read them, and rejects a read one. Runs no compiler:
the fixtures are the committed AIR in air/0.16.0, edited in memory.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
GEN = HERE / "ConstLocals" / "Gen.lean"
ARGS = ["--namespace", "ConstLocals", "--prefix", "const_locals."]
MARKER = "address-0 placeholder"


def fixtures():
    return {p.name: json.loads(p.read_text()) for p in sorted(AIR.glob("*.json"))}


def translate(binary, documents, directory):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-const-locals-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-const-locals-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (result.returncode, result.stderr)
        assert MARKER in result.stderr, result.stderr
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air")],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        report = json.loads(diagnostics.stdout)
        assert any(MARKER in entry["message"] and entry["code"] == "INSTRUCTION_FAILURE"
                   for entry in report["diagnostics"]), report


def body(documents, name):
    return documents[f"const_locals.{name}.json"]["body"]


def placeholders(insts):
    return [i["id"] for i in insts if i["tag"] == "bitcast"
            and i["args"] == [{"ty": i["args"][0].get("ty"), "val": "0"}]]


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else ".lake/build/bin/air2lean").resolve()
    # The committed AIR and sources are the ones provenance.json records.
    provenance = json.loads((HERE / "provenance.json").read_text())
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    committed = sorted(HERE.glob("air*/0.16.0/*.json"))
    assert {str(p.relative_to(HERE)): digest(p) for p in committed} == provenance["air_sha256"]
    assert {n: digest(HERE / n) for n in provenance["sources_sha256"]} == provenance["sources_sha256"]
    base = fixtures()
    # The exporter output really has the placeholders, in `dead` and `live`.
    assert len(placeholders(body(base, "dead"))) == 3
    assert len(placeholders(body(base, "live"))) == 3
    # The retained translation, byte for byte: no placeholder survives as `Zig.ptrFromAddr 0`,
    # `dead` stays pointer-free, `live` passes the global base of its constant.
    text = accept(binary, base)
    assert text == GEN.read_text()
    assert "Zig.ptrFromAddr ((0" not in text
    assert "def dead (p0 : BitVec 32) (p1 : BitVec 32) : Zig.Result (BitVec 32)" in text
    assert "read (⟨some 1, 0⟩ : Zig.Ptr) p0" in text
    assert "instance : Zig.Enc F where" in text
    # A placeholder that a live instruction reads is rejected, directly or through a
    # projection of it.
    direct = copy.deepcopy(base)
    insts = body(direct, "live")
    call = next(i for i in insts if i["tag"] == "call")
    call["args"][0] = {"inst": placeholders(insts)[0]}
    reject(binary, direct)
    projected = copy.deepcopy(base)
    insts = body(projected, "live")
    field = next(i for i in insts if i["tag"] == "struct_field_ptr_index_1")
    ret = next(i for i in insts if i["tag"] == "ret_safe")
    child = projected["const_locals.live.json"]["types"][field["ty"]]["child"]
    load = {"id": 100, "tag": "load", "ty": child, "args": [{"inst": field["id"]}]}
    insts.insert(insts.index(ret), load)
    reject(binary, projected)
    print("const-locals CLI checks passed")


if __name__ == "__main__":
    main()
