#!/usr/bin/env python3
"""CLI regressions for `undefined` constant operands, for a root-built translator.

A partly `undefined` constant that a store writes is explicit undefined bytes; every other
`undefined` operand is rejected with a stable `unsupported_semantics` diagnostic. None is
replaced by a default. Never builds or invokes compilers: the fixtures in air/0.16.0 are
hand-written AIR in the exporter's schema.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
GEN = HERE / "UndefOperands" / "Gen.lean"
# The fixtures are schema-11 AIR: translating them needs the explicit legacy profile.
ARGS = ["--namespace", "UndefOperands", "--prefix", "undef_operands.", "--profile", "legacy-abi64-le"]
REJECTED = "is outside the subset (`undefined` is never read as a default"


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
    with tempfile.TemporaryDirectory(prefix="air2lean-undef-operands-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker):
    """CLI rejection with `marker`; `--diagnostics-json` reports it as unsupported semantics."""
    with tempfile.TemporaryDirectory(prefix="air2lean-undef-operands-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr and REJECTED in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air"), "--profile", "legacy-abi64-le"],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        report = json.loads(diagnostics.stdout)
        hits = [e for e in report["diagnostics"] if marker in e["message"]]
        assert hits, (marker, report)
        assert all(e["code"] == "CONSTANT_FAILURE" and e["category"] == "unsupported_semantics"
                   for e in hits), hits
    return 1


def only(name, edit):
    """One fixture file, `name`, with `edit` applied to it (`edit(document)`)."""
    document = copy.deepcopy(fixtures()[name])
    edit(document)
    return {name: document}


def add_type(document, ty):
    document["types"] = document["types"] + [ty]
    return len(document["types"]) - 1


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[2] / ".lake/build/bin/air2lean")
    checks = 0

    # Positive: retained translation, byte-identical, with explicit undefined bytes.
    text = accept(binary, fixtures())
    assert text == GEN.read_text(), "fresh translation differs from UndefOperands/Gen.lean"
    pair = ("Zig.storeBytes p0 4 (Zig.writeBytes (Zig.Enc.encode (({ a := (1 : BitVec 32), "
            "b := (0#32) } : Pair) : Pair)) 4 (Array.replicate 4 .undef))")
    assert pair in text, "storePair: field `b` is not undefined bytes"
    assert "(Zig.Enc.encode (({ len := (2 : BitVec 8), buf := (#v[(1 : BitVec 16), (0#16), " \
        "(3 : BitVec 16)] : Vector (BitVec 16) 3) } : Rec) : Rec)) 2 (Array.replicate 2 .undef))" in text
    # The local that receives a partly `undefined` store is a stack block, not a `Locals` value.
    assert "def localB  : Zig.MemM (BitVec 32) := do\n  let s0 ← Zig.allocStack 8 4" in text
    assert "Zig.store (α := Pair)" not in text and "local0 := ({" not in text
    checks += 1

    store = "undef_operands.storePair.json"
    local = "undef_operands.localB.json"

    # A wholly `undefined` store stays `Zig.storeUndef` (unchanged).
    def whole(d):
        d["body"][2]["args"][1] = dict(ty=2, undef=True)
    assert "Zig.storeUndef (Pair) 4 p0" in accept(binary, only(store, whole))
    checks += 1

    # A partly `undefined` value under an optional, error union or union has no byte range.
    def optional(d):
        opt = add_type(d, dict(k="optional", child=0, abi_size=8, abi_align=4))
        ptr = add_type(d, dict(d["types"][3], child=opt))
        d["body"][0]["ty"] = ptr
        d["params"] = [ptr]
        d["body"][2]["args"][1] = dict(ty=opt, some=dict(ty=0, undef=True))
    checks += reject(binary, only(store, optional), "under an optional")

    # A vector lane has no byte offset of its own here (bool vectors are bits).
    def vector(d):
        vec = add_type(d, dict(k="vector", len=2, child=0, abi_size=8, abi_align=8))
        ptr = add_type(d, dict(d["types"][3], child=vec, ptr_align=8))
        d["body"][0]["ty"] = ptr
        d["params"] = [ptr]
        d["body"][2]["args"][1] = dict(ty=vec, elems=[dict(ty=0, val="1"), dict(ty=0, undef=True)])
    checks += reject(binary, only(store, vector), "under an optional")

    # A value result: a return of a partly or wholly `undefined` value.
    def ret_partial(d):
        d["ret"] = 2
        d["body"][6]["args"] = [dict(ty=2, elems=[dict(ty=0, val="1"), dict(ty=0, undef=True)])]
    checks += reject(binary, only(local, ret_partial), "an `undefined` operand")

    def ret_whole(d):
        d["body"][6]["args"] = [dict(ty=0, undef=True)]
    checks += reject(binary, only(local, ret_whole), "an `undefined` operand")

    # Arithmetic on `undefined`.
    def arith(d):
        d["body"].insert(6, dict(id=7, tag="add_wrap", ty=0, args=[{"inst": 5}, dict(ty=0, undef=True)]))
        d["body"][7]["args"] = [{"inst": 7}]
    checks += reject(binary, only(local, arith), "an `undefined` operand")

    # `aggregate_init` with an `undefined` element.
    def aggregate(d):
        d["ret"] = 2
        d["body"].insert(6, dict(id=7, tag="aggregate_init", ty=2,
                                 args=[{"inst": 5}, dict(ty=0, undef=True)]))
        d["body"][7]["args"] = [{"inst": 7}]
    checks += reject(binary, only(local, aggregate), "an `undefined` operand")

    # A call argument: a partly `undefined` `Pair` passed by value.
    documents = fixtures()
    callee = copy.deepcopy(documents["undef_operands.localA.json"])
    fn_ty = add_type(callee, dict(k="other", name="fn () u32"))
    callee["body"][5:5] = [dict(id=8, tag="call", ty=1, callee=dict(ty=fn_ty, func="undef_operands.sink",
                                noreturn=False), args=[dict(ty=2, elems=[dict(ty=0, val="1"),
                                                                         dict(ty=0, undef=True)])])]
    sink = dict(schema=11, zig_version="0.16.0", target_endian="little", name="undef_operands.sink",
                params=[0], ret=1, body=[dict(id=0, tag="arg", ty=0, param=0),
                                         dict(id=1, tag="ret_safe", ty=2, args=[dict(ty=1, val="{}")])],
                types=[documents["undef_operands.localA.json"]["types"][2],
                       dict(k="void", abi_size=0, abi_align=1), dict(k="noreturn")])
    sink["types"][0] = copy.deepcopy(sink["types"][0])
    sink["types"][0]["fields"] = [dict(name="a", ty=3, offset=0), dict(name="b", ty=3, offset=4)]
    sink["types"].append(dict(k="int", signed=False, bits=32, abi_size=4, abi_align=4))
    checks += reject(binary, {"undef_operands.localA.json": callee, "undef_operands.sink.json": sink},
                     "an `undefined` operand")

    # A `memset` item with an `undefined` part.
    def memset(d):
        arr = add_type(d, dict(k="array", len=2, child=2, sentinel=False, abi_size=16, abi_align=4))
        ptr = add_type(d, dict(d["types"][3], child=arr))
        d["body"][0]["ty"] = ptr
        d["params"] = [ptr]
        d["body"][2] = dict(id=2, tag="memset_safe", ty=1, args=[{"inst": 0},
                            dict(ty=2, elems=[dict(ty=0, val="1"), dict(ty=0, undef=True)])])
    checks += reject(binary, only(store, memset), "a `memset` of a partly `undefined` item")

    # An `undefined` `shuffle` lane.
    def shuffle(d):
        vec = add_type(d, dict(k="vector", len=2, child=0, abi_size=8, abi_align=8))
        d["params"] = [vec]
        d["ret"] = vec
        d["body"] = [dict(id=0, tag="arg", ty=vec, param=0),
                     dict(id=1, tag="shuffle_one", ty=vec, args=[{"inst": 0}],
                          mask=[{"a": 0}, {"u": True}]),
                     dict(id=2, tag="ret_safe", ty=5, args=[{"inst": 1}])]
    checks += reject(binary, only(store, shuffle), "an `undefined` `shuffle` lane")

    print(f"{checks} undefined-operand CLI checks passed")


if __name__ == "__main__":
    main()
