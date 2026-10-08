#!/usr/bin/env python3
"""L09 lane reads through a bit-packed vector pointer (`lane_reads.zig`).

Positive: the committed 0.16.0 and 0.15.2 AIR translates to a lane-pointer read
(`Zig.loadLane`) or a whole-vector read (`Zig.load` of the vector, then its lane), never to a
byte-strided item read; kernel-checked runs give the native values.
Negative: hand-made `ptr_elem_val` reads through `*@Vector(8, u3)` / `*@Vector(5, bool)` (comptime
and runtime index) and `ptr_elem_ptr` with a runtime index into a bit-packed vector are rejected
with their diagnostic, for every supported Zig version.

Usage: test_lane_reads.py AIR2LEAN_BINARY   (run from the repository root; uses `lake env lean`)
"""
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
AIR = HERE / "air-reads"
VERSIONS = ("0.16.0", "0.15.2", "0.14.1")
NOT_STRIDED = "a pointer to a lane of a vector whose lanes are not byte-strided"
BOOL_LANE = "a pointer to a lane of a `bool` vector is outside the subset"
LANE_MISMATCH = "a lane pointer whose type does not match its vector and comptime lane"
LANE_TYPE = "a pointer to a vector lane (vector_index) is outside the subset"

CHECKS = """
private def memoryValue {α : Type} (r : Zig.MemM α) : Option α :=
  ((r.run {}).run.bind Except.toOption).map Prod.fst

-- `lane_reads.zig`'s native test: lane 5 of 0..7 is 5, lane 3 of (f, t, f, t, f) is true.
example : (memoryValue (do
    let p ← Zig.alloc .stack 4 4
    Zig.store 4 p (⟨#v[0, 1, 2, 3, 4, 5, 6, 7]⟩ : Zig.Vec (BitVec 3) 8)
    R.u3Read p)).map BitVec.toNat = some 5 := by decide +kernel
example : memoryValue (do
    let p ← Zig.alloc .stack 1 1
    Zig.store 1 p (⟨#v[false, true, false, true, false]⟩ : Zig.Vec Bool 5)
    R.boolRead p) = some true := by decide +kernel
"""


def translate(binary, air, out):
    return subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "R",
                           "--prefix", "lane_reads."], capture_output=True, text=True, timeout=60)


def positives(binary, work):
    checks = 0
    for version, read in (("0.16.0", "Zig.loadLane (BitVec 3) 3 1 15"),
                          ("0.15.2", "Zig.load (Zig.Vec (BitVec 3) 8) 4")):
        gen = work / f"Gen-{version}.lean"
        result = translate(binary, AIR / version, gen)
        assert result.returncode == 0, (version, result.stderr)
        text = gen.read_text()
        assert read in text, (version, "lane read form")
        assert ".elem " not in text, (version, "byte-strided item address")
        gen.write_text(text + CHECKS)
        lean = subprocess.run(["lake", "env", "lean", str(gen)], capture_output=True, text=True,
                              timeout=600)
        assert lean.returncode == 0, (version, lean.stdout, lean.stderr)
        checks += 1
    return checks


def reject(binary, work, document, marker):
    air = work / "neg"
    if air.exists():
        for f in air.iterdir():
            f.unlink()
    air.mkdir(exist_ok=True)
    (air / "f.json").write_text(json.dumps(document))
    result = translate(binary, air, work / "neg.lean")
    assert result.returncode != 0, (marker, "accepted")
    assert marker in result.stderr + result.stdout, (marker, result.stderr)
    return 1


def negatives(binary, work):
    u3 = json.loads((AIR / "0.16.0" / "lane_reads.u3Read.json").read_text())
    boolean = json.loads((AIR / "0.16.0" / "lane_reads.boolRead.json").read_text())
    checks = 0
    for version in VERSIONS:
        for base, lane_ty, ret_conv, marker in ((u3, 5, True, NOT_STRIDED),
                                                (boolean, None, False, BOOL_LANE)):
            doc = copy.deepcopy(base)
            doc["zig_version"] = doc["profile"]["zig_version"] = version
            types = doc["types"]
            usize = next(k for k, t in enumerate(types) if t.get("k") == "int" and t["bits"] == 64)
            lane = next(k for k, t in enumerate(types) if "vector_index" in t)
            child = types[lane]["child"]
            doc["params"] = [0, usize]
            ret = doc["body"][-1]

            def body(read):
                tail = [read]
                if ret_conv:
                    tail.append(dict(id=20, tag="intcast", ty=doc["ret"], args=[dict(inst=10)]))
                result = dict(inst=20 if ret_conv else 10)
                return [dict(id=0, tag="arg", ty=0, param=0), dict(id=1, tag="arg", ty=usize, param=1),
                        *tail, dict(id=30, tag=ret["tag"], ty=ret["ty"], args=[result])]

            # `ptr_elem_val` through the vector pointer, comptime and runtime index.
            for index in (dict(ty=usize, val="3"), dict(inst=1)):
                doc["body"] = body(dict(id=10, tag="ptr_elem_val", ty=child, args=[dict(inst=0), index]))
                checks += reject(binary, work, doc, marker)
            if lane_ty is None:
                continue
            # `ptr_elem_ptr` with a runtime index: as a lane pointer to lane 5, as a 0.14.1/0.15.2
            # runtime lane pointer, and as a plain `*u3` item pointer.
            def elem_ptr(ptr_ty):
                return [dict(id=0, tag="arg", ty=0, param=0), dict(id=1, tag="arg", ty=usize, param=1),
                        dict(id=5, tag="ptr_elem_ptr", ty=ptr_ty, args=[dict(inst=0), dict(inst=1)]),
                        dict(id=10, tag="load", ty=child, args=[dict(inst=5)]),
                        dict(id=20, tag="intcast", ty=doc["ret"], args=[dict(inst=10)]),
                        dict(id=30, tag=ret["tag"], ty=ret["ty"], args=[dict(inst=20)])]
            doc["body"] = elem_ptr(lane)
            checks += reject(binary, work, doc, LANE_MISMATCH)
            runtime = copy.deepcopy(doc)
            runtime["types"][lane]["vector_index"] = "runtime"
            checks += reject(binary, work, runtime, LANE_TYPE)
            plain = copy.deepcopy(doc)
            plain["types"][lane].update(host_size=0)
            plain["types"][lane].pop("bit_offset")
            plain["types"][lane].pop("vector_index")
            checks += reject(binary, work, plain, NOT_STRIDED)
            # A comptime lane pointer whose index differs from its type's lane.
            doc["body"] = elem_ptr(lane)
            doc["body"][2]["args"][1] = dict(ty=usize, val="4")
            checks += reject(binary, work, doc, LANE_MISMATCH)
    return checks


def main():
    [binary] = sys.argv[1:]
    with tempfile.TemporaryDirectory(prefix="air2lean-lane-reads-") as directory:
        work = Path(directory)
        checks = positives(binary, work) + negatives(binary, work)
    print(f"lane reads: {checks} positive and negative checks passed")


if __name__ == "__main__":
    main()
