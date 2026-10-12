#!/usr/bin/env python3
"""L-series long tail CLI regressions for a built translator (`test_cli.py <air2lean>`).

Each case edits a committed compiler export and requires a stable rejection (or, for an
accepted shape, the translation). Never builds or invokes a compiler.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def fixtures(stem, version="0.16.0"):
    return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air" / stem / version).glob("*.json"))}


TABLE = "error-table.air2lean"


def table(stem, version="0.16.0"):
    return json.loads((HERE / "air" / stem / version / TABLE).read_text())


def translate(binary, documents, directory, args):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        # A file that is not a function (the error numbering) keeps its own name.
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *args], text=True,
                            capture_output=True, check=False, timeout=120)
    return result, out


def reject(binary, documents, args, marker):
    with tempfile.TemporaryDirectory(prefix="air2lean-lang-long-tail-") as d:
        result, out = translate(binary, documents, Path(d), args)
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"


def accept(binary, documents, args):
    with tempfile.TemporaryDirectory(prefix="air2lean-lang-long-tail-") as d:
        result, out = translate(binary, documents, Path(d), args)
        assert result.returncode == 0, result.stderr
        return out.read_text()


def walk(body):
    for inst in body:
        yield inst
        for value in inst.values():
            if isinstance(value, list) and value and isinstance(value[0], dict) and "tag" in value[0]:
                yield from walk(value)
        for case in inst.get("cases", []):
            yield from walk(case["body"])


def drop_arg(document, param):
    """The function without an `arg` of `param`: an unread `arg` is removed; a read one reads
    another parameter's slot instead (the body refers to it)."""
    args = [i for i in document["body"] if i["tag"] == "arg" and i["param"] == param]
    rest = json.dumps([i for i in document["body"] if i not in args])
    other = next(i["param"] for i in document["body"] if i["tag"] == "arg" and i["param"] != param)
    for inst in args:
        if json.dumps({"inst": inst["id"]}) in rest:
            inst["param"] = other
        else:
            document["body"].remove(inst)


# --- L10: error values as runtime parameters --------------------------------------------------

EP = ["--namespace", "ErrorParams", "--prefix", "error_params."]


def error_params(binary):
    docs = fixtures("error_params")
    # The export of `orBoom(x, e: error{Boom})` has an `arg` for each parameter. Without the
    # error parameter's `arg` (as if the one-name set had one possible value), the args no longer
    # match the runtime parameters and the function is rejected, never renumbered.
    dropped = copy.deepcopy(docs)
    drop_arg(dropped["error_params.orBoom.json"], 1)
    reject(binary, dropped, EP, "AIR args do not match non-OPV runtime parameters (1 args, 2 slots)")
    # A `u0` parameter has one possible value: its slot keeps no `arg`; a one-field `enum(u8)`
    # does not, nor does a one-field `union(enum(u8))` (its tag is stored), so an export without
    # their `arg` is rejected.
    u8 = {"k": "int", "signed": False, "bits": 8, "abi_size": 1, "abi_align": 1}
    void = {"k": "void", "abi_size": 0, "abi_align": 1}
    for name, ok in (("u0", True), ("enum(u8)", False), ("union(enum(u8))", False)):
        edited = copy.deepcopy(docs)
        doc = edited["error_params.skipFirst.json"]
        types = doc["types"]
        if name == "u0":
            ty = {"k": "int", "signed": False, "bits": 0, "abi_size": 0, "abi_align": 1}
        else:
            types.append(u8)
            ty = {"k": "enum", "name": "error_params.One", "module": "root", "tag": len(types) - 1,
                  "exhaustive": True, "fields": [{"name": "only", "value": "7"}], "abi_size": 1, "abi_align": 1}
            if name == "union(enum(u8))":
                types.extend([ty, void])
                ty = {"k": "union", "name": "error_params.U", "module": "root", "layout": "auto",
                      "tag": len(types) - 2, "fields": [{"name": "only", "ty": len(types) - 1}],
                      "abi_size": 1, "abi_align": 1}
        types.append(ty)
        doc["params"][0] = len(doc["types"]) - 1
        drop_arg(doc, 0)
        edited.pop("error_params.viaFail.json")
        if ok:
            accept(binary, edited, EP)
        else:
            reject(binary, edited, EP, "AIR args do not match non-OPV runtime parameters (1 args, 2 slots)")


# --- L09: Zig ≤0.16 `@bitCast` with a vector side -------------------------------------------

VC = ["--namespace", "VectorCasts", "--prefix", "vector_casts."]


def one(stem, name):
    return {name: fixtures(stem)[name]}


def vector_casts(binary):
    # Array items that do not fill whole bytes cast to a vector of another item type: 0.16.0
    # copies item by item into lanes of another type, no representation cast.
    docs = one("vector_casts", "vector_casts.bytesToHalves.json")
    doc = docs["vector_casts.bytesToHalves.json"]
    doc["types"][4] = {"k": "int", "signed": False, "bits": 4, "abi_size": 1, "abi_align": 1}
    doc["types"][0] = dict(doc["types"][0], len=8, abi_size=8)
    reject(binary, docs, VC, "source items do not fill whole bytes")
    # Equal bit sizes are required (`@bitSizeOf`): `[4]u8` (32 bits) to `@Vector(4, u16)`.
    docs = one("vector_casts", "vector_casts.bytesToHalves.json")
    doc = docs["vector_casts.bytesToHalves.json"]
    doc["types"][1] = dict(doc["types"][1], len=4, abi_size=8, abi_align=8)
    reject(binary, docs, VC, "between types of 32 and 64 bits")
    # Non-byte lanes in memory are the LLVM backend's image only: another backend is rejected.
    docs = one("vector_casts", "vector_casts.packedLanesToInt.json")
    docs["vector_casts.packedLanesToInt.json"]["profile"]["backend"] = "stage2_x86_64"
    reject(binary, docs, VC + ["--allow-unqualified-build-mode"], "LLVM backend")


ES = ["--namespace", "ExternStorage", "--prefix", "extern_storage."]
EI = ["--namespace", "ErrorInts", "--prefix", "error_ints."]
RL = ["--namespace", "RuntimeLanes", "--prefix", "runtime_lanes."]
FL = ["--namespace", "FloatLanes", "--prefix", "float_lanes."]


def global_named(doc, name):
    return next(g for g in doc["globals"] if g.get("name") == name)


def extern_storage(binary):
    # Pointer-bearing externs are accepted; a function pointer is not (an indirect call
    # dispatches on the program's address-taken functions).
    docs = one("extern_storage", "extern_storage.slotValue.json")
    accept(binary, docs, ES)
    doc = docs["extern_storage.slotValue.json"]
    slot = global_named(doc, "ext_slot")
    doc["types"].append({"k": "other", "name": "fn () callconv(.c) void"})
    doc["types"].append(dict(doc["types"][slot["ty"]], child=len(doc["types"]) - 1))
    slot["ty"] = len(doc["types"]) - 1
    reject(binary, docs, ES, "its type can hold a function pointer")
    # Error storage stays rejected.
    docs = one("extern_storage", "extern_storage.counter.json")
    doc = docs["extern_storage.counter.json"]
    doc["types"].append({"k": "error_set", "errors": ["Boom"], "abi_size": 2, "abi_align": 2})
    global_named(doc, "ext_counter")["ty"] = len(doc["types"]) - 1
    reject(binary, docs, ES, "its type holds error storage")
    # A pointer-bearing extern in a program with error-bearing globals: the finite
    # error-storage fragment tracks every pointer into those.
    docs = one("extern_storage", "extern_storage.slotValue.json")
    doc = docs["extern_storage.slotValue.json"]
    doc["types"].append({"k": "error_set", "errors": ["Boom"], "abi_size": 2, "abi_align": 2})
    doc["globals"].append({"name": "extern_storage.boom", "module": "root", "ty": len(doc["types"]) - 1,
                           "const": False, "extern": False, "threadlocal": False,
                           "init": {"ty": len(doc["types"]) - 1, "err": "Boom"}})
    reject(binary, docs, ES, "the program has error-bearing globals")


def error_ints(binary):
    funcs = fixtures("error_ints")
    numbering = table("error_ints")
    accept(binary, {**funcs, TABLE: numbering}, EI)
    # No numbering beside the AIR files: integer/error casts are rejected, never guessed.
    reject(binary, funcs, EI, "needs the compilation's error numbering")
    # A numbering of another compilation (version, width) or naming an error twice.
    reject(binary, {**funcs, TABLE: dict(numbering, zig_version="0.15.2")}, EI,
           "error-table.air2lean is of Zig 0.15.2")
    reject(binary, {**funcs, TABLE: dict(numbering, error_set_bits=8)}, EI, "with 8-bit errors")
    reject(binary, {**funcs, TABLE: dict(numbering, names=numbering["names"] + numbering["names"][:1])},
           EI, "an error name occurs twice")
    # More errors than the error integer has codes.
    narrow = {name: copy.deepcopy(d) for name, d in funcs.items()}
    for d in narrow.values():
        d["profile"]["error_set_bits"] = 7
        for t in d["types"]:
            if t.get("k") == "int" and t.get("bits") == 16 and not t.get("signed"):
                t.update(bits=7, abi_size=1, abi_align=1)
            if t.get("k") in ("error_set",):
                t.update(abi_size=1, abi_align=1)
    reject(binary, {**narrow, TABLE: dict(numbering, error_set_bits=7)}, EI, "more than the 127 codes")


def runtime_lanes(binary):
    docs = {"runtime_lanes.setU9.json": fixtures("runtime_lanes", "0.15.2")["runtime_lanes.setU9.json"]}
    accept(binary, docs, RL)
    # The lane store follows the LLVM backend's bit-packed layout: another backend is rejected.
    other = copy.deepcopy(docs)
    other["runtime_lanes.setU9.json"]["profile"]["backend"] = "stage2_x86_64"
    reject(binary, other, RL + ["--allow-unqualified-build-mode"], "runtime-index vector lane store")
    # A runtime lane pointer that is read is not dropped and stays rejected.
    read = copy.deepcopy(docs)
    doc = read["runtime_lanes.setU9.json"]
    for inst in walk(doc["body"]):
        if inst["tag"] == "vector_store_elem":
            lane_ptr = next(i for i in walk(doc["body"]) if i["tag"] == "ptr_elem_ptr")
            inst["tag"] = "store"
            inst["args"] = [{"inst": lane_ptr["id"]}, inst["args"][2]]
    reject(binary, read, RL, "a pointer to a vector lane (vector_index)")


def float_lanes(binary):
    docs = one("float_lanes", "float_lanes.middle.json")
    accept(binary, docs, FL)
    other = copy.deepcopy(docs)
    other["float_lanes.middle.json"]["profile"]["backend"] = "stage2_x86_64"
    reject(binary, other, FL + ["--allow-unqualified-build-mode"], "LLVM backend")


def main():
    binary = Path(sys.argv[1]).resolve()
    error_params(binary)
    vector_casts(binary)
    extern_storage(binary)
    error_ints(binary)
    runtime_lanes(binary)
    float_lanes(binary)
    print("lang-long-tail test_cli: ok")


if __name__ == "__main__":
    main()
