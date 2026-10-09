#!/usr/bin/env python3
"""Positive/mutation driver for a root-built translator; never builds or invokes compilers."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def integer(bits=32):
    return dict(k="int", signed=False, bits=bits, abi_size=(bits + 7) // 8, abi_align=(bits + 7) // 8)


def function(name, types, params, ret, body, globals=()):
    return dict(schema=11, zig_version="0.16.0", target_endian="little", name=name,
                types=types, params=params, ret=ret, body=body, globals=list(globals))


def inst(i, tag, ty, args=(), **extra):
    return dict(id=i, tag=tag, ty=ty, args=list(args), **extra)


VOID = dict(k="void", abi_size=0, abi_align=1)
NORETURN = dict(k="noreturn")
CALLER = function("caller", [integer(), VOID, NORETURN], [0], 0, [
    inst(0, "arg", 0, param=0),
    inst(1, "call", 0, [dict(inst=0)], callee=dict(func="target", noreturn=False)),
    inst(2, "ret", 2, [dict(inst=1)])])
TARGET = function("target", [VOID, integer(), NORETURN], [1], 1, [
    inst(0, "arg", 1, param=0), inst(1, "ret", 2, [dict(inst=0)])])


def invoke(binary, air, output, error=None, timeout=10):
    output.write_text("sentinel\n")
    # Every fixture here is schema-11 AIR: translating it needs the explicit legacy profile.
    result = subprocess.run([str(binary), str(air), "-o", str(output), "--namespace", "Validation",
                             "--profile", "legacy-abi64-le"],
                            text=True, capture_output=True, check=False, timeout=timeout)
    if error is not None:
        assert result.returncode == 1, (error, result.returncode, result.stderr)
        assert error in result.stderr, (error, result.stderr)
        assert output.read_text() == "sentinel\n", "rejected input replaced output"
    else:
        assert result.returncode == 0, result.stderr
        assert output.read_text().startswith("-- air2lean-profile: ")
    return 1


def run(binary, documents, error=None):
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for k, document in enumerate(documents):
            text = document if isinstance(document, str) else json.dumps(document, ensure_ascii=False)
            (air / f"{k}.json").write_text(text)
        return invoke(binary, air, directory / "Gen.lean", error)


def run_sparse(binary, size=1 << 40):
    # Reject oversized logical files from metadata, without reading their sparse zeros.
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-sparse-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        with (air / "huge.json").open("wb") as source:
            source.truncate(size)
        return invoke(binary, air, directory / "Gen.lean", "UTF-8 bytes", timeout=10)


def run_file_kind(binary, kind):
    assert kind in ("fifo", "symlink")
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-kind-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        source = air / "input.json"
        if kind == "fifo":
            # No writer: opening this FIFO would block before the byte-limit check.
            os.mkfifo(source)
        else:
            target = directory / "target.json"
            target.write_text(json.dumps(TARGET))
            source.symlink_to(target)
        error = "must be a regular file" if kind == "fifo" else None
        return invoke(binary, air, directory / "Gen.lean", error, timeout=3)


def global_(name, ty, value, const=False):
    return dict(name=name, ty=ty, const=const, threadlocal=False, extern=False, init=value)


MISSING = object()
LANE_ERROR = "a pointer to a vector lane (vector_index) is outside the subset"
UNVERIFIED_ERROR = "is a bit-pointer without `vector_index` in the AIR file"


def bit_pointer(child, host_size, bit_offset, vector_index=MISSING):
    """`*align(2:bit_offset:host_size[:vector_index]) child`; MISSING: an older export."""
    entry = dict(k="ptr", size="one", const=False, child=child, ptr_align=2, volatile=False,
                 allowzero=False, sentinel=False, host_size=host_size, bit_offset=bit_offset,
                 abi_size=8, abi_align=8)
    if vector_index is not MISSING:
        entry["vector_index"] = vector_index
    return entry


def diagnose(binary, document, marker):
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-diag-") as directory:
        air = Path(directory) / "air"
        air.mkdir()
        (air / "0.json").write_text(json.dumps(document))
        result = subprocess.run([str(binary), "--diagnostics-json", str(air),
                                 "--profile", "legacy-abi64-le"], text=True,
                                capture_output=True, check=False, timeout=10)
        assert result.returncode != 0, (marker, result.stdout)
        assert marker in result.stdout, (marker, result.stdout, result.stderr)
    return 1


def lane_pointers(binary):
    """`&v[2]` of a `@Vector(4, u9)` is `*align(2:0:4:2) u9`: lane count 4 as host_size. Without
    `vector_index` it has the shape of a packed field pointer into a 4-byte host integer."""
    checks = 0
    u9 = integer(9)
    u9["abi_size"] = u9["abi_align"] = 2

    def param(vector_index):
        return function("laneParam", [u9, bit_pointer(0, 4, 0, vector_index), NORETURN], [1], 0, [
            inst(0, "arg", 1, param=0), inst(1, "load", 0, [dict(inst=0)]),
            inst(2, "ret", 2, [dict(inst=1)])])

    def loaded(vector_index):
        holder = dict(k="ptr", size="one", const=True, child=1, ptr_align=8, volatile=False,
                      allowzero=False, sentinel=False, host_size=0, abi_size=8, abi_align=8)
        return function("laneLoaded", [u9, bit_pointer(0, 4, 0, vector_index), holder, NORETURN], [2], 0, [
            inst(0, "arg", 2, param=0), inst(1, "load", 1, [dict(inst=0)]),
            inst(2, "load", 0, [dict(inst=1)]), inst(3, "ret", 3, [dict(inst=2)])])

    # (a) A lane pointer parameter: an explicit lane index (or 0.14.1/0.15.2 "runtime") is
    # rejected as a lane pointer; an older export without the field is rejected as unverifiable.
    for index in (2, 0, "runtime"):
        checks += run(binary, [param(index)], LANE_ERROR)
    checks += run(binary, [param(MISSING)], "laneParam: near line 0: a parameter " + UNVERIFIED_ERROR)
    # (c) The same pointer loaded from memory: rejected at the load, whichever export.
    checks += run(binary, [loaded(2)], LANE_ERROR)
    checks += run(binary, [loaded(MISSING)], "a value not made by a packed `struct_field_ptr` " + UNVERIFIED_ERROR)
    # The collecting `--diagnostics-json` checker applies the same rules.
    for document, marker in ((param(MISSING), UNVERIFIED_ERROR), (loaded(MISSING), UNVERIFIED_ERROR),
                             (loaded(2), LANE_ERROR)):
        checks += diagnose(binary, document, marker)
    # A malformed field is rejected, not read as absent.
    for bad in ("2", -1, True):
        checks += run(binary, [param(bad)], "vector_index must be null, a lane index or \"runtime\"")
    # (b) A packed field pointer: `vector_index: null` (current exporter) is a packed field
    # pointer, also as a parameter or loaded value.
    checks += run(binary, [param(None)])
    checks += run(binary, [loaded(None)])
    # Exact retained packed-struct goldens (no `vector_index`): their bit-pointers are all made by
    # `struct_field_ptr` of a packed struct, and stay accepted.
    root = Path(__file__).resolve().parents[3]
    for name in ("layout/air/layout.bumpPair.json", "0.15.2/layout/air/layout.bumpPair.json",
                 "0.14.1/layout/air/layout.isOk.json", "sync/air/Io.Condition.signal.json"):
        golden = json.loads((root / "tests/golden" / name).read_text())
        assert any(t.get("host_size", 0) and "vector_index" not in t for t in golden["types"]), name
        checks += run(binary, [golden])
    # The same golden function: a bit-pointer it did not make by `struct_field_ptr` is rejected.
    golden = json.loads((root / "tests/golden/layout/air/layout.bumpPair.json").read_text())
    bit_types = [k for k, t in enumerate(golden["types"]) if t.get("host_size", 0)]
    projection = next(i for i in golden["body"] if i["ty"] in bit_types)
    projection["tag"], projection["args"] = "bitcast", [dict(inst=0)]
    checks += run(binary, [golden], "a value not made by a packed `struct_field_ptr` " + UNVERIFIED_ERROR)
    return checks


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    checks = run(binary, [CALLER, TARGET])
    mutate = copy.deepcopy(TARGET)
    mutate["params"] = []
    mutate["body"] = [inst(0, "ret", 2, [dict(ty=1, val="7")])]
    checks += run(binary, [CALLER, mutate], "expected 0")
    mutate = copy.deepcopy(TARGET)
    mutate["types"][1] = integer(64)
    checks += run(binary, [CALLER, mutate], "incompatible result type")
    mutate = copy.deepcopy(TARGET)
    mutate["types"].append(dict(k="bool", abi_size=1, abi_align=1))
    mutate["params"] = [3]
    mutate["body"] = [inst(0, "arg", 3, param=0), inst(1, "ret", 2, [dict(ty=1, val="7")])]
    checks += run(binary, [CALLER, mutate], "incompatible argument 0")
    checks += run(binary, [TARGET, TARGET], "duplicate function name")
    mutate = copy.deepcopy(TARGET)
    mutate["params"] = [99]
    mutate["body"][0]["ty"] = 99
    checks += run(binary, [mutate], "unknown type id 99")
    mutate = copy.deepcopy(TARGET)
    mutate["body"][0]["ty"] = 0
    checks += run(binary, [mutate], "arg type does not match its runtime parameter")
    mutate = copy.deepcopy(TARGET)
    mutate["body"] = [inst(0, "arg", 1, param=0), inst(1, "ret", 2, [dict(ty=0, val="{}")])]
    checks += run(binary, [mutate], "incompatible result type")
    pointer = dict(k="ptr", size="one", const=False, child=0, abi_size=8, abi_align=8, ptr_align=8)
    self_a = function("globalA", [pointer, VOID, NORETURN], [], 1,
                      [inst(0, "ret", 2, [dict(ty=1, val="{}")])],
                      [global_("shared.state", 0, dict(ty=0, ptr={"global": 0, "off": 0}))])
    self_b = copy.deepcopy(self_a)
    self_b["name"] = "globalB"
    self_b["types"] = [VOID, dict(pointer, child=1), NORETURN]
    self_b["ret"] = 0
    self_b["body"][0]["args"] = [dict(ty=0, val="{}")]
    self_b["globals"][0]["ty"] = 1
    self_b["globals"][0]["init"]["ty"] = 1
    checks += run(binary, [self_a, self_b])
    for key, value in [("const", True), ("init", dict(ty=1, ptr={"global": 0, "off": 8}))]:
        mutate = copy.deepcopy(self_b)
        mutate["globals"][0][key] = value
        checks += run(binary, [self_a, mutate], "inconsistent shared global 'shared.state'")
    mutate = copy.deepcopy(self_a)
    mutate["globals"][0]["name"] = "globalA"
    checks += run(binary, [mutate], "collides with a function name")
    mutate = copy.deepcopy(self_a)
    del mutate["globals"][0]["name"]
    checks += run(binary, [mutate], "unnamed mutable global")
    # Follow pointers through distinct local global indices; changing only the referenced
    # initializer must be rejected, rather than comparing the pointer's raw index.
    head_pointer = dict(pointer, child=1, ptr_align=4)
    chain_a = function("chainA", [head_pointer, integer(), VOID, NORETURN], [], 2,
                       [inst(0, "ret", 3, [dict(ty=2, val="{}")])], [
                           global_("shared.head", 0, dict(ty=0, ptr={"global": 1, "off": 0})),
                           global_("shared.tail", 1, dict(ty=1, val="7"))])
    chain_b = copy.deepcopy(chain_a)
    chain_b["name"] = "chainB"
    chain_b["globals"].insert(0, dict(ty=1, const=True, init=dict(ty=1, val="9")))
    chain_b["globals"][1]["init"]["ptr"]["global"] = 2
    checks += run(binary, [chain_a, chain_b])
    mutate = copy.deepcopy(chain_b)
    mutate["globals"][2]["init"]["val"] = "8"
    checks += run(binary, [chain_a, mutate], "inconsistent shared global 'shared.head'")
    mutate = copy.deepcopy(chain_a)
    mutate["globals"][0]["init"]["ptr"]["global"] = 99
    checks += run(binary, [mutate], "unknown global id 99")
    named = dict(k="struct", name="Pair", layout="auto", fields=[dict(name="value", ty=1, offset=0)],
                 abi_size=4, abi_align=4, offsets=[0])
    typed_a = copy.deepcopy(chain_a)
    typed_a["types"].append(named)
    typed_a["params"] = [4]
    typed_a["body"] = [inst(0, "arg", 4, param=0), inst(1, "ret", 3, [dict(ty=2, val="{}")])]
    typed_b = copy.deepcopy(typed_a)
    typed_b["name"] = "typedB"
    checks += run(binary, [typed_a, typed_b])
    mutate = copy.deepcopy(typed_b)
    mutate["types"][-1]["fields"][0]["name"] = "other"
    checks += run(binary, [typed_a, mutate], "inconsistent shared type 'Pair'")
    # Valid function pointers still use typed instructions and known indirect targets.
    fn_type = dict(k="other", name="fn (u32) u32")
    fn_pointer = dict(pointer, const=True, child=1, ptr_align=1)
    indirect = function("indirect", [integer(), fn_type, fn_pointer, VOID, NORETURN], [2, 0], 0, [
        inst(0, "arg", 2, param=0), inst(1, "arg", 0, param=1),
        inst(2, "call", 0, [dict(inst=1)], callee=dict(inst=0)),
        inst(3, "ret", 4, [dict(inst=2)])],
        [global_("target", 1, dict(func="target", noreturn=False), const=True)])
    checks += run(binary, [indirect, TARGET])
    mutate = copy.deepcopy(TARGET)
    mutate["params"] = []
    mutate["body"] = [inst(0, "ret", 2, [dict(ty=1, val="7")])]
    checks += run(binary, [indirect, mutate], "expected 0")
    sink = function("sink", [fn_type, fn_pointer, VOID, NORETURN], [1], 2,
                    [inst(0, "arg", 1, param=0), inst(1, "ret", 3, [dict(ty=2, val="{}")])])
    pointer_caller = function("pointerCaller", [fn_type, fn_pointer, VOID, NORETURN], [1], 2, [
        inst(0, "arg", 1, param=0),
        inst(1, "call", 2, [dict(inst=0)], callee=dict(func="sink", noreturn=False)),
        inst(2, "ret", 3, [dict(ty=2, val="{}")])])
    # fn_pointer's child index is adjusted for this table.
    for document in (sink, pointer_caller):
        document["types"][1] = dict(fn_pointer, child=0)
    checks += run(binary, [pointer_caller, sink])
    allocator = function("allocation", [dict(k="struct", name="mem.Allocator"), integer(),
        dict(pointer, child=1, ptr_align=4),
        dict(k="error_union", error=4, payload=2, abi_size=16, abi_align=8),
        dict(k="error_set", errors=["OutOfMemory"], abi_size=2, abi_align=2), VOID, NORETURN], [0], 3, [
            inst(0, "arg", 0, param=0), inst(1, "call", 3, [dict(inst=0)],
                callee=dict(func="mem.Allocator.create__anon_1", noreturn=False)),
            inst(2, "ret", 6, [dict(inst=1)])])
    checks += run(binary, [allocator])
    mutate = copy.deepcopy(allocator)
    mutate["body"][1]["args"].append(dict(ty=1, val="0"))
    checks += run(binary, [mutate], "argument count")
    mutate = copy.deepcopy(allocator)
    mutate["body"][1]["args"] = [dict(ty=1, val="0")]
    checks += run(binary, [mutate], "allocator argument")
    for errors in ([], ["Unrelated"]):
        mutate = copy.deepcopy(allocator)
        mutate["types"][4]["errors"] = errors
        checks += run(binary, [mutate], "error set admitting OutOfMemory")
    open_allocator = copy.deepcopy(allocator)
    open_allocator["types"][4]["any"] = True
    checks += run(binary, [open_allocator])
    for model in ("alloc", "alignedAlloc", "dupe"):
        allocation = copy.deepcopy(allocator)
        allocation["name"] = "allocation_" + model
        allocation["types"][2] = dict(pointer, size="slice", child=1, ptr_align=4, abi_size=16)
        allocation["types"][3]["abi_size"] = 24
        allocation["types"].append(integer(64))
        argument = 2 if model == "dupe" else 7
        allocation["params"] = [0, argument]
        allocation["body"] = [inst(0, "arg", 0, param=0), inst(1, "arg", argument, param=1),
            inst(2, "call", 3, [dict(inst=0), dict(inst=1)],
                 callee=dict(func=f"mem.Allocator.{model}__anon_1", noreturn=False)),
            inst(3, "ret", 6, [dict(inst=2)])]
        checks += run(binary, [allocation])
        allocation["types"][4]["errors"] = ["Unrelated"]
        checks += run(binary, [allocation], "error set admitting OutOfMemory")
    # The existing qualified ret_ptr/ret_load example stays valid, while changing only
    # its declared return to u32 must fail before producing an ill-typed Gen.lean.
    golden = Path(__file__).resolve().parents[3] / "tests/golden/layout/air/layout.wordOf.json"
    loaded = json.loads(golden.read_text())
    checks += run(binary, [loaded])
    loaded["ret"] = 0
    checks += run(binary, [loaded], "loaded return has an incompatible result type")
    # A third file must not inherit equality cached for the first two file tables.
    chain_c = copy.deepcopy(chain_b)
    chain_c["name"] = "chainC"
    checks += run(binary, [chain_a, chain_b, chain_c])
    chain_c["globals"][2]["init"]["val"] = "8"
    checks += run(binary, [chain_a, chain_b, chain_c], "inconsistent shared global 'shared.head'")
    nested = function("nested", [integer(), VOID, NORETURN,
        dict(k="array", len=1, child=0, sentinel=False, abi_size=4, abi_align=4)], [], 1,
        [inst(0, "ret", 2, [dict(ty=1, val="{}")])],
        [global_("nested.constant", 3, dict(ty=3, elems=[dict(ty=0, val="7")]), const=True)])
    checks += run(binary, [nested])
    nested["globals"][0]["init"]["elems"][0]["val"] = "-1"
    checks += run(binary, [nested], "integer constant does not fit")
    timer_type = dict(k="struct", name="time.Timer", layout="auto", fields=[dict(name="started", ty=1, offset=0)],
                      abi_size=8, abi_align=8)
    timer = function("timerRead", [dict(pointer, child=2), integer(64), timer_type, NORETURN], [0], 1, [
        inst(0, "arg", 0, param=0), inst(1, "call", 1, [dict(inst=0)], callee=dict(func="time.Timer.read", noreturn=False)),
        inst(2, "ret", 3, [dict(inst=1)])])
    # `std.time.Timer` exists (and its model row is reviewed) up to Zig 0.15.2 only.
    timer["zig_version"] = "0.15.2"
    checks += run(binary, [timer])
    mutate = copy.deepcopy(timer)
    mutate["types"][2]["name"] = "OtherTimer"
    checks += run(binary, [mutate], "Timer pointer/u64")
    mutate = copy.deepcopy(timer)
    mutate["types"][0]["const"] = True
    checks += run(binary, [mutate], "Timer pointer/u64")
    # Successful header type equality must not suppress initializer value comparisons.
    error_a = function("errorA", [dict(k="error_set", errors=["Left", "Right"], abi_size=2, abi_align=2),
        VOID, NORETURN, dict(k="error_union", error=0, payload=1, abi_size=2, abi_align=2)], [], 1,
        [inst(0, "ret", 2, [dict(ty=1, val="{}")])],
        [global_("error.state", 3, dict(ty=3, err="Left"), const=True)])
    error_b = copy.deepcopy(error_a)
    error_b["name"] = "errorB"
    checks += run(binary, [error_a, error_b])
    error_b["globals"][0]["init"]["err"] = "Right"
    checks += run(binary, [error_a, error_b], "inconsistent shared global 'error.state'")
    aggregate_a = copy.deepcopy(nested)
    aggregate_a["globals"][0]["init"]["elems"][0]["val"] = "7"
    aggregate_b = copy.deepcopy(aggregate_a)
    aggregate_b["name"] = "nestedB"
    checks += run(binary, [aggregate_a, aggregate_b])
    aggregate_b["globals"][0]["init"]["elems"][0]["val"] = "8"
    checks += run(binary, [aggregate_a, aggregate_b], "inconsistent shared global 'nested.constant'")
    opaque = function("opaque", [dict(k="other", name="anyopaque"),
        dict(pointer, const=True, child=0, ptr_align=1), VOID, NORETURN], [1], 2, [
            inst(0, "arg", 1, param=0), inst(1, "call", 2, [], callee=dict(inst=0)),
            inst(2, "ret", 3, [dict(ty=2, val="{}")])])
    checks += run(binary, [opaque], "inst 1: indirect callee is not a function pointer")
    twice = copy.deepcopy(CALLER)
    twice["body"] = [inst(0, "arg", 0, param=0),
        inst(1, "call", 0, [dict(inst=0)], callee=dict(func="target", noreturn=False)),
        inst(2, "call", 0, [dict(inst=0)], callee=dict(func="target", noreturn=False)),
        inst(3, "ret", 2, [dict(inst=2)])]
    checks += run(binary, [twice, TARGET])
    for args, error in [([], "inst 2: callee 'target' has 0 arguments, expected 1"),
                        ([dict(ty=3, val="true")], "inst 2: callee 'target' has an incompatible argument 0"),
                        ([dict(func="target", noreturn=False)], "inst 2: callee 'target' argument 0: function values lack")]:
        mutate = copy.deepcopy(twice)
        mutate["body"][2]["args"] = args
        if any(arg.get("ty") == 3 for arg in args):
            mutate["types"].append(dict(k="bool", abi_size=1, abi_align=1))
        checks += run(binary, [mutate, TARGET], error)
    other_source = copy.deepcopy(CALLER)
    other_source["name"] = "otherSource"
    other_source["types"][0] = integer(64)
    checks += run(binary, [CALLER, other_source, TARGET],
                  "otherSource: inst 1: callee 'target' has an incompatible result")
    missing = copy.deepcopy(twice)
    missing["body"][2]["callee"]["func"] = "missing"
    checks += run(binary, [missing, TARGET], "callee 'missing' has no AIR file and no model")
    bool_type = dict(k="bool", abi_size=1, abi_align=1)
    bool_target = function("boolTarget", [bool_type, VOID, NORETURN], [0], 1,
        [inst(0, "arg", 0, param=0), inst(1, "ret", 2, [dict(ty=1, val="{}")])])
    bool_source = function("boolSource", [dict(bool_type, abi_align=2), VOID, NORETURN], [0], 1, [
        inst(0, "arg", 0, param=0),
        inst(1, "call", 1, [dict(ty=0, val="true")], callee=dict(func="boolTarget", noreturn=False)),
        inst(2, "ret", 2, [dict(ty=1, val="{}")])])
    checks += run(binary, [bool_source, bool_target])
    bool_source["body"][2:] = [
        inst(2, "call", 1, [dict(inst=0)], callee=dict(func="boolTarget", noreturn=False)),
        inst(3, "ret", 2, [dict(ty=1, val="{}")])]
    checks += run(binary, [bool_source, bool_target], "inst 2: callee 'boolTarget' has an incompatible argument 0")
    raw = json.dumps(TARGET)
    checks += run(binary, [raw[:-1] + ',"sch\\u0065ma":11}'], "duplicate JSON object key")
    for keys in ['"x":0,"\\u0078":1', '"😀":0,"\\ud83d\\ude00":1',
                 '"�":0,"\\ud800":1']:
        checks += run(binary, [raw[:-1] + "," + keys + "}"], "duplicate JSON object key")
    checks += run(binary, [raw.replace('"schema": 11', '"schema": 1e999999999')], "exponent exceeds")
    for exponent in ("1e999999999e9", "1e999999999.0", "1e999999999+0"):
        checks += run(binary, [raw.replace('"schema": 11', '"schema": ' + exponent)], "invalid JSON exponent")
    checks += run(binary, [raw[:-1] + ',"extra":' + '[' * 129 + '0' + ']' * 129 + '}'], "nesting exceeds")
    checks += run(binary, [raw[:-1] + ',"extra":"\\uZZZZ"}'], "invalid hex character")
    checks += run(binary, [raw[:-1] + ',"extra":01}'], "expected")
    checks += run(binary, [raw[:-1] + ',"extra":' + '9' * 1025 + '}'], "number exceeds")
    # Check actual packed field domains before their backing-bit encoding.
    for signed, values, invalid in [
            (False, ("0", "255"), ("256", "-1")),
            (True, ("-128", "127"), ("128", "-129"))]:
        packed = function("packed", [dict(integer(8), signed=signed),
            dict(k="struct", name="Packed", layout="packed", fields=[dict(name="x", ty=0)],
                 abi_size=1, abi_align=1), NORETURN], [], 1,
            [inst(0, "ret", 2, [dict(ty=1, val=".{ .x = 0 }")])])
        for value in values:
            packed["body"][0]["args"][0]["val"] = ".{ .x = " + value + " }"
            checks += run(binary, [packed])
        for value in invalid:
            packed["body"][0]["args"][0]["val"] = ".{ .x = " + value + " }"
            checks += run(binary, [packed],
                          f"packed: packed field x value {value} does not fit its integer type")
    checks += lane_pointers(binary)
    mutate = copy.deepcopy(TARGET)
    mutate["types"][1]["bits"] = 65536
    checks += run(binary, [mutate], "65535-bit limit")
    mutate = copy.deepcopy(TARGET)
    mutate["body"] = [inst(0, "arg", 1, param=0), inst(1, "ret", 2, [dict(ty=1, val="9" * 32769)])]
    checks += run(binary, [mutate], "integer literal exceeds")
    mutate = copy.deepcopy(TARGET)
    mutate["body"] = [inst(0, "arg", 1, param=0), inst(1, "ret", 2, [dict(ty=1, val="4294967296")])]
    checks += run(binary, [mutate], "integer constant does not fit")
    mutate = copy.deepcopy(typed_a)
    mutate["types"][-1]["fields"].append(dict(name="value", ty=1, offset=4))
    checks += run(binary, [mutate], "duplicate type field name")
    mutate = copy.deepcopy(allocator)
    mutate["types"][3]["error"] = 1
    checks += run(binary, [mutate], "not an error set")
    chain = copy.deepcopy(TARGET)
    chain["params"] = []
    chain["types"] = [dict(k="optional", child=n + 1) for n in range(257)] + [integer(), NORETURN]
    chain["ret"] = 0
    chain["body"] = []
    checks += run(binary, [chain], "value type traversal exceeds")
    checks += run_sparse(binary, 64 * 1024 * 1024 + 1)
    mutate = copy.deepcopy(TARGET)
    mutate["types"][1] = dict(k="float", bits=1048576)
    mutate["body"] = [inst(0, "arg", 1, param=0), inst(1, "ret", 2,
                       [dict(ty=1, fbits="0x" + "f" * 262144)])]
    checks += run(binary, [mutate], "float type of 1048576 bits is outside the subset")
    checks += run_sparse(binary)
    checks += run_file_kind(binary, "fifo")
    checks += run_file_kind(binary, "symlink")
    print(f"{checks} whole-program CLI positive/mutation checks passed")


if __name__ == "__main__":
    main()
