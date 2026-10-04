#!/usr/bin/env python3
"""Positive/mutation driver for a root-built translator; never builds or invokes compilers."""
import copy
import json
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


def run(binary, documents, error=None):
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for k, document in enumerate(documents):
            text = document if isinstance(document, str) else json.dumps(document, ensure_ascii=False)
            (air / f"{k}.json").write_text(text)
        output = directory / "Gen.lean"
        output.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(output), "--namespace", "Validation"],
                                text=True, capture_output=True, check=False)
        if error is not None:
            assert result.returncode == 1, (error, result.returncode, result.stderr)
            assert error in result.stderr, (error, result.stderr)
            assert output.read_text() == "sentinel\n", "rejected input replaced output"
        else:
            assert result.returncode == 0, result.stderr
            assert output.read_text().startswith("-- air2lean-profile: ")
    return 1



def run_sparse(binary):
    # A terabyte logical file must be rejected from metadata, without reading its zeros.
    with tempfile.TemporaryDirectory(prefix="air2lean-input-validation-sparse-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        with (air / "huge.json").open("wb") as source:
            source.truncate(1 << 40)
        output = directory / "Gen.lean"
        output.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(output), "--namespace", "Validation"],
                                text=True, capture_output=True, check=False, timeout=10)
        assert result.returncode == 1, (result.returncode, result.stderr)
        assert "UTF-8 bytes" in result.stderr, result.stderr
        assert output.read_text() == "sentinel\n", "sparse rejection replaced output"
    return 1


def global_(name, ty, value, const=False):
    return dict(name=name, ty=ty, const=const, threadlocal=False, extern=False, init=value)


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
    timer_type = dict(k="struct", name="time.Timer", layout="auto", fields=[dict(name="started", ty=1, offset=0)],
                      abi_size=8, abi_align=8)
    timer = function("timerRead", [dict(pointer, child=2), integer(64), timer_type, NORETURN], [0], 1, [
        inst(0, "arg", 0, param=0), inst(1, "call", 1, [dict(inst=0)], callee=dict(func="time.Timer.read", noreturn=False)),
        inst(2, "ret", 3, [dict(inst=1)])])
    checks += run(binary, [timer])
    mutate = copy.deepcopy(timer)
    mutate["types"][2]["name"] = "OtherTimer"
    checks += run(binary, [mutate], "Timer pointer/u64")
    mutate = copy.deepcopy(timer)
    mutate["types"][0]["const"] = True
    checks += run(binary, [mutate], "Timer pointer/u64")
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
    checks += run(binary, [raw[:-1] + ',"extra":"' + 'a' * (64 * 1024 * 1024) + '"}'], "UTF-8 bytes")
    mutate = copy.deepcopy(TARGET)
    mutate["types"][1] = dict(k="float", bits=1048576)
    mutate["body"] = [inst(0, "arg", 1, param=0), inst(1, "ret", 2,
                       [dict(ty=1, fbits="0x" + "f" * 262144)])]
    checks += run(binary, [mutate], "float type of 1048576 bits is outside the subset")
    checks += run_sparse(binary)
    print(f"{checks} whole-program CLI positive/mutation checks passed")


if __name__ == "__main__":
    main()
