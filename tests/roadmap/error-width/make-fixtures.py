#!/usr/bin/env python3
"""Write the hand-written L10 AIR fixtures for each error-code width.

The files follow the exporter schema (docs/air-json.md, schema 12). They mirror
`error_width.zig` compiled with `-OReleaseSafe -fno-error-tracing -target x86_64-linux
-mcpu=baseline` and `--error-limit LIMIT`. They are not compiler exports: no width,
including the default 16 bits, is attested by these files. Layouts follow Zig 0.16's
rules for the selected width (`Zcu.errorSetBits`, `std.zig.target.intByteSize` and
`intAlignment`, `Type.abiSize` of an error union). `check` regenerates in memory and
compares with the committed files.

usage: make-fixtures.py write|check
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROFILE = {
    "name": "abi64-le-v1", "target_triple": "x86_64-linux.5.10...6.19-gnu.2.31", "pointer_bits": 64,
    "endian": "little", "abi": "gnu", "zig_version": "0.16.0", "backend": "stage2_llvm", "cpu": "x86_64",
    "features": ["64bit", "cmov", "cx8", "fxsr", "idivq_to_divl", "macrofusion", "mmx", "nopl",
                 "slow_3ops_lea", "slow_incdec", "sse", "sse2", "vzeroupper", "x87"],
    "build_mode": "ReleaseSafe", "float_mode": "per-instruction", "error_set_bits": 16,
    "error_layout": "type-table", "error_tracing": False, "export_stage": "analyzed-air"}
# Directory -> --error-limit. The width is Zig's `Zcu.errorSetBits` of the limit.
CONFIGS = {"bits16": 65534, "bits8": 255, "bits10": 1000, "bits17": 100000}


def error_limit_bits(limit):
    """`Zcu.errorSetBits` (Zig 0.16 `src/Zcu.zig`) for a non-SPIR-V target."""
    return 0 if limit == 0 else limit.bit_length()


def int_size_align(bits):
    """`intByteSize`/`intAlignment` on x86_64 for 1..64 bits."""
    align = 1 if bits <= 8 else 2 if bits <= 16 else 4 if bits <= 32 else 8
    size = -(-((bits + 7) // 8) // align) * align
    return size, align


def forward(n, a):
    return -(-n // a) * a


def union_layout(bits, psize, palign):
    """`Type.abiSize`/`abiAlignment` of `E!T` whose payload has runtime bits."""
    csize, calign = int_size_align(bits)
    if calign > palign:
        size = forward(forward(csize, palign) + psize, calign)
    else:
        size = forward(forward(psize, calign) + csize, palign)
    return size, max(calign, palign)


def ptr(child, align):
    return {"k": "ptr", "size": "one", "const": False, "child": child, "ptr_align": align,
            "volatile": False, "allowzero": False, "sentinel": False, "host_size": 0,
            "abi_size": 8, "abi_align": 8}


def types_for(bits):
    csize, calign = int_size_align(bits)
    s8, a8 = union_layout(bits, 1, 1)
    s64, a64 = union_layout(bits, 8, 8)
    return [
        {"k": "error_set", "errors": ["Bad", "Other"], "abi_size": csize, "abi_align": calign},  # 0 E
        ptr(0, calign),                                                                          # 1 *E
        {"k": "void", "abi_size": 0, "abi_align": 1},                                            # 2
        {"k": "noreturn"},                                                                       # 3
        {"k": "optional", "child": 0, "abi_size": csize, "abi_align": calign},                   # 4 ?E
        ptr(4, calign),                                                                          # 5 *?E
        {"k": "int", "signed": False, "bits": 8, "abi_size": 1, "abi_align": 1},                 # 6 u8
        {"k": "error_union", "error": 0, "payload": 6, "abi_size": s8, "abi_align": a8},         # 7 E!u8
        ptr(7, a8),                                                                              # 8
        ptr(6, 1),                                                                               # 9 *u8
        {"k": "int", "signed": False, "bits": 64, "abi_size": 8, "abi_align": 8},                # 10 u64
        {"k": "error_union", "error": 0, "payload": 10, "abi_size": s64, "abi_align": a64},      # 11 E!u64
        ptr(11, a64),                                                                            # 12
        ptr(10, 8),                                                                              # 13 *u64
        {"k": "bool", "abi_size": 1, "abi_align": 1},                                            # 14
    ]


def inst(i, tag, ty, *args, **extra):
    out = {"id": i, "tag": tag, "ty": ty}
    if args:
        out["args"] = [{"inst": a} for a in args]
    out.update(extra)
    return out


def try_body(base, cell, union):
    return [inst(base, "unwrap_errunion_err_ptr", 0, cell),
            inst(base + 1, "wrap_errunion_err", union, base),
            inst(base + 2, "ret_safe", 3, base + 1)]


def try_union(cell_ty, union_ty, payload_ptr, payload_ty):
    return [inst(0, "arg", cell_ty, param=0), inst(1, "arg", union_ty, param=1),
            inst(2, "store_safe", 2, 0, 1),
            inst(6, "try_ptr", payload_ptr, 0, body=try_body(3, 0, union_ty)),
            inst(7, "load", payload_ty, 6), inst(8, "wrap_errunion_payload", union_ty, 7),
            inst(9, "ret_safe", 3, 8)]


# name -> (params, ret, body); the Zig source of each is in error_width.zig.
FUNCTIONS = {
    "storeError": ([1, 0], 0, [
        inst(0, "arg", 1, param=0), inst(1, "arg", 0, param=1),
        inst(2, "store_safe", 2, 0, 1), inst(3, "load", 0, 0), inst(4, "ret_safe", 3, 3)]),
    "storeOptional": ([5, 4], 14, [
        inst(0, "arg", 5, param=0), inst(1, "arg", 4, param=1),
        inst(2, "store_safe", 2, 0, 1), inst(3, "is_non_null_ptr", 14, 0), inst(4, "ret_safe", 3, 3)]),
    "loadOptional": ([5], 4, [
        inst(0, "arg", 5, param=0), inst(1, "load", 4, 0), inst(2, "ret_safe", 3, 1)]),
    "unionTry8": ([8, 7], 7, try_union(8, 7, 9, 6)),
    "unionTry64": ([12, 11], 11, try_union(12, 11, 13, 10)),
    "setPayload": ([8, 6], 14, [
        inst(0, "arg", 8, param=0), inst(1, "arg", 6, param=1),
        inst(2, "errunion_payload_ptr_set", 9, 0), inst(3, "store_safe", 2, 2, 1),
        inst(4, "is_err_ptr", 14, 0), inst(5, "ret_safe", 3, 4)]),
    "loadUnion": ([8], 7, [
        inst(0, "arg", 8, param=0), inst(1, "load", 7, 0), inst(2, "ret_safe", 3, 1)]),
}


def document(bits, name, params, ret, body):
    return {"schema": 12, "zig_version": "0.16.0", "target_endian": "little",
            "profile": dict(PROFILE, error_set_bits=bits),
            "name": f"error_width.{name}", "params": params, "ret": ret, "body": body,
            "types": types_for(bits)}


def render():
    out = {}
    for directory, limit in CONFIGS.items():
        bits = error_limit_bits(limit)
        for name, (params, ret, body) in FUNCTIONS.items():
            text = json.dumps(document(bits, name, params, ret, body), indent=1) + "\n"
            out[HERE / "air" / directory / f"error_width.{name}.json"] = text
    return out


def main():
    if sys.argv[1:] not in (["write"], ["check"]):
        raise SystemExit(__doc__)
    assert [error_limit_bits(n) for n in CONFIGS.values()] == [16, 8, 10, 17]
    files = render()
    if sys.argv[1] == "write":
        for path, text in files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return
    committed = set((HERE / "air").rglob("*.json"))
    if committed != set(files):
        raise SystemExit(f"fixture inventory differs: {sorted(map(str, committed ^ set(files)))}")
    for path, text in files.items():
        if path.read_text() != text:
            raise SystemExit(f"stale fixture: {path}")
    print(f"error-width fixtures current: {len(files)} files")


if __name__ == "__main__":
    main()
