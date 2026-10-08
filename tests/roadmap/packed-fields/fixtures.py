#!/usr/bin/env python3
"""Hand-written exporter-schema AIR for the L08 packed-field fixtures (README.md).

`python3 fixtures.py --write` rewrites air/0.16.0 from these builders; `test_cli.py` checks that
the committed files are exactly their output. Never runs a compiler.

Pointer types follow the compiler's `Type.packedStructFieldPtrInfo`: a field's bit offset is the
sum of the earlier fields' bit sizes (plus the base's bit offset for a bit-pointer base, whose host
it keeps); the host of a plain base is `(bits + 7) / 8` bytes on LLVM (3 for `Reg`, a
`packed struct(u24)`) or the ABI size on the self-hosted x86_64 backend (4); a byte-aligned field
whose bit size fills its ABI size (`inner.c`, a `u8` at bit 8) is a byte pointer.
"""
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
PREFIX = "packed_fields."


def integer(bits, signed=False, size=1, align=1):
    return dict(k="int", signed=signed, bits=bits, abi_size=size, abi_align=align)


def ptr(child, align, host=0, bit=None):
    t = dict(k="ptr", size="one", const=False, child=child, ptr_align=align, volatile=False,
             allowzero=False, sentinel=False, host_size=host, abi_size=8, abi_align=8)
    if host:
        t["bit_offset"] = bit
    return t


# Type ids (comments: the Zig types).
VOID, NORET, U4, U8, I5, BOOL, U2, MODE, INNER, REG = range(10)
P_REG, P_A, P_INNER, P_C, P_B, P_S, P_ON, P_MODE = range(10, 18)
U24, WORD, P_WORD, P_RAW, P_A_ABI, P_INNER_ABI = range(18, 24)
TYPES = [
    dict(k="void", abi_size=0, abi_align=1),
    dict(k="noreturn"),
    integer(4), integer(8), integer(5, signed=True), dict(k="bool", abi_size=1, abi_align=1),
    integer(2),
    # const Mode = enum(u2) { off, low, high };
    dict(k="enum", name="packed_fields.Mode", tag=U2, exhaustive=True,
         fields=[dict(name="off", value="0"), dict(name="low", value="1"), dict(name="high", value="2")],
         abi_size=1, abi_align=1),
    # const Inner = packed struct(u12) { b: u4, c: u8 };
    dict(k="struct", name="packed_fields.Inner", layout="packed",
         fields=[dict(name="b", ty=U4), dict(name="c", ty=U8)], abi_size=2, abi_align=2),
    # const Reg = packed struct(u24) { a: u4, inner: Inner, s: i5, on: bool, mode: Mode };
    dict(k="struct", name="packed_fields.Reg", layout="packed",
         fields=[dict(name="a", ty=U4), dict(name="inner", ty=INNER), dict(name="s", ty=I5),
                 dict(name="on", ty=BOOL), dict(name="mode", ty=MODE)], abi_size=4, abi_align=4),
    ptr(REG, 4),                 # *Reg
    ptr(U4, 4, 3, 0),            # &reg.a: *align(4:0:3) u4
    ptr(INNER, 4, 3, 4),         # &reg.inner: *align(4:4:3) Inner (crosses bytes 0 and 1)
    ptr(U8, 1),                  # &reg.inner.c: *u8 (bit 4 + 4 = 8, byte 1)
    ptr(U4, 4, 3, 4),            # &reg.inner.b: *align(4:4:3) u4
    ptr(I5, 4, 3, 16),           # &reg.s
    ptr(BOOL, 4, 3, 21),         # &reg.on
    ptr(MODE, 4, 3, 22),         # &reg.mode
    integer(24, size=4, align=4),
    # const Word = packed union { reg: Reg, raw: u24 };
    dict(k="union", name="packed_fields.Word", layout="packed",
         fields=[dict(name="reg", ty=REG), dict(name="raw", ty=U24)], abi_size=4, abi_align=4),
    ptr(WORD, 4),                # *Word
    ptr(U24, 4),                 # &word.raw
    ptr(U4, 4, 4, 0),            # &reg.a on x86_64: host = ABI size
    ptr(INNER, 4, 4, 4),         # &reg.inner on x86_64
]
GLOBALS = [
    # var reg: Reg = undefined; var word: Word = undefined;
    dict(name="packed_fields.reg", ty=REG, const=False, threadlocal=False, extern=False, init=dict(ty=REG, undef=True)),
    dict(name="packed_fields.word", ty=WORD, const=False, threadlocal=False, extern=False, init=dict(ty=WORD, undef=True)),
]


def g(index, ty):
    return dict(ty=ty, ptr=dict(off=0, **{"global": index}))


def ref(i):
    return {"inst": i}


def c(ty, val):
    return dict(ty=ty, val=str(val))


def undef(ty):
    return dict(ty=ty, undef=True)


def body(*ops):
    """`ops`: (tag, ty, args, extra) without ids; ids are the positions."""
    return [dict(id=i, tag=tag, ty=ty, args=list(args), **extra) for i, (tag, ty, args, extra) in enumerate(ops)]


def op(tag, ty, *args, **extra):
    return (tag, ty, args, extra)


def fp(index, ty, base):
    if index > 3:  # AIR has `struct_field_ptr_index_0` to `_3`, then `struct_field_ptr`.
        return op("struct_field_ptr", ty, base, index=index)
    return op(f"struct_field_ptr_index_{index}", ty, base)


def store(p, v):
    return op("store_safe", VOID, p, v)


def ret(v):
    return op("ret_safe", NORET, v)


REG_G, WORD_G = g(0, P_REG), g(1, P_WORD)

# name -> (return type, body); the Zig source is in README.md.
FUNCTIONS = {
    # reg.a = 5; return reg.a;  (the rest of the host is undefined)
    "setA": (U4, body(fp(0, P_A, REG_G), store(ref(0), c(U4, 5)), op("load", U4, ref(0)), ret(ref(2)))),
    # reg.a = 1; reg.inner.c = 0xAB; return reg.inner.c;  (a byte pointer under a bit-pointer)
    "innerC": (U8, body(fp(0, P_A, REG_G), store(ref(0), c(U4, 1)), fp(1, P_INNER, REG_G),
                        fp(1, P_C, ref(2)), store(ref(3), c(U8, 0xAB)), op("load", U8, ref(3)),
                        ret(ref(5)))),
    # reg.a = 1; reg.inner.c = 0xAB; return reg.a;
    "innerCKeepsA": (U4, body(fp(0, P_A, REG_G), store(ref(0), c(U4, 1)), fp(1, P_INNER, REG_G),
                              fp(1, P_C, ref(2)), store(ref(3), c(U8, 0xAB)), op("load", U4, ref(0)),
                              ret(ref(5)))),
    # reg.inner = .{ .b = 2, .c = 0x5A }; return reg.inner;  (12 bits across two bytes)
    "setInner": (INNER, body(fp(1, P_INNER, REG_G), store(ref(0), c(INNER, 0x5A2)),
                             op("load", INNER, ref(0)), ret(ref(2)))),
    # reg.inner.c = 0x5A; return reg.inner;  (`b` is still undefined)
    "innerPartial": (INNER, body(fp(1, P_INNER, REG_G), fp(1, P_C, ref(0)), store(ref(1), c(U8, 0x5A)),
                                 op("load", INNER, ref(0)), ret(ref(3)))),
    # reg.a = 3; reg.inner.b = undefined; return reg.a;  (same byte as `b`)
    "undefKeepsA": (U4, body(fp(0, P_A, REG_G), store(ref(0), c(U4, 3)), fp(1, P_INNER, REG_G),
                             fp(0, P_B, ref(2)), store(ref(3), undef(U4)), op("load", U4, ref(0)),
                             ret(ref(5)))),
    # reg.inner.b = 7; reg.inner.b = undefined; return reg.inner.b;
    "undefField": (U4, body(fp(1, P_INNER, REG_G), fp(0, P_B, ref(0)), store(ref(1), c(U4, 7)),
                            store(ref(1), undef(U4)), op("load", U4, ref(1)), ret(ref(4)))),
    # reg.s = -3; return reg.s;
    "signedS": (I5, body(fp(2, P_S, REG_G), store(ref(0), c(I5, -3)), op("load", I5, ref(0)), ret(ref(2)))),
    # reg.on = true; return reg.on;
    "boolOn": (BOOL, body(fp(3, P_ON, REG_G), store(ref(0), c(BOOL, "true")), op("load", BOOL, ref(0)),
                          ret(ref(2)))),
    # reg.mode = .high; return reg.mode;
    "modeHigh": (MODE, body(fp(4, P_MODE, REG_G), store(ref(0), dict(ty=MODE, enum="2")),
                            op("load", MODE, ref(0)), ret(ref(2)))),
    # word.raw = 0x123456; word.reg.a = 0xF; return word.raw;
    "unionRaw": (U24, body(fp(1, P_RAW, WORD_G), store(ref(0), c(U24, 0x123456)), fp(0, P_REG, WORD_G),
                           fp(0, P_A, ref(2)), store(ref(3), c(U4, 0xF)), op("load", U24, ref(0)),
                           ret(ref(5)))),
    # word.raw = 0xC00000; return word.reg.mode;  (tag 3 has no name)
    "unionBadMode": (MODE, body(fp(1, P_RAW, WORD_G), store(ref(0), c(U24, 0xC00000)), fp(0, P_REG, WORD_G),
                                fp(4, P_MODE, ref(2)), op("load", MODE, ref(3)), ret(ref(4)))),
    # reg.a = 9; reg.inner = .{ .b = 1, .c = 2 }; return reg.a;  (x86_64 host widths)
    "hostAbi": (U4, body(fp(0, P_A_ABI, REG_G), store(ref(0), c(U4, 9)), fp(1, P_INNER_ABI, REG_G),
                         store(ref(2), c(INNER, 0x21)), op("load", U4, ref(0)), ret(ref(4)))),
    # var r: Reg = undefined; r.a = 6; r.inner.b = undefined; return r.a;  (a stack block)
    "localUndef": (U4, body(op("alloc", P_REG), fp(0, P_A, ref(0)), store(ref(1), c(U4, 6)),
                            fp(1, P_INNER, ref(0)), fp(0, P_B, ref(3)), store(ref(4), undef(U4)),
                            op("load", U4, ref(1)), ret(ref(6)))),
}


def document(name, ret_ty, insts):
    return dict(schema=11, zig_version="0.16.0", target_endian="little", name=PREFIX + name, params=[],
                ret=ret_ty, body=copy.deepcopy(insts), globals=copy.deepcopy(GLOBALS),
                types=copy.deepcopy(TYPES))


def fixtures():
    """File name -> document."""
    return {f"{PREFIX}{name}.json": document(name, r, b) for name, (r, b) in FUNCTIONS.items()}


def render(doc):
    return json.dumps(doc, indent=1) + "\n"


def main():
    if sys.argv[1:] != ["--write"]:
        sys.exit("usage: fixtures.py --write")
    AIR.mkdir(parents=True, exist_ok=True)
    for old in AIR.glob("*.json"):
        old.unlink()
    for name, doc in fixtures().items():
        (AIR / name).write_text(render(doc))


if __name__ == "__main__":
    main()
