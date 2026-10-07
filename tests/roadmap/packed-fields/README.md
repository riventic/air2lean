# Packed fields and bit-pointers (L08)

A bit-pointer access reads and writes the field's bits only, with defined-bit masks
(`ZigLean/Packed.lean` §Defined bits): every other bit of the host keeps its state, defined or
undefined, and a store of `undefined` makes only the field's bits undefined. The checker compares
each exporter pointer to a packed struct field with the layout that the model computes and rejects
a mismatch with `PACKED_LAYOUT` (`docs/generated-code.md` §Packed structs).

The fixture is hand-written AIR in the exporter's schema (`air/0.16.0`, written by
`fixtures.py --write`; pointer types follow the compiler's `Type.packedStructFieldPtrInfo`) for:

```zig
const Mode = enum(u2) { off, low, high };
const Inner = packed struct(u12) { b: u4, c: u8 };
const Reg = packed struct(u24) { a: u4, inner: Inner, s: i5, on: bool, mode: Mode };
const Word = packed union { reg: Reg, raw: u24 };
var reg: Reg = undefined;
var word: Word = undefined;
export fn setA() u4 { reg.a = 5; return reg.a; }
export fn innerC() u8 { reg.a = 1; reg.inner.c = 0xAB; return reg.inner.c; }
export fn innerCKeepsA() u4 { reg.a = 1; reg.inner.c = 0xAB; return reg.a; }
export fn setInner() Inner { reg.inner = .{ .b = 2, .c = 0x5A }; return reg.inner; }
export fn innerPartial() Inner { reg.inner.c = 0x5A; return reg.inner; }
export fn undefKeepsA() u4 { reg.a = 3; reg.inner.b = undefined; return reg.a; }
export fn undefField() u4 { reg.inner.b = 7; reg.inner.b = undefined; return reg.inner.b; }
export fn signedS() i5 { reg.s = -3; return reg.s; }
export fn boolOn() bool { reg.on = true; return reg.on; }
export fn modeHigh() Mode { reg.mode = .high; return reg.mode; }
export fn unionRaw() u24 { word.raw = 0x123456; word.reg.a = 0xF; return word.raw; }
export fn unionBadMode() Mode { word.raw = 0xC00000; return word.reg.mode; }
export fn hostAbi() u4 { reg.a = 9; reg.inner = .{ .b = 1, .c = 2 }; return reg.a; } // x86_64 hosts
export fn localUndef() u4 { var r: Reg = undefined; r.a = 6; r.inner.b = undefined; return r.a; }
```

`Reg`'s bit-pointers have the LLVM host width, 3 bytes (`(24 + 7) / 8`); `hostAbi` uses the
self-hosted x86_64 host, the ABI size (4). `&reg.inner` crosses bytes 0 and 1; `&reg.inner.c`
(bit 4 + 4 = 8, a `u8`) is a byte pointer to byte 1 of the host.

`PackedFields/Gen.lean` is the retained translation. `PackedFields/Proofs.lean` runs each function
from `mem0` (`decide +kernel`): `setA` returns 5 with the rest of the host undefined; `innerC`
returns `0xAB` and `innerCKeepsA` 1; `setInner` reads the 12-bit field back; `innerPartial` and
`undefField` throw `.unspecified`; `undefKeepsA` returns 3; `signedS`, `boolOn`, `modeHigh`,
`unionRaw` (`0x12345F`), `hostAbi` and `localUndef` return their values; `unionBadMode` throws
`.illegal`. `ZigLean/PackedLemmas.lean` proves the general frame.

`test_cli.py` checks the retained translation byte for byte, and rejects (CLI and
`--diagnostics-json`, output untouched) a wrong `bit_offset`, a wrong `host_size`, a nested
bit-pointer that does not keep its base's host or offset, a byte pointer to an unaligned field
and a byte-pointer field exported at the wrong bit (`PACKED_LAYOUT`), and a field past its host
(`TYPE_FAILURE`).

```sh
lake build air2lean ZigLean ZigLean.PackedLemmas
bash tests/roadmap/packed-fields/check.sh
```

Scope: hand-written AIR only; no fresh compiler export and no native execution. Packed unions as
fields of packed structs, float and pointer fields, partly `undefined` packed constants and
big-endian targets remain outside the subset.
