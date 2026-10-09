# Packed fields and bit-pointers (L08)

A bit-pointer access reads and writes the field's bits only, with defined-bit masks
(`ZigLean/Packed.lean` §Defined bits): every other bit of the host keeps its state, defined or
undefined, and a store of `undefined` makes only the field's bits undefined. The checker compares
each exporter pointer to a packed struct field with the layout that the model computes and rejects
a mismatch with `PACKED_LAYOUT` (`docs/generated-code.md` §Casts, layout and function pointers).

The first fixture is hand-written AIR in the exporter's schema (`air/0.16.0`, written by
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
lake build air2lean ZigLean
bash tests/roadmap/packed-fields/check.sh
```

## Compiler export

`packed_fields.zig` is the source (the Zig above, as `pub fn`s because packed types with a width
that is not a power of two are not extern compatible, plus `bytePtr` over a plain `Inner` global
and `innerCPtr`, `innerCKeepsAPtr`, `setInnerPtr` over a runtime `*Reg`). `air-fresh/0.16.0/llvm`
is its unmodified export from a patched 0.16.0 compiler (`compiler-provenance.json`: build tree
and command) and `air-fresh/0.16.0/x86_64` is `hostAbi` from the self-hosted x86_64 backend
(`-fno-llvm -fno-lld`), whose bit-pointers have the ABI host size 4. Both are schema 12 (explicit
Linux/baseline ReleaseSafe profile); `PackedFieldsFresh/Gen.lean` and `PackedFieldsX86/Gen.lean`
are their translations and `PackedFieldsFresh/Proofs.lean` proves, from `mem0` with
`decide +kernel`, the same results as above for every function (plus `bytePtr` and the three
pointer-parameter functions).

```sh
lake build air2lean ZigLean
bash tests/roadmap/packed-fields/compiler.sh --check                       # retained export, no compiler
AIR2LEAN_ZIG_NATIVE=/stock/zig bash tests/roadmap/packed-fields/compiler.sh --native
AIR2LEAN_ZIG_AIR=/patched/zig bash tests/roadmap/packed-fields/compiler.sh --export "$fresh"
python3 tests/roadmap/packed-fields/compiler-check.py --fresh "$fresh"
```

What the real compiler does differently from the hand-written AIR (the model is unchanged):

* It folds every field pointer of a global into a constant pointer (`global` 0, offset 0) with
  the final bit-pointer type, instead of `struct_field_ptr_index_N` instructions; through a
  runtime `*Reg` it emits the instructions, with the same types.
* `&reg.inner.c` is the bit-pointer `*align(4:8:3) u8` (host 3, bit 8), not the byte pointer
  `*u8` of the hand-written `innerC`. The byte-pointer path (and the nested-base fix of PR125)
  is therefore exercised by hand-written AIR only; the bit-pointer form reads and writes the
  same byte 1.
* `reg.inner = .{ ... }` is two stores (`b`, then `c`), not one store of a 12-bit `Inner`.
* `hostAbi` on the LLVM backend has host size 3 (the ABI host size 4 appears only in the
  `-fno-llvm` export).

`packed_fields.zig` has native tests for every defined-behaviour function (stock 0.16.0 on an
aarch64-macos host, ReleaseSafe and Debug: all pass). Not run natively: `innerPartial` and
`undefField` (they read bits that are still undefined) and `unionBadMode` (an enum tag without a
name is a safety panic). Native execution on x86_64 Linux is not done.

Scope: the hand-written AIR remains the only input for the byte-pointer form and the
`struct_field_ptr` forms above. Packed unions as fields of packed structs, float and pointer
fields, partly `undefined` packed constants and big-endian targets remain outside the subset.
