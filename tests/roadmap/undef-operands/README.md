# `undefined` constant operands

No `undefined` part of a constant operand is replaced by a default (`0`, `false`). Before this
check, a partly `undefined` constant (a struct, array, optional, error-union or union constant
with an `undefined` part) was emitted with those parts as typed defaults, so a later read saw
`0` instead of `.unspecified`. Now:

| Operand | Translation |
|---|---|
| `store` of a wholly `undefined` value to memory | `Zig.storeUndef T align p` (unchanged) |
| `store` of a constant with `undefined` items of arrays or fields of non-`packed` structs/tuples, at any depth | one `Zig.storeBytes p align` of the value's encoding with each `undefined` part's bytes undefined (`Zig.writeBytes … off (Array.replicate len .undef)`) |
| the same store to a local | the local becomes a stack block (`escapingAllocs`), then as above |
| `memset` of a wholly `undefined` item | `Zig.memset … none` (unchanged) |
| an `undefined` part under an optional, error union, union, slice, vector or packed struct; a store to a packed field; a partly `undefined` `memset` item | rejected, `CONSTANT_FAILURE`, `unsupported_semantics` |
| `undefined` (wholly or partly) as any other operand: call argument, return/block result, `aggregate_init` element, arithmetic, `select`, atomic operand, pointer operand; an `undefined` `shuffle` lane | rejected, `CONSTANT_FAILURE`, `unsupported_semantics` |

The fixture is hand-written AIR in the exporter's schema (`air/0.16.0`) for:

```zig
const Pair = struct { a: u32, b: u32 };
const Rec = struct { len: u8, buf: [3]u16 }; // buf at offset 0, len at 6
var rec: Rec = .{ .len = 0, .buf = .{ 0, 0, 0 } };
export fn localA() u32 { var s: Pair = .{ .a = 1, .b = undefined }; return s.a; }
export fn localB() u32 { var s: Pair = .{ .a = 1, .b = undefined }; return s.b; }
export fn storePair(p: *Pair) void { p.* = .{ .a = 1, .b = undefined }; }
export fn recLen() u8 { rec = .{ .len = 2, .buf = .{ 1, undefined, 3 } }; return rec.len; }
export fn recMid() u16 { rec = .{ .len = 2, .buf = .{ 1, undefined, 3 } }; return rec.buf[1]; }
```

`UndefOperands/Gen.lean` is its retained translation. `UndefOperands/Proofs.lean` proves from
`mem0` that `localA` returns 1 and `recLen` returns 2 (the defined parts), and that `localB` and
`recMid` throw `.unspecified` (the `undefined` field and nested array item). `test_cli.py`
checks the retained translation byte for byte and each rejection above through the CLI and
`--diagnostics-json`.

```sh
lake build air2lean ZigLean
bash tests/roadmap/undef-operands/check.sh
```

Scope: partly `undefined` global initializers are a separate check (L12). A wholly `undefined`
store to a local is `tests/roadmap/undef-locals` (byte locals, dead stores).
