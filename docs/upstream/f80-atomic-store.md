# Draft upstream bug: `@atomicStore` of an `f80` stores the operand's address (aarch64, 0.17.1)

Status: draft, not filed (a row for the issue #131 table). Target: ziglang/zig (`codegen/llvm.zig`,
atomic store lowering). The translator is not affected: it rejects every float atomic
([aarch64-abi.md](../aarch64-abi.md#atomic-f80), `CheckCtx.atomicChild`).

## Summary

On aarch64, where `f80` is a soft float, Zig 0.17.1 accepts `@atomicStore(f80, p, v, order)` and
lowers it to an LLVM `store atomic ptr <address of v's constant>, ptr p`: the 8-byte address of the
operand is written into the low bytes of the cell, and the high bytes keep their old value. No
error is reported. Zig 0.14.1 to 0.16.0 abort in LLVM's verifier instead (`Broken module found`).
Every other atomic op on an `f80` (`@atomicLoad`, `@atomicRmw` `.Xchg`/`.Add`/`.Sub`/`.Max`/`.Min`)
also fails in LLVM on every version (`Broken module found`, or `Invalid cast` for `.Xchg`), and
`@cmpxchgStrong`/`@cmpxchgWeak` are rejected by Sema. The language reference allows atomics on
floats; an `f80` atomic should either work or be a compile error.

## Reproducer

```zig
const std = @import("std");
var cell: f80 = 1.5;
noinline fn put(p: *f80, v: f80) void {
    @atomicStore(f80, p, v, .seq_cst);
}
pub fn main() void {
    put(&cell, 2.5);
    const got: u80 = @bitCast(cell);
    const want: u80 = @bitCast(@as(f80, 2.5));
    std.debug.print("got {x:0>20} want {x:0>20}\n", .{ got, want });
}
```

`zig build-exe -fllvm -OReleaseSafe -target aarch64-macos-none -mcpu=baseline` with 0.17.1 on Apple
silicon prints `got 3fff0000000100959448 want 4000a000000000000000` (the low eight bytes change from
run to run: they are an address); the same holds for `aarch64-linux-gnu` in a native `linux/arm64`
container, and for `.monotonic` and `.release`. The emitted IR of `put`:

```llvm
store atomic ptr @__anon_2444, ptr @st2.cell seq_cst, align 8
```

## Evidence

The `f80atomic` rows of `tests/roadmap/aarch64-abi/expected/<zig>/<triple>-ReleaseSafe.txt`
(`scripts/aarch64-abi.py`, probe `tests/roadmap/aarch64-abi/atomic_f80.zig`) for 0.14.1, 0.15.2,
0.16.0 and 0.17.1 on aarch64-linux-gnu and aarch64-macos-none.
