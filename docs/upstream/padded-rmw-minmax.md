# Draft upstream bug: `@atomicRmw` `.Max`/`.Min` and `@cmpxchg*` on integers with padding bits

Status: draft, not filed. Target: ziglang/zig (frontend `Sema`/`codegen/llvm.zig` atomic lowering).
The translator's mitigation is the `PADDED_ATOMIC` diagnostic ([diagnostics.md](../diagnostics.md),
[std-models.md](../std-models.md) Thread model).

## Summary

For an integer type whose bit width is not `8 * @sizeOf(T)` (`i24`, `u24`, `i40`, `u31`, ...), Zig
lowers `@atomicRmw(.Max/.Min)` and `@cmpxchgStrong/Weak` to an LLVM atomic on the whole ABI cell
(`i32` for `i24`, `i64` for `i40`). The operand is widened (`sext` for signed, `zext`/`and` for
unsigned), but the cell's padding bits are whatever the memory holds. The padding is not
sign-extended, so:

- `.Max`/`.Min` on a **signed** padded type orders a negative cell as a large positive value, even
  when the padding is zero: `@atomicRmw(i24, p, .Max, 3, ...)` on a cell holding `-5` keeps `-5`.
- `.Max`/`.Min` and `@cmpxchg*` on **any** padded type (signed or unsigned) see nonzero padding as
  part of the value: padding left by a narrower store, by an RMW `.Add` carry into the padding, or by
  any other writer makes `@cmpxchgStrong(u24, p, 5, 7, ...)` fail although the value bits equal `5`.

The language reference says the operation is on the value of type `T`; no padding is observable.

## Reproducer

```zig
const std = @import("std");

pub fn main() void {
    // i24 -5 is fb ff ff; the 4th byte (padding) is zero.
    var slot: [4]u8 align(4) = .{ 0xfb, 0xff, 0xff, 0x00 };
    var p: *i24 = @ptrCast(&slot);
    const hidden: *volatile *i24 = &p;
    const old = @atomicRmw(i24, hidden.*, .Max, 3, .seq_cst);
    std.debug.print("old={d} final={d} (expected old=-5 final=3)\n", .{ old, hidden.*.* });
}
```

Observed `old=-5 final=-5` with `zig build-exe -OReleaseSafe` on 0.14.1 and 0.15.2 (x86_64-linux,
docker linux/amd64), 0.16.0 and 0.17.0 (aarch64-macos).

A second reproducer for the padding-dependent part (unsigned, carry into padding):

```zig
var cell: u24 = std.math.maxInt(u24);
var p: *u24 = &cell;
const h: *volatile *u24 = &p;
_ = @atomicRmw(u24, h.*, .Add, 1, .seq_cst);   // wraps to 0; the carry lands in the padding byte
const r = @cmpxchgStrong(u24, h.*, 0, 1, .seq_cst, .seq_cst);   // returns non-null: fails
```

## LLVM IR (identical on 0.16.0 and 0.17.0, x86_64-linux)

```
; @atomicRmw(i24, p, .Max, v, .seq_cst)
%sext = shl i32 %1, 8
%2 = ashr exact i32 %sext, 8            ; the operand, sign-extended
%3 = atomicrmw max ptr %0, i32 %2 seq_cst   ; the cell, raw bytes incl. padding
; @cmpxchgStrong(u24, p, a, b, ...)
%3 = and i32 %1, 16777215
%4 = and i32 %2, 16777215
%5 = cmpxchg ptr %0, i32 %3, i32 %4 seq_cst seq_cst   ; padding compared as part of the cell
```

Plain stores differ by version (IR checked on x86_64-linux): 0.16.0 emits `store i24` (padding byte
untouched); 0.17.0 emits `store i32` of the widened value (padding written, sign-extended for signed
types). That is why an
ordinary store-then-RMW test passes on 0.17.0 but the reproducers above, a carry, a `@memcpy`, an
`extern`/C writer or a `packed struct` write still fail there.

## Probe results (cell value x operand over 0, 1, 2, top, top-1, all ones, ... , padding 00/ff/aa)

Each cell is a plain store of the value into a 32-byte buffer pre-filled with the padding byte.
Probe widths: 3, 9, 17, 24, 31, 33, 40, 48, 56, 63 (+65, 72, 100, 127 on aarch64), signed and
unsigned, and 8/16/32/64/128 as controls.

| Zig | target | `.Max`/`.Min`, signed padded widths | `.Max`/`.Min`, unsigned padded widths | other RMW ops | power-of-two widths |
|---|---|---|---|---|---|
| 0.14.1 | x86_64-linux (docker) | wrong, all padded widths, also with padding 00 | wrong when padding nonzero (u17 and wider) | correct | correct |
| 0.15.2 | x86_64-linux (docker) | same | same | correct | correct |
| 0.16.0 | x86_64-linux (docker) | same | same | correct | correct |
| 0.16.0 | aarch64-macos | same (up to i127) | same (up to u100) | correct | correct (incl. i128/u128) |
| 0.17.0 | x86_64-linux, aarch64-macos | correct (plain stores widen), wrong in the zero-padding reproducer | correct (plain stores widen), wrong after a carry | correct | correct |

`cmpxchg` on u/i17..i56: succeeds with padding 00, fails with padding ff/aa on 0.16.0 (aarch64-macos);
passes the same probe on 0.17.0 (x86_64-linux and aarch64-macos) for the store-widening reason above,
but fails after a carry (`u17`, `u24`, `u40`, second reproducer, 0.17.0 aarch64-macos).

"Other RMW ops" are `.Xchg .Add .Sub .And .Nand .Or .Xor`: their results are masked on return and
their final value is masked on load, so they agree with a value-only model.

## Suggested fix

Either (a) lower padded-width atomics on the integer type (`atomicrmw` / `cmpxchg` on `iN`; LLVM
legalizes `i24`), or (b) canonicalize before the op: for `.Max`/`.Min`/`cmpxchg` load the cell,
extend from bit N and operate on the extended value (a compare-exchange loop), or (c) document that
atomics on integers with padding bits are not supported and reject them in `Sema`
(`checkAtomicPtrOperand` already rejects widths above the target's maximum).

## Evidence files

The probe sources (`rmwprobe.zig`: every RMW op, padding 00/ff/aa; `cxprobe.zig` for `cmpxchg`) were
run from a scratch directory and are not committed; the two reproducers above are self-contained. The repository's
own cross-platform ABI probe (`tests/roadmap/aarch64-abi/probe.zig`, branch
`codex/b10-assurance-records`, `rmw` rows) records the same `.Max` mismatch for `i24`/`i40`.
