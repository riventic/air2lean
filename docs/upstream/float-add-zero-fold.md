# Zig 0.14.1: `x + 0.0` is folded to `x` in strict float mode, so `-0.0 + 0.0` gives `-0.0`

> **DRAFT. Not filed upstream.** Filing requires the maintainer's decision. Found while
> checking the `add` rewrites for F03 ([docs/research/F03.md](../research/F03.md)).

## Summary

In Zig 0.14.1 `Sema.analyzeArithmetic` returns the other operand when one operand of a float
`+` is a comptime-known zero (`if (try rhs_val.compareAllWithZeroSema(.eq, pt)) return casted_lhs;`,
and the same for the left operand). That rewrite is right for integers. For floats in the default
strict mode it is wrong for `x = -0.0`: IEEE-754 round-to-nearest gives `-0.0 + +0.0 = +0.0`,
and Zig's language reference does not enable value-changing float rewrites outside
`@setFloatMode(.optimized)`. The fold also removes the `add` from the AIR, so no backend and no
optimization mode can give the IEEE result.

Zig 0.15.2, 0.16.0 and 0.17.0 do not fold: their `analyzeArithmetic` only folds when both
operands are comptime-known ("`0 * x` isn't always `0`"), the runtime add is emitted, and the
probe below prints `0`.

## Reproducer

```zig
const std = @import("std");

var neg_zero: f64 = -0.0;

fn addZeroRhs(x: f64) f64 {
    return x + 0.0;
}

fn addZeroLhs(x: f64) f64 {
    return 0.0 + x;
}

pub fn main() void {
    const r = addZeroRhs(neg_zero);
    const l = addZeroLhs(neg_zero);
    std.debug.print("x + 0.0: {x}  0.0 + x: {x}  (IEEE: both 0x0)\n", .{ @as(u64, @bitCast(r)), @as(u64, @bitCast(l)) });
}
```

`zig run -ODebug add_zero.zig`, stock tarballs, x86_64-linux in `docker run --platform linux/amd64`
(aarch64-macos gives the same for 0.16.0 and 0.17.0; the stock 0.14.1 and 0.15.2 cannot link on
the current macOS SDK):

| Zig | Output |
|---|---|
| 0.14.1 | `x + 0.0: 8000000000000000  0.0 + x: 8000000000000000` (wrong) |
| 0.15.2 | `x + 0.0: 0  0.0 + x: 0` |
| 0.16.0 | `x + 0.0: 0  0.0 + x: 0` |
| 0.17.0 | `x + 0.0: 0  0.0 + x: 0` |

The same difference shows in every optimization mode: `tests/roadmap/fast-math/records/0.14.1--x86_64-linux--*.json`,
case `add_zero.strict` (`8000000000000000` for 0.14.1, `0000000000000000` for the later versions).

## Impact on air2lean

None for soundness: air2lean translates the analyzed AIR, which for 0.14.1 contains no `add`
there, so the generated code is the operand itself and agrees with the compiler. The IEEE float
model (MTH-01) is not the semantics of the 0.14.1 *source* in this one case. Proofs about 0.14.1
code that depends on the sign of a zero sum are about the folded program.
