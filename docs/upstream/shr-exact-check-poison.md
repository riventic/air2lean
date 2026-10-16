# Draft upstream note: the `@shrExact` safety check branches on poison, and optimized builds delete it

Status: draft, **not filed**. Found by the soundness audit 2026-10-14, S3b
([soundness-2026-10-14.md](../architecture-audit/soundness-2026-10-14.md), §S3). Zig 0.14.1, 0.15.2,
0.16.0 and 0.17.0, LLVM backend.

## Summary

With runtime safety on, `@shrExact(a, b)` is meant to panic with "right shift overflowed bits"
when a set bit is shifted out. Sema emits the shift first and checks its result afterwards
(`zirShr`, `src/Sema.zig`):

```zig
const result = try block.addBinOp(air_tag, lhs, rhs);        // .shr_exact
...
if (air_tag == .shr_exact) {
    const back = try block.addBinOp(.shl, result, rhs);
    const ok = ... try block.addBinOp(.cmp_eq, lhs, back);
    try sema.addSafetyCheck(block, src, ok, .shr_overflow);
}
```

The LLVM backend lowers `shr_exact` to `lshr exact` / `ashr exact` (`airShr`,
`src/codegen/llvm/FuncGen.zig`). An exact shift that shifts out a set bit is `poison`, so the
check computes `shl poison, b`, compares it, and branches on `poison`: undefined behaviour in
exactly the case the check exists for. Debug IR (0.16.0, `-OReleaseSafe` drops all but the first
and the last line):

```llvm
%6 = lshr exact i32 %1, %5
%8 = shl i32 %6, %7
%9 = icmp eq i32 %1, %8
br i1 %9, label %Then, label %Else        ; Else calls FullPanic.shrOverflow
...
ret i32 %6
```

InstCombine folds `shl (lshr exact x, b), b` to `x`, the comparison to `true`, and removes the
panic. In ReleaseSafe the function is `lshr exact` and `ret`, and the program goes on with a
poison-derived value. A Debug build happens to keep the check and panics.

The same holds for signed operands (`ashr exact`), vectors, and integer widths that are not a
power of two (there the separate `shiftRhsTooBig` count check survives; it does not read the
result). No other integer safety check is affected: `@shlExact` with safety is
`shl_with_overflow`, and the division, cast and overflow checks come before their op.

## Reproducer

[`shr-unsafe/native.zig`](../../tests/roadmap/architecture-audit/soundness-1014/translator/shr-unsafe/native.zig)
with [`shr.zig`](../../tests/roadmap/architecture-audit/soundness-1014/translator/shr-unsafe/shr.zig):

```zig
pub fn shrSafe(a: u32, b: u5) u32 {
    return @shrExact(a, b);
}
```

```sh
zig build-exe -OReleaseSafe --dep shr -Mroot=native.zig -Mshr=shr.zig && ./root
```

Stock 0.16.0 and 0.17.0 on aarch64-macos print `shrSafe(3, 1) = 3` and `= 1` respectively
(no panic); `-ODebug` panics. 0.14.1 and 0.15.2 (aarch64-linux-musl) behave the same, and the
ReleaseSafe IR for x86_64-linux is `lshr exact` and `ret` in all four versions.
[`family.zig`](../../tests/roadmap/architecture-audit/soundness-1014/translator/shr-unsafe/family.zig)
runs every other integer safety check with a violating input: each one panics.

## Possible fixes

* Sema: with safety, emit a plain `shr` and check that, as `@shlExact` uses
  `shl_with_overflow`. The checked result is then a defined value, and the check survives.
* Or check before the shift: `a & ((1 << b) - 1) == 0` (the low `b` bits are zero), then emit
  `shr_exact`.
* Or the backend could drop the `exact` flag in a function with safety on. AIR does not record
  that, so this would need a new tag (a `shr_exact_safe`).

## Effect on air2lean

`Zig.shrExact` throws `.illegal` on an inexact shift, with and without the check
([illegal-behavior.md](../illegal-behavior.md) row 13). That is the LLVM semantics; for a build
that keeps the check, it over-approximates the panic.
