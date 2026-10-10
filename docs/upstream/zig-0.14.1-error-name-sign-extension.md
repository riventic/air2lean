# Draft upstream note: `@errorName` reads out of bounds for codes with the top bit set (Zig 0.14.1)

Status: draft, not filed. The bug is already fixed in Zig 0.15.2. This note records it as the
reason air2lean rejects `@errorName` on 0.14.1.

## Summary

With the LLVM backend, Zig 0.14.1 lowers `@errorName(e)` to a `getelementptr inbounds` into
`__zig_err_name_table`, and it passes the error integer `u<bits>` (LLVM `i<bits>`) as the index
without widening it. LLVM treats GEP indices as signed. A code whose top bit is set, meaning a
code of at least `2^(bits-1)`, therefore becomes a negative index. The load reads the slice
before the table instead of the error's name. The result is an empty or garbage slice, or a
segmentation fault, all in a `ReleaseSafe` build without a safety panic.

`src/codegen/llvm.zig`, `airErrorName` (0.14.1):

```zig
const error_name_ptr =
    try self.wip.gep(.inbounds, slice_llvm_ty, error_name_table, &.{operand}, "");
```

0.15.2 zero-extends the operand to `usize` first ("If operand is small (e.g. `u8`), then
signedness becomes a problem -- GEP always treats the index as signed."). 0.16.0 does the same.

`@errorFromInt` itself is correct in 0.14.1. `__zig_lt_errors_len` compares with an unsigned
`icmp ule`, so it accepts exactly the codes 1..N.

## Reproduction

The bug needs a compilation with at least `2^(bits-1)` errors. With the default
`--error-limit` (16 bits) that means 32768 errors. A narrow limit makes it small:
`--error-limit 255` gives an 8-bit error integer, and 128 errors are enough.

```zig
// zig build-exe -lc -OReleaseSafe -fno-error-tracing --error-limit 255 repro.zig
// errs.zig declares `pub const Big = error{ E1, ..., E242 };` and
// `pub const last: anyerror = Big.E242;`, so the compilation has 255 errors (0.14.1's start
// code names 12 itself). No `std` beyond `no_panic`: `std` names hundreds of errors.
const std = @import("std");
const errs = @import("errs.zig");
pub const panic = std.debug.no_panic;
extern "c" fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
pub export fn main() c_int {
    if (@intFromError(errs.last) == 0) return 1; // keep every error in the compilation
    var code: u8 = 200; // any code >= 128 of an existing error
    const e = @errorFromInt(@as(*volatile u8, &code).*); // accepted: the error exists
    const name = @errorName(e); // out-of-bounds read: "" here, garbage at 254 and 255
    const verdict: []const u8 = if (name.len == 0) "empty name\n" else "named\n";
    _ = write(1, verdict.ptr, verdict.len); // 0.14.1: "empty name"; 0.15.2: "named"
    return 0;
}
```

Observed on aarch64-macos with the stock 0.14.1 (sha256
`b3de43be2f2a65738c11d6bba5520e3e2f75a3aadbedd4ac3640a6a107fcd593`). The probe is
`tests/roadmap/error-width/probe.zig`, and each configuration's compilation has as many errors
as its limit allows:

| `--error-limit` | bits | code | `@errorFromInt` | `@errorName` |
| --- | --- | --- | --- | --- |
| 255 | 8 | 127 | ok | `E117` (correct) |
| 255 | 8 | 128, 200, 253 | ok | `""` |
| 255 | 8 | 254, 255 | ok | a garbage slice (length 4303785312, 6643796016) |
| 65534 | 16 | 32767 | ok | correct |
| 65534 | 16 | 32768 | ok | SIGSEGV |
| 65534 | 16 | 40000, 65534 | ok | garbage slices |
| 65536 | 17 | 65536 | ok | SIGSEGV |

The 0.15.2 and 0.16.0 builds of the same probe name every code 1..N.

## Effect on air2lean

The ZigLean model names an error by its symbolic name (`errorNameOf`) and has no out-of-bounds
case. AIR does not export the compilation's error count, so the translator cannot show that every
code stays below `2^(bits-1)`. `Air2Lean/Check.lean` therefore rejects `@errorName` in a 0.14.1
export. `tests/roadmap/error-width/negatives.py` checks the rejection and checks that 0.15.2 and
0.16.0 still accept the same function. On 0.14.1, `tests/roadmap/error-width/native.py` does not
read names of top-bit codes (`names from 2^(bits-1) unread`), and `Model.lean` requires that
line.

An earlier recording printed `@errorName` inside its `@errorFromInt` probe. Its out-of-bounds
reads looked like rejected codes, for example `bound count 253` at limit 255 and `32767` at the
default limit. With the probe printing `@intFromError` instead, `@errorFromInt` matches the model
at every limit.
