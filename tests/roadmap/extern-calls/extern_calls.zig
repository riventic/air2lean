//! Calls to extern C functions (`docs/air-json.md` §Extern calls). The definitions are the
//! `export fn`s of `libc_ref.zig`, which the same compilation analyses.

comptime {
    _ = @import("libc_ref.zig");
}

extern fn memset(dest: [*]u8, c: c_int, n: usize) [*]u8;
extern fn strlen(s: [*:0]const u8) usize;

/// Fill the first `n` (at most 16) of 16 ones with the byte `c`; the sum of all 16 bytes.
pub export fn fillSum(n: usize, c: c_int) u32 {
    var buf = [_]u8{1} ** 16;
    const m = if (n > 16) 16 else n;
    _ = memset(&buf, c, m);
    var sum: u32 = 0;
    for (buf) |b| sum += b;
    return sum;
}

/// The length of one of two string literals.
pub export fn greetLen(which: u32) usize {
    const a: [*:0]const u8 = "hello";
    const b: [*:0]const u8 = "extern calls";
    return strlen(if (which == 0) a else b);
}
