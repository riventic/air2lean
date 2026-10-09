//! Extern calls whose declarations name other Zig types than their definitions (abi_ref.zig),
//! as translate-c's musl-header declarations do against Zig's libc: the binding converts at the
//! C ABI boundary (`docs/air-json.md` §Extern calls).

comptime {
    _ = @import("abi_ref.zig");
}

extern fn abi_fill(dest: ?*anyopaque, c: c_int, n: usize) ?*anyopaque;
extern fn abi_len(s: [*c]const u8) usize;

/// Fill the first `n` (at most 16) of 16 ones with the byte `c` through `abi_fill(u8)`; the sum
/// of all 16 bytes. A `c` outside `u8` has no defined behaviour.
pub export fn fillSum(n: usize, c: c_int) u32 {
    var buf = [_]u8{1} ** 16;
    const m = if (n > 16) 16 else n;
    _ = abi_fill(&buf, c, m);
    var sum: u32 = 0;
    for (buf) |b| sum += b;
    return sum;
}

/// The length of one of two strings through `abi_len([*:0]const c_char)`; `null` for `which`
/// 2, which has no defined behaviour.
pub export fn lenOf(which: u32) usize {
    const a: [*c]const u8 = "hello";
    const b: [*c]const u8 = "abi calls";
    return abi_len(switch (which) {
        0 => a,
        1 => b,
        else => null,
    });
}
