//! Inline asm, register operands only (M21, x86_64 only): a byte swap, a population count and a
//! leading-zero count, each one instruction with one output and one input, both general-purpose
//! registers. `docs/generated-code.md` §Inline asm: the translation is one `opaque` per distinct
//! (source, constraints, operand widths) — a proof can use only a fact the caller states about
//! it. `bswap32`/`popcnt64` are non-volatile (pure functions of their input); `lzcnt64` is
//! `volatile` with a `cc` clobber (a real instruction property, unrelated to the M21 subset:
//! `cc` is not `memory`, so `Check.lean` still accepts it) to exercise that path too.
//!
//! x86_64 only: `.{ .cc = true }` is a clobber literal of x86(_64)'s own `Clobbers` struct
//! (`std.builtin.assembly.Clobbers`), which other targets do not have a matching field for, so
//! this file fails to compile there. Exclude it with `AIR2LEAN_EXAMPLES` on such a host
//! (`docs/floats.md`'s `AIR2LEAN_EXAMPLES` precedent for a target-specific example); CI's
//! `ubuntu-24.04` runners are natively x86_64, so the full matrix legs need no exclusion.

const std = @import("std");

pub fn bswap32(x: u32) u32 {
    return asm ("bswap %[x]"
        : [ret] "=r" (-> u32),
        : [x] "r" (x),
    );
}

pub fn popcnt64(x: u64) u64 {
    return asm ("popcnt %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
    );
}

pub fn lzcnt64(x: u64) u64 {
    return asm volatile ("lzcnt %[x], %[ret]"
        : [ret] "=r" (-> u64),
        : [x] "r" (x),
        : .{ .cc = true }
    );
}

comptime {
    _ = &bswap32;
    _ = &popcnt64;
    _ = &lzcnt64;
}

test "bswap32" {
    try std.testing.expectEqual(@as(u32, 0x78563412), bswap32(0x12345678));
}

test "popcnt64" {
    try std.testing.expectEqual(@as(u64, 4), popcnt64(0b1011));
}

test "lzcnt64" {
    try std.testing.expectEqual(@as(u64, 32), lzcnt64(@as(u64, 1) << 31));
}
