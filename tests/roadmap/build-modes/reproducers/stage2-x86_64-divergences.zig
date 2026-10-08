//! Reproducers for the three places where the self-hosted x86_64 backend (-fno-llvm, Zig 0.16.0)
//! differs from the LLVM backend (and from the model) on legal inputs. Run on x86_64-linux:
//!   zig run -OReleaseSafe -fllvm    stage2-x86_64-divergences.zig
//!   zig run -OReleaseSafe -fno-llvm stage2-x86_64-divergences.zig
//! LLVM prints  mod=0x0000 min=0x80000000000000000000 nib=-8
//! stage2 prints mod=0x3c00 min=0x00000000000000000000 nib=8
const std = @import("std");

// 1. f16 @mod(-2^-24, 1.0): LLVM computes frem(frem(a, b) + b, b) = 0; stage2 gives 1.0.
noinline fn modF16(a: f16, b: f16) f16 {
    return @mod(a, b);
}

// 2. f80 @min(-0.0, +0.0): signed-zero order of min is unspecified; LLVM gives -0.0, stage2 +0.0.
noinline fn minF80(a: f80, b: f80) f80 {
    return @min(a, b);
}

// 3. An i4 read from a packed union is not sign-extended by stage2 when it is returned.
const Nib = packed union {
    lo: u4,
    signed: i4,
};
noinline fn setNib(p: *Nib, v: u4) i4 {
    p.lo = v;
    return p.signed;
}

pub fn main() void {
    const tiny: f16 = @bitCast(@as(u16, 0x8001));
    const one: f16 = 1.0;
    const m: u16 = @bitCast(modF16(tiny, one));
    const neg_zero: f80 = -0.0;
    const pos_zero: f80 = 0.0;
    const z: u80 = @bitCast(minF80(neg_zero, pos_zero));
    var n: Nib = .{ .lo = 0 };
    const nib = setNib(&n, 8);
    std.debug.print("mod=0x{x:0>4} min=0x{x:0>20} nib={d}\n", .{ m, z, nib });
}
