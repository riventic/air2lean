//! Static archive for the Lean side: one exported function per opaque in Proofs/Asm/Gen.lean,
//! implementing the SAME behavior as examples/asm/asm.zig's inline asm, but with ordinary Zig
//! builtins -- the diff test only needs behavioral equivalence, not instruction equivalence, and
//! this archive (unlike the example) must build on every host, not just x86_64.
//!
//! ABI: one `air2lean_asm_<fn>(x: uN) uN` per op, plain integer in/out (everything here fits one
//! register, unlike libm.zig's f80/f128 hi/lo split).
//!
//! Build (scripts/diff.sh, mirroring the libm section):
//!   zig build-lib -static -fPIC -OReleaseFast -mcpu=baseline --name air2lean_asm \
//!     -femit-bin=tests/diff/out/asm/air2lean_asm.a -Mroot=tests/diff/asm/asm.zig

export fn air2lean_asm_bswap32(x: u32) u32 {
    return @byteSwap(x);
}

export fn air2lean_asm_popcnt64(x: u64) u64 {
    return @popCount(x);
}

export fn air2lean_asm_lzcnt64(x: u64) u64 {
    return @clz(x);
}

/// `divl` with `edx = 0`: the quotient in the low 32 bits, the remainder in the high 32 bits.
/// Never called with `b = 0`: there the generated wrapper traps first (`Zig.asmTrap`, S7), and
/// tests/diff/Diff.lean's `runDivmod` reports that trap without calling this.
export fn air2lean_asm_divmod32(a: u32, b: u32) u64 {
    return (@as(u64, a % b) << 32) | (a / b);
}
