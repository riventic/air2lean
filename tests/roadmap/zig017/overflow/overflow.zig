// Zig 0.17.0 @mulWithOverflow, exported as AIR by the patched compiler (support:tags:mul_with_overflow).
export fn mulOverflowU32(a: u32, b: u32) u32 {
    const r = @mulWithOverflow(a, b);
    return r[0] ^ r[1];
}
export fn mulOverflowI16(a: i16, b: i16) i16 {
    const r = @mulWithOverflow(a, b);
    return r[0] ^ @as(i16, r[1]);
}
