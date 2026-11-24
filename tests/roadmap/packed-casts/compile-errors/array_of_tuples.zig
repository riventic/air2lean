const P = struct { u8, u16 };
pub fn cast(a: [2]P) u64 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
