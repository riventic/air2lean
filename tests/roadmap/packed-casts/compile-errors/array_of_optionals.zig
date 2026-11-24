pub fn cast(a: [2]?u8) u32 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
