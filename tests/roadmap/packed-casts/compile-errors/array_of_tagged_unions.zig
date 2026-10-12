const T = union(enum) { a: u16, b: u8 };
pub fn cast(a: [2]T) u64 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
