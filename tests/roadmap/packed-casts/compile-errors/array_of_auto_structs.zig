const S = struct { a: u16, b: u16 };
pub fn cast(a: [2]S) u64 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
