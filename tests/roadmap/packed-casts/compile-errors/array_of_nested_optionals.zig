pub fn cast(a: [2][2]?u16) u128 {
    return @bitCast(a);
}
comptime {
    _ = &cast;
}
