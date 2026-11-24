pub fn cast(v: void) u0 {
    return @bitCast(v);
}
comptime {
    _ = &cast;
}
