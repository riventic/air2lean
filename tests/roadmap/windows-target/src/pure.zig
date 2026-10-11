//! Pure integer and `f64` code: accepted on x86_64-windows-gnu; `c_long` is 32 bits there.
export fn mix(a: c_long, b: f64) f64 {
    const wide: i64 = a;
    return @as(f64, @floatFromInt(wide)) * b + 0.5;
}

export fn neg80(x: f80) f80 {
    return -x;
}
