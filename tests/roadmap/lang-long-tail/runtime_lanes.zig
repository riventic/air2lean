//! L09: lane stores at a runtime index into bit-packed vectors (`v[i] = x` through a vector
//! pointer). Zig 0.14.1 and 0.15.2 lower them to `vector_store_elem`; 0.16.0 and later reject a
//! runtime vector index at compile time, so this source exists for 0.14.1 and 0.15.2 only.
pub fn setU9(v: *@Vector(4, u9), i: usize, x: u9) void {
    v[i] = x;
}

pub fn setU24(v: *@Vector(3, u24), i: usize, x: u24) void {
    v[i] = x;
}

pub fn setBool(v: *@Vector(5, bool), i: usize, x: bool) void {
    v[i] = x;
}

pub fn setF80(v: *@Vector(2, f80), i: usize, x: f80) void {
    v[i] = x;
}

/// A local vector written lane by lane at runtime indices, then read back.
pub fn fillSum(n: usize) u9 {
    var v: @Vector(4, u9) = @splat(1);
    var i: usize = 0;
    while (i < n and i < 4) : (i += 1) v[i] = @intCast(i * 100 + 7);
    return v[0] +% v[1] +% v[2] +% v[3];
}

comptime {
    _ = &setU9;
    _ = &setU24;
    _ = &setBool;
    _ = &setF80;
    _ = &fillSum;
}
