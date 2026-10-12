//! L09: comptime lane pointers into vectors of `f80` lanes, which the LLVM backend bit-packs at
//! an 80-bit stride (`Vec.packedEnc`): `&v[k]` is a bit-pointer into the vector's integer, and
//! a lane is its 80 bits (`Zig.Packed (Float fmt)`).
pub fn swap(v: *@Vector(2, f80)) void {
    const a = &v[0];
    const b = &v[1];
    const t = a.*;
    a.* = b.*;
    b.* = t;
}

/// Writes lane 1 through its pointer; lanes 0 and 2 keep their values.
pub fn middle(x: f80) f80 {
    var v: @Vector(3, f80) = .{ 1.5, 2.5, 3.5 };
    const p = &v[1];
    p.* = x;
    return v[0] + p.* + v[2];
}

comptime {
    _ = &swap;
    _ = &middle;
}
