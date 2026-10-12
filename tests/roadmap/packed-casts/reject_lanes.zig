//! Rejected (`checkPackedVectorLanes`): stores through lane pointers into a vector field of a
//! packed struct, which Zig 0.14.1 and 0.15.2 miscompile (docs/upstream/packed-vector-lane-ptr.md).
pub const VF = packed struct(u16) { t: u4, v: @Vector(3, u4) };

pub fn setOne(p: *VF) u16 {
    p.v[1] = 7;
    return @bitCast(p.*);
}

comptime {
    _ = &setOne;
}
