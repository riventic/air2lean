//! L08: a vector as a packed-struct field (Zig 0.14.1 and 0.15.2 only; 0.16.0 made it a compile
//! error, "packed structs cannot contain fields of type '@Vector(3, u4)'"). Lane 0 is in the
//! lowest bits of the field. Whole-vector reads and writes only: a lane pointer into the field
//! is miscompiled by both versions (`reject_lanes.zig`, docs/upstream/packed-vector-lane-ptr.md).
pub const VF = packed struct(u16) { t: u4, v: @Vector(3, u4) };

var vf: VF = undefined;

/// The vector field written as a whole after the field below it.
pub fn setVector(a: u4, b: u4, c: u4) u16 {
    vf.t = 0xA;
    const v: @Vector(3, u4) = .{ a, b, c };
    vf.v = v;
    return @bitCast(vf);
}

/// Lane 1 of the field of a struct made from its bits.
pub fn lane1(x: u16) u4 {
    const s: VF = @bitCast(x);
    return s.v[1];
}

/// The sum of the lanes, read from memory as one vector.
pub fn laneSum(x: u16) u4 {
    vf = @bitCast(x);
    const v = vf.v;
    return v[0] +% v[1] +% v[2];
}

comptime {
    _ = &setVector;
    _ = &lane1;
    _ = &laneSum;
}
