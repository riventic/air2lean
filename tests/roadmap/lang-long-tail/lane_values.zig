//! L09, Zig 0.17.1: `&v[i]` is a lane pointer (`*align(a:0:n:i) T`, the vector's address with
//! the lane in the type) for every lane type. A lane of a whole power-of-two number of bytes
//! (`u32`) is modelled as the element pointer that Zig up to 0.16.0 made (`Canon.laneElemPtrs`),
//! which is right only where `&v[i]` is used as it is made. As a value of the lane pointer type
//! (a parameter, a result) it is the vector's address, which the element pointer is not: the
//! translator rejects the type. A bit-packed lane (`lanes.zig`, `float_lanes.zig`) has one model,
//! the bit-pointer, and is accepted in every position.
const V = @Vector(4, u32);
const Lane = @TypeOf(&@as(*V, undefined)[1]);

noinline fn put(p: Lane, x: u32) void {
    p.* = x;
}

/// A lane pointer parameter.
pub fn viaParam(v: *V, x: u32) void {
    put(&v[1], x);
}

/// A lane pointer result.
pub fn viaResult(v: *V) Lane {
    return &v[1];
}

comptime {
    _ = &viaParam;
    _ = &viaResult;
}
