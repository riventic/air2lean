//! L09: a lane pointer into a bit-packed vector in every position a pointer value takes: a
//! constant (`&g[2]` of a global), a function result, a struct field, a lane of a vector that is
//! a struct field, and a `const` lane; with a whole-byte lane pointer used where it is made as the
//! control. Zig 0.17.1 writes `&v[i]` as a `ptr_cast` to the lane pointer type, older versions as
//! `ptr_elem_ptr`; both are the bit-pointer into the vector's integer, so the versions translate
//! alike. `probe_lane_shapes.zig` prints the native results, `ModelLaneShapes.lean` the model's.
const V9 = @Vector(4, u9);
const V32 = @Vector(4, u32);
const Lane1 = @TypeOf(&@as(*V9, undefined)[1]);
const Holder = struct { p: Lane1 };
const Framed = struct { a: u8, v: V9 };

var g: V9 = .{ 1, 2, 3, 4 };

fn lanes(a: u32) V9 {
    return .{ @truncate(a), @truncate(a >> 9), @truncate(a >> 18), @truncate(a >> 27) };
}

/// The four lanes, lane `i` at bit `9 * i`.
fn pack(v: V9) u64 {
    return @as(u64, v[0]) | @as(u64, v[1]) << 9 | @as(u64, v[2]) << 18 | @as(u64, v[3]) << 27;
}

/// A constant lane pointer: lane 2 of the global. Returns the new lanes and the old lane.
pub fn globalLane(x: u16) u64 {
    const p = &g[2];
    const old: u64 = p.*;
    p.* = @truncate(x);
    return pack(g) | old << 36;
}

noinline fn pick(v: *V9) Lane1 {
    return &v[1];
}

/// A lane pointer as a function result.
pub fn viaResult(a: u32, x: u16) u64 {
    var v = lanes(a);
    const p = pick(&v);
    const old: u64 = p.*;
    p.* = @truncate(x);
    return pack(v) | old << 36;
}

noinline fn writeHeld(h: *const Holder, x: u9) void {
    h.p.* = x;
}

/// A lane pointer stored in a struct field and loaded back.
pub fn viaField(a: u32, x: u16) u64 {
    var v = lanes(a);
    const h: Holder = .{ .p = &v[1] };
    writeHeld(&h, @truncate(x));
    return pack(v) | @as(u64, h.p.*) << 36;
}

/// Lanes of a vector that is a field of a struct.
pub fn fieldLane(a: u32, x: u16) u64 {
    var s: Framed = .{ .a = 7, .v = lanes(a) };
    s.v[3] = @truncate(x);
    const q = &s.v[0];
    return pack(s.v) | @as(u64, q.*) << 36 | @as(u64, s.a) << 45;
}

noinline fn readConst(v: *const V9) u9 {
    const p = &v[3];
    return p.*;
}

/// A lane read through a `const` lane pointer.
pub fn constLane(a: u32) u16 {
    const v = lanes(a);
    return readConst(&v);
}

/// Whole-byte lanes: `&v[1]` is an element pointer where it is made.
pub fn byteLocal(a: u32, x: u32) u32 {
    var v: V32 = .{ a, a +% 1, a +% 2, a +% 3 };
    const p = &v[1];
    p.* +%= x;
    v[3] = x;
    return v[0] ^ (p.* *% 3) ^ (v[2] *% 5) ^ (v[3] *% 7);
}

comptime {
    _ = &globalLane;
    _ = &viaResult;
    _ = &viaField;
    _ = &fieldLane;
    _ = &constLane;
    _ = &byteLocal;
}
