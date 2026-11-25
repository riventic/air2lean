//! L09: lane pointers of whole-byte lanes (`u8`, `i16`, `u32`, `u64`, `u128`, `f32`, `f64`) in
//! every position a pointer value takes: a parameter, a function result, a struct field, a
//! `const` lane and a constant (`&g[2]` of a global). Zig 0.17.1 types `&v[i]` of every vector as
//! a lane pointer (`*align(a:0:n:i) T`: the vector's address, the lane in the type), as it types
//! `&v[i]` of a bit-packed lane (`lane_shapes.zig`) in every version: one model, the bit-pointer
//! into the vector's integer. Up to 0.16.0 `&v[i]` of such a lane is a plain element pointer
//! (`*T` at the lane's address). `offset` tells the two apart: `@intFromPtr(&v[1])` is the
//! vector's address in 0.17.1 and the lane's up to 0.16.0. `probe_lane_values.zig` prints the
//! native results, `ModelLaneValues.lean` the model's.
fn Lanes(comptime T: type) type {
    return struct {
        const V = @Vector(4, T);
        const Lane1 = @TypeOf(&@as(*V, undefined)[1]);
        const Lane2 = @TypeOf(&@as(*V, undefined)[2]);
        const Holder = struct { p: Lane1 };

        var g: V = .{ of(1), of(2), of(3), of(4) };

        /// A lane value from `x`: spread bits for an integer lane, a small exact float.
        fn of(x: u32) T {
            const w = @as(u128, x) *% 0x9e3779b97f4a7c15_f39cc0605cedc835;
            return switch (T) {
                u8, u32, u64 => @truncate(w),
                u128 => w,
                i16 => @bitCast(@as(u16, @truncate(w))),
                f32, f64 => @floatFromInt(x & 0xff),
                else => @compileError("lane type"),
            };
        }

        /// The lane's bits (an integer lane) or value (a float lane, a small integer).
        fn bits(x: T) u128 {
            return switch (T) {
                i16 => @as(u16, @bitCast(x)),
                f32, f64 => @intFromFloat(x),
                else => x,
            };
        }

        fn lanes(a: u32) V {
            return .{ of(a), of(a >> 3), of(a >> 7), of(a >> 13) };
        }

        fn pack(v: V) u128 {
            return bits(v[0]) +% bits(v[1]) *% 0x100 +% bits(v[2]) *% 0x10000 +%
                bits(v[3]) *% 0x1000000;
        }

        noinline fn put(p: Lane1, x: T) void {
            p.* = x;
        }

        noinline fn pick(v: *V) Lane2 {
            return &v[2];
        }

        noinline fn writeHeld(h: *const Holder, x: T) void {
            h.p.* = x;
        }

        noinline fn readConst(v: *const V) T {
            const p = &v[3];
            return p.*;
        }

        /// A lane pointer as a parameter, a result, a struct field and a `const` lane.
        fn values(a: u32, x: u32) u128 {
            var v = lanes(a);
            put(&v[1], of(x));
            const p = pick(&v);
            const old = bits(p.*);
            p.* = of(x >> 4);
            const h: Holder = .{ .p = &v[1] };
            writeHeld(&h, of(x >> 8));
            return pack(v) ^ old << 64 ^ bits(readConst(&v)) << 96;
        }

        /// A constant lane pointer: lane 2 of the global.
        fn global(x: u32) u128 {
            const p = &g[2];
            const old = bits(p.*);
            p.* = of(x);
            return pack(g) ^ old << 64;
        }

        /// The lane pointer's address relative to the vector's.
        fn offset(a: u32) usize {
            var v = lanes(a);
            const p = &v[1];
            p.* = of(a +% 1);
            return @intFromPtr(p) - @intFromPtr(&v);
        }
    };
}

pub fn valuesU8(a: u32, x: u32) u128 {
    return Lanes(u8).values(a, x);
}
pub fn valuesI16(a: u32, x: u32) u128 {
    return Lanes(i16).values(a, x);
}
pub fn valuesU32(a: u32, x: u32) u128 {
    return Lanes(u32).values(a, x);
}
pub fn valuesU64(a: u32, x: u32) u128 {
    return Lanes(u64).values(a, x);
}
pub fn valuesU128(a: u32, x: u32) u128 {
    return Lanes(u128).values(a, x);
}
pub fn valuesF32(a: u32, x: u32) u128 {
    return Lanes(f32).values(a, x);
}
pub fn valuesF64(a: u32, x: u32) u128 {
    return Lanes(f64).values(a, x);
}

pub fn globalU8(x: u32) u128 {
    return Lanes(u8).global(x);
}
pub fn globalU32(x: u32) u128 {
    return Lanes(u32).global(x);
}
pub fn globalU128(x: u32) u128 {
    return Lanes(u128).global(x);
}
pub fn globalF64(x: u32) u128 {
    return Lanes(f64).global(x);
}

pub fn offsetU8(a: u32) usize {
    return Lanes(u8).offset(a);
}
pub fn offsetU32(a: u32) usize {
    return Lanes(u32).offset(a);
}
pub fn offsetF64(a: u32) usize {
    return Lanes(f64).offset(a);
}

comptime {
    for (.{
        &valuesU8,  &valuesI16, &valuesU32,  &valuesU64, &valuesU128, &valuesF32, &valuesF64,
        &globalU8,  &globalU32, &globalU128, &globalF64, &offsetU8,   &offsetU32, &offsetF64,
    }) |f| _ = f;
}
