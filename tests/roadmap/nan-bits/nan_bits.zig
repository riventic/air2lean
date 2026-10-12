//! A float's bits observed as an integer through memory (docs/architecture-audit/nan-bits.md).
//! A NaN that an operation makes has target-specific sign and payload bits, so the model gives
//! `.unspecified` wherever such bits become an integer; a NaN constant keeps its exact bits.
//! Every function compiles on Zig 0.14.1, 0.15.2, 0.16.0 and 0.17.0 (`README.md`).
var g32: f32 = 0;
var g64: f64 = 0;
/// A NaN constant in a global initializer: its bits are the constant's.
var gnan: f32 = @bitCast(@as(u32, 0x7fa0_0001));

pub const FU = extern union { f: f32, i: u32 };
pub const FS = extern struct { f: f32, k: u32 };

/// The quotient stored to a global and read back through a `*const u32`.
pub fn storeLoad(a: f32, b: f32) u32 {
    g32 = a / b;
    return @as(*const u32, @ptrCast(&g32)).*;
}

/// The same with `f64`.
pub fn storeLoad64(a: f64, b: f64) u64 {
    g64 = a / b;
    return @as(*const u64, @ptrCast(&g64)).*;
}

/// A sum: x86_64 and aarch64 both propagate a NaN operand's payload.
pub fn sumBits(a: f32, b: f32) u32 {
    g32 = a + b;
    return @as(*const u32, @ptrCast(&g32)).*;
}

/// Through an `extern union`.
pub fn unionView(a: f32, b: f32) u32 {
    const u: FU = .{ .f = a / b };
    return u.i;
}

/// `@bitCast` of an array of floats (a memory reinterpretation up to 0.16).
pub fn arrayCast(a: f32, b: f32) u64 {
    return @bitCast([2]f32{ a / b, 1.0 });
}

/// `@bitCast` of a vector of floats.
pub fn vectorCast(a: f32, b: f32) u64 {
    return @bitCast(@Vector(2, f32){ a / b, 1.0 });
}

/// An `extern struct` with a float field, read as one integer.
pub fn structView(a: f32, b: f32) u64 {
    const s: FS = .{ .f = a / b, .k = 7 };
    return @as(*align(4) const u64, @ptrCast(&s)).*;
}

/// The quotient's bytes copied into an integer.
pub fn copyBytes(a: f32, b: f32) u32 {
    const f: f32 = a / b;
    var i: u32 = 0;
    @memcpy(@as(*[4]u8, @ptrCast(&i)), @as(*const [4]u8, @ptrCast(&f)));
    return i;
}

/// A finite quotient keeps its exact bits.
pub fn finiteBits(a: f32, b: f32) u32 {
    g32 = a / b;
    return @as(*const u32, @ptrCast(&g32)).*;
}

/// A NaN constant stored at run time keeps its bits.
pub fn constStore() u32 {
    g32 = @bitCast(@as(u32, 0x7fa0_0002));
    return @as(*const u32, @ptrCast(&g32)).*;
}

/// A NaN constant in a global initializer keeps its bits.
pub fn constGlobal() u32 {
    return @as(*const u32, @ptrCast(&gnan)).*;
}

/// A NaN read back as a float stays a NaN natively (the model: `.unspecified`, README.md).
pub fn reloadIsNaN(a: f32, b: f32) bool {
    g32 = a / b;
    return g32 != g32;
}

comptime {
    _ = &storeLoad;
    _ = &storeLoad64;
    _ = &sumBits;
    _ = &unionView;
    _ = &arrayCast;
    _ = &vectorCast;
    _ = &structView;
    _ = &copyBytes;
    _ = &finiteBits;
    _ = &constStore;
    _ = &constGlobal;
    _ = &reloadIsNaN;
}
