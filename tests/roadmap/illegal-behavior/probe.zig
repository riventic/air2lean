//! Inventory probes (docs/illegal-behavior.md): illegal behaviour that the translator rejects,
//! or that stays a gap. `check.sh` translates each function alone and records whether the
//! translator accepts it; `expected.json` pins the result.

const E = enum(u8) { a, b, _ };
const Small = error{A};
const Big = error{ A, B };

pub fn errorFromIntSafe(x: u16) anyerror {
    return @errorFromInt(x);
}

pub fn errorFromIntUnsafe(x: u16) anyerror {
    @setRuntimeSafety(false);
    return @errorFromInt(x);
}

pub fn errorCastSafe(e: Big) Small {
    return @errorCast(e);
}

pub fn errorCastUnsafe(e: Big) Small {
    @setRuntimeSafety(false);
    return @errorCast(e);
}

pub fn errorCastUnionUnsafe(e: Big!u32) Small!u32 {
    @setRuntimeSafety(false);
    return @errorCast(e);
}

pub fn tagNameSafe(e: E) []const u8 {
    return @tagName(e);
}

pub fn tagNameUnsafe(e: E) []const u8 {
    @setRuntimeSafety(false);
    return @tagName(e);
}

pub fn shl24Safe(a: u24, b: u5) u24 {
    return a << b;
}

pub fn vecPtrCast(p: *align(16) const [4]u32) u32 {
    const v: *const @Vector(4, u32) = @ptrCast(p);
    return v.*[0];
}

pub fn sentinelUnsafe(s: []const u8, n: usize) [:0]const u8 {
    @setRuntimeSafety(false);
    return s[0..n :0];
}

pub fn forLenUnsafe(a: []const u32, b: []const u32) u32 {
    @setRuntimeSafety(false);
    var sum: u32 = 0;
    for (a, b) |x, y| sum +%= x +% y;
    return sum;
}

pub fn noreturnCall(x: u32) u32 {
    if (x == 0) die();
    return x;
}

fn die() noreturn {
    @panic("die");
}

comptime {
    _ = &errorFromIntSafe;
    _ = &errorFromIntUnsafe;
    _ = &errorCastSafe;
    _ = &errorCastUnsafe;
    _ = &errorCastUnionUnsafe;
    _ = &tagNameSafe;
    _ = &tagNameUnsafe;
    _ = &shl24Safe;
    _ = &vecPtrCast;
    _ = &sentinelUnsafe;
    _ = &forLenUnsafe;
    _ = &noreturnCall;
}
