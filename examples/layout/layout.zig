//! M20: casts (`@intFromPtr`, `@ptrFromInt`, `@ptrCast`, `@constCast`, `@volatileCast`,
//! `@alignCast`), `@fieldParentPtr`, `packed` and `extern` structs.

pub const Point = struct {
    x: u32,
    y: u32,
};

/// Two pointers are equal iff their addresses are (`@intFromPtr`).
pub fn addrEq(a: *const u32, b: *const u32) bool {
    return @intFromPtr(a) == @intFromPtr(b);
}

/// A pointer through its own address and back (`@intFromPtr` then `@ptrFromInt`): the identity.
pub fn ptrRoundTrip(p: *u32) *u32 {
    return @ptrFromInt(@intFromPtr(p));
}

/// The pointer at address `a` (`@ptrFromInt`; panics `castToNull` if `a` is 0,
/// `incorrectAlignment` if `a` is not a multiple of 4). A non-panicking `@ptrFromInt` is already
/// exercised through `ptrRoundTrip`: a valid address here would need a real allocation, since the
/// diff-test harness reads back the pointee.
pub fn ptrFromAddr(a: usize) *u32 {
    return @ptrFromInt(a);
}

/// `p` viewed as `const` (`@ptrCast`).
pub fn asConst(p: *u32) *const u32 {
    return @ptrCast(p);
}

/// `p` with `const` removed (`@constCast`).
pub fn dropConst(p: *const u32) *u32 {
    return @constCast(p);
}

/// `p` viewed as `volatile` (`@volatileCast`).
pub fn asVolatile(p: *u32) *volatile u32 {
    return @volatileCast(p);
}

/// `p` re-aligned to 4 (`@alignCast`; panics `incorrectAlignment` if `p`'s address is not a
/// multiple of 4).
pub fn align4(p: *align(1) u32) *align(4) u32 {
    return @alignCast(p);
}

/// The `Point` that has `xp` as its `x` field (`@fieldParentPtr`).
pub fn parentOfX(xp: *u32) *Point {
    return @fieldParentPtr("x", xp);
}

/// The `Point` that has `yp` as its `y` field.
pub fn parentOfY(yp: *u32) *Point {
    return @fieldParentPtr("y", yp);
}

/// A flags register: 8 bits, first field in the lowest bit.
pub const Flags = packed struct(u8) {
    ready: bool,
    err: bool,
    mode: u2,
    count: u4,
};

/// The byte of `f` (`@bitCast` of a packed struct).
pub fn flagsToByte(f: Flags) u8 {
    return @bitCast(f);
}

/// The flags of `b`.
pub fn byteToFlags(b: u8) Flags {
    return @bitCast(b);
}

/// `b` with its `mode` bits set to `m`.
pub fn setMode(b: u8, m: u2) u8 {
    var f: Flags = @bitCast(b);
    f.mode = m;
    return @bitCast(f);
}

/// Add 1 to `p.count`, wrapping (a bit-pointer read and write through memory).
pub fn incCount(p: *Flags) void {
    p.count +%= 1;
}

/// `p.ready and !p.err`.
pub fn isOk(p: *const Flags) bool {
    return p.ready and !p.err;
}

/// A message header in C layout: 8 bytes, `len` at offset 4.
pub const Header = extern struct {
    magic: u32,
    len: u16,
    kind: u8,
    flags: Flags,
};

/// The payload length in the header at the start of `bytes`, or `null` if `bytes` is too short
/// or the magic number is wrong (`@ptrCast` of a byte pointer to an `extern struct`).
pub fn headerLen(bytes: []const u8) ?u16 {
    if (bytes.len < @sizeOf(Header)) return null;
    const h: *align(1) const Header = @ptrCast(bytes.ptr);
    if (h.magic != 0x4C52_4941) return null;
    return h.len;
}

/// The whole header at the start of `bytes` (a load of an `extern struct` through a byte
/// pointer).
pub fn readHeader(bytes: []const u8) Header {
    const h: *align(1) const Header = @ptrCast(bytes.ptr);
    return h.*;
}

/// The bits of the `f32` at `p`, read through a `*const u32` (`@ptrCast`).
pub fn floatBits(p: *const f32) u32 {
    const q: *const u32 = @ptrCast(p);
    return q.*;
}

/// Store `bits` at `p` as a `u32`, then read it back as an `f32`.
pub fn bitsToFloat(p: *f32, bits: u32) f32 {
    const q: *u32 = @ptrCast(p);
    q.* = bits;
    return p.*;
}

comptime {
    _ = &addrEq;
    _ = &ptrRoundTrip;
    _ = &ptrFromAddr;
    _ = &asConst;
    _ = &dropConst;
    _ = &asVolatile;
    _ = &align4;
    _ = &parentOfX;
    _ = &parentOfY;
    _ = &flagsToByte;
    _ = &byteToFlags;
    _ = &setMode;
    _ = &incCount;
    _ = &isOk;
    _ = &headerLen;
    _ = &readHeader;
    _ = &floatBits;
    _ = &bitsToFloat;
}
