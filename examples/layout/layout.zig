//! M20: casts (`@intFromPtr`, `@ptrFromInt`, `@ptrCast`, `@constCast`, `@volatileCast`,
//! `@alignCast`), `@fieldParentPtr`, `packed` and `extern` structs, function pointers, tagged,
//! bare, `extern` and `packed` unions and error unions in memory, and a write to a `const`
//! global.

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

fn double(x: u32) u32 {
    return x *% 2;
}

fn square(x: u32) u32 {
    return x *% x;
}

fn succ(x: u32) u32 {
    return x +% 1;
}

/// A global table of function pointers.
const ops = [_]*const fn (u32) u32{ &double, &square, &succ };

/// `ops[i](x)` (an indirect call; panics if `i` is out of bounds).
pub fn applyOp(i: usize, x: u32) u32 {
    return ops[i](x);
}

/// `f(f(x))`: `f` is a runtime function pointer.
fn applyTwice(f: *const fn (u32) u32, x: u32) u32 {
    return f(f(x));
}

/// `square(square(x))` if `sq`, else `double(double(x))`.
pub fn twice(sq: bool, x: u32) u32 {
    return applyTwice(if (sq) &square else &double, x);
}

pub const Rect = struct {
    w: u16,
    h: u16,
};

pub const Shape = union(enum) {
    circle: u32,
    rect: Rect,
    none,
};

/// Store a circle at `p` (a tagged union store).
pub fn setCircle(p: *Shape, r: u32) void {
    p.* = .{ .circle = r };
}

/// `3 * r * r`, `w * h` or 0, wrapping (a tagged union load).
pub fn shapeArea(p: *const Shape) u32 {
    return switch (p.*) {
        .circle => |r| 3 *% r *% r,
        .rect => |q| @as(u32, q.w) *% q.h,
        .none => 0,
    };
}

/// Add 1 to the radius if `p` is a circle (a pointer to the active payload).
pub fn growCircle(p: *Shape) void {
    switch (p.*) {
        .circle => |*r| r.* +%= 1,
        else => {},
    }
}

pub const ParseError = error{ Empty, TooBig };

fn digit(c: u8) ParseError!u8 {
    if (c == 0) return error.Empty;
    if (c > 9) return error.TooBig;
    return c;
}

/// Add 1 to the payload of `r`, if it has one.
fn bump(r: *ParseError!u8) void {
    if (r.*) |*v| v.* +%= 1 else |_| {}
}

/// `digit(c) + 1`, or 100 for `error.Empty` and 200 for `error.TooBig` (an error union in a
/// memory block).
pub fn bumpDigit(c: u8) u8 {
    var r = digit(c);
    bump(&r);
    return r catch |e| switch (e) {
        error.Empty => 100,
        error.TooBig => 200,
    };
}

/// A bare union. In `ReleaseSafe` it has a hidden tag: a read of a field that is not active
/// panics.
pub const Num = union {
    int: u32,
    small: u8,
};

/// Store `v` in `p.int` if `big`, else its low byte in `p.small`.
pub fn setNum(p: *Num, big: bool, v: u32) void {
    p.* = if (big) .{ .int = v } else .{ .small = @truncate(v) };
}

/// `p.int` (panics if `small` is active).
pub fn numInt(p: *const Num) u32 {
    return p.int;
}

/// `setNum`, then `numInt`: `v` if `big`, else a panic.
pub fn numRoundTrip(big: bool, v: u32) u32 {
    var n: Num = undefined;
    setNum(&n, big, v);
    return numInt(&n);
}

/// An `extern` union: all fields start at byte 0, and a read of a field reads those bytes.
pub const Word = extern union {
    int: u32,
    half: u16,
    bytes: [4]u8,
};

/// Byte `i` of `v`, little-endian (`v` in `int`, read through `bytes`).
pub fn wordByte(v: u32, i: u2) u8 {
    var w: Word = .{ .int = v };
    const p: *Word = &w;
    return p.bytes[i];
}

/// Write `v` to `p.half`, then read `p.int`: the two high bytes do not change.
pub fn setHalf(p: *Word, v: u16) u32 {
    p.half = v;
    return p.int;
}

/// A `packed` union: every field has the same bit width and starts at bit 0.
pub const Reg = packed union {
    raw: u8,
    signed: i8,
    flags: Flags,
};

/// `v` as an `i8` (`v` in `raw`, read through `signed`).
pub fn regSigned(v: u8) i8 {
    const r: Reg = .{ .raw = v };
    return r.signed;
}

/// Write `f` to `p.flags`, then read `p.raw`.
pub fn setRegFlags(p: *Reg, f: Flags) u8 {
    p.flags = f;
    return p.raw;
}

/// A `const` global: its block is read-only.
const table = [_]u32{ 10, 20, 30 };

/// Write `v` to `table[i]` through `@constCast`: illegal behaviour (the model throws
/// `.illegal`).
pub fn writeTable(i: usize, v: u32) u32 {
    const p: *u32 = @constCast(&table[i]);
    p.* = v;
    return table[i];
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
    _ = &applyOp;
    _ = &twice;
    _ = &setCircle;
    _ = &shapeArea;
    _ = &growCircle;
    _ = &bumpDigit;
    _ = &setNum;
    _ = &numInt;
    _ = &numRoundTrip;
    _ = &wordByte;
    _ = &setHalf;
    _ = &regSigned;
    _ = &setRegFlags;
    _ = &writeTable;
}
