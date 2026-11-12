//! L09/L07: `@bitCast` with a vector side (`docs/generated-code.md` §Casts). Up to Zig 0.16.0
//! `[n]T` ↔ `@Vector(n, T)` is lane `i` = item `i`, for whole-byte and for padded items alike;
//! any other vector cast reinterprets the vector's memory image (bit-packed lanes, LLVM backend).
//! `eqlChunk` is the shape of `std.mem.eqlBytes`, which `std.mem.eql(u8, …)` calls for slices
//! of more than 16 bytes (`stdEql`). Zig 0.17.0 uses the logical bit order instead
//! (`docs/bitcast-semantics.md`); its exports translate with those rules. The functions are
//! `pub` and referenced in a `comptime` block: array and vector parameters are not C ABI types.
const std = @import("std");

/// `std.mem.eqlBytes`'s 16-byte step: two array loads cast to vectors and compared.
pub fn eqlChunk(a: [16]u8, b: [16]u8) bool {
    const va: @Vector(16, u8) = @bitCast(a);
    const vb: @Vector(16, u8) = @bitCast(b);
    return !@reduce(.Or, va != vb);
}

/// `std.mem.eql` on 40-byte slices: `mem.eqlBytes` with its vector chunks.
pub fn stdEql(a: *const [40]u8, b: *const [40]u8) bool {
    return std.mem.eql(u8, a, b);
}

pub fn bytesToLanes(a: [4]u8) @Vector(4, u8) {
    return @bitCast(a);
}

pub fn lanesToBytes(v: @Vector(4, u8)) [4]u8 {
    return @bitCast(v);
}

/// A padded item (`@sizeOf(u24) = 4`): lane `i` is item `i`, not the array's bytes. `@bitCast`
/// needs equal `@bitSizeOf`, so with padded items only one item converts (`[3]u24` has 88 bits,
/// `@Vector(3, u24)` 72).
pub fn u24ItemToLane(a: [1]u24) @Vector(1, u24) {
    return @bitCast(a);
}

pub fn u24LaneToItem(v: @Vector(1, u24)) [1]u24 {
    return @bitCast(v);
}

pub fn boolItemToLane(a: [1]bool) @Vector(1, bool) {
    return @bitCast(a);
}

/// The memory image of a `bool` vector: lane `i` is bit `i`.
pub fn boolLanesToByte(v: @Vector(8, bool)) u8 {
    return @bitCast(v);
}

pub fn lanesToWord(v: @Vector(4, u8)) u32 {
    return @bitCast(v);
}

pub fn wordToLanes(x: u32) @Vector(4, u8) {
    return @bitCast(x);
}

/// Bytes to wider lanes: the array's bytes are the vector's memory image.
pub fn bytesToHalves(a: [4]u8) @Vector(2, u16) {
    return @bitCast(a);
}

pub fn halvesToBytes(v: @Vector(2, u16)) [4]u8 {
    return @bitCast(v);
}

/// Non-byte lanes: bit-packed, lane 0 in the low bits.
pub fn packedLanesToInt(v: @Vector(3, u3)) u9 {
    return @bitCast(v);
}

pub fn intToPackedLanes(x: u9) @Vector(3, u3) {
    return @bitCast(x);
}

comptime {
    _ = &eqlChunk;
    _ = &stdEql;
    _ = &bytesToLanes;
    _ = &lanesToBytes;
    _ = &u24ItemToLane;
    _ = &u24LaneToItem;
    _ = &boolItemToLane;
    _ = &boolLanesToByte;
    _ = &lanesToWord;
    _ = &wordToLanes;
    _ = &bytesToHalves;
    _ = &halvesToBytes;
    _ = &packedLanesToInt;
    _ = &intToPackedLanes;
}
