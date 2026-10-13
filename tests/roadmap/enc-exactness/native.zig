//! Prints each case of `enc_exactness.zig` and `opaque_bytes.zig` as one line `name: value` on
//! stderr (hex); `Model.lean` prints the model's lines for the same cases (`unspecified` matches
//! any value).
//! The operands are volatile loads, so the compiler cannot fold the cases. Run by
//! `check.sh --native`.
const std = @import("std");
const ee = @import("enc_exactness.zig");
const ob = @import("opaque_bytes.zig");

fn ld(comptime T: type, v: T) T {
    var x: T = v;
    return @as(*volatile T, &x).*;
}

fn hex(name: []const u8, v: anytype) void {
    const T = @TypeOf(v);
    const U = if (@bitSizeOf(T) == 16) u16 else if (@bitSizeOf(T) == 32) u32 else u8;
    std.debug.print("{s}: 0x{x}\n", .{ name, @as(U, @bitCast(v)) });
}

pub fn main() void {
    hex("i10ZeroPad", ee.i10ZeroPad(ld(u16, 0x0200)));
    hex("u24SetPad", ee.u24SetPad(ld(u32, 0x0100_0005)));
    hex("i24ZeroPad", ee.i24ZeroPad(ld(u32, 0x0080_0000)));
    hex("e24SetPad", ee.e24SetPad(ld(u32, 0x0100_0005)));
    hex("i10StoreBytes", ee.i10StoreBytes(ld(i10, -1)));
    hex("u24StoreBytes", ee.u24StoreBytes(ld(u24, 5)));
    hex("i24RoundTrip", ee.i24RoundTrip(ld(i24, -2)));
    hex("boolByte", ee.boolByte(ld(bool, true)));
    // The allocator's `vtable` word is an address: only whether it is 0.
    hex("allocatorWordIsZero", @as(u8, @intFromBool(ob.allocatorWord(std.heap.page_allocator) == 0)));
}
