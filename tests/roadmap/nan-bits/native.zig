//! Prints each case of `nan_bits.zig` as one line `name: value` on stderr (hex, `bool` as 0/1);
//! `Model.lean` prints the model's lines for the same cases. The operands are volatile loads, so
//! the compiler cannot fold the NaN-making operations. Run by `check.sh --native`.
const std = @import("std");
const nb = @import("nan_bits.zig");

var zero32: f32 = 0;
var one32: f32 = 1;
var three32: f32 = 3;
var zero64: f64 = 0;
/// A quiet NaN with a payload.
var payload32: u32 = 0x7fc0_0123;

fn ld(comptime T: type, p: *T) T {
    return @as(*volatile T, p).*;
}

fn hex(name: []const u8, v: anytype) void {
    std.debug.print("{s}: 0x{x}\n", .{ name, v });
}

pub fn main() void {
    const z = ld(f32, &zero32);
    hex("storeLoad", nb.storeLoad(z, z));
    hex("storeLoad64", nb.storeLoad64(ld(f64, &zero64), ld(f64, &zero64)));
    hex("sumBits", nb.sumBits(@bitCast(ld(u32, &payload32)), ld(f32, &one32)));
    hex("unionView", nb.unionView(z, z));
    hex("arrayCast", nb.arrayCast(z, z));
    hex("vectorCast", nb.vectorCast(z, z));
    hex("structView", nb.structView(z, z));
    hex("copyBytes", nb.copyBytes(z, z));
    hex("finiteBits", nb.finiteBits(ld(f32, &one32), ld(f32, &three32)));
    hex("constStore", nb.constStore());
    hex("constGlobal", nb.constGlobal());
    hex("reloadIsNaN", @intFromBool(nb.reloadIsNaN(z, z)));
}
