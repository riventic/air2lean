//! Native observations of the illegal-behaviour input classes (docs/illegal-behavior.md).
//! `check.sh` builds this with stock Zig 0.16.0 in ReleaseSafe and ReleaseFast and keeps the
//! output (`native/<mode>.txt`). Every row is illegal behaviour that the build does not check,
//! so the builds may disagree; `Cases.lean` shows that the model gives `.illegal` for each row,
//! so the differential harness never compares them. Lines: `<case> <result bits in hex>`.
const std = @import("std");
const ib = @import("ib");

fn f64Bits(x: f64) u64 {
    return @bitCast(x);
}

fn bitsF64(b: u64) f64 {
    return @bitCast(b);
}

pub fn main() void {
    const one = bitsF64(0x3FF0000000000000);
    const two = bitsF64(0x4000000000000000);
    const three = bitsF64(0x4008000000000000);
    const tiny = bitsF64(1);
    const nan = bitsF64(0x7FF8000000000000);
    std.debug.print("divExactSafe tiny/1 {x:0>16}\n", .{f64Bits(ib.divExactSafe(tiny, one))});
    std.debug.print("divExactSafe 3/2 {x:0>16}\n", .{f64Bits(ib.divExactSafe(three, two))});
    std.debug.print("divExactSafe 1/0 {x:0>16}\n", .{f64Bits(ib.divExactSafe(one, 0.0))});
    std.debug.print("divExactUnsafe tiny/1 {x:0>16}\n", .{f64Bits(ib.divExactUnsafe(tiny, one))});
    std.debug.print("divExactUnsafe 3/2 {x:0>16}\n", .{f64Bits(ib.divExactUnsafe(three, two))});
    const lanes = ib.divExactLanes(.{ tiny, three }, .{ one, two });
    std.debug.print("divExactLanes {x:0>16} {x:0>16}\n", .{ f64Bits(lanes[0]), f64Bits(lanes[1]) });
    std.debug.print("divExactIntUnsafe 7/2 {x:0>8}\n", .{@as(u32, @bitCast(ib.divExactIntUnsafe(7, 2)))});
    std.debug.print("shlExactUnsafe 0x80000000<<1 {x:0>8}\n", .{ib.shlExactUnsafe(0x80000000, 1)});
    std.debug.print("shl24Unsafe 1<<24 {x:0>6}\n", .{ib.shl24Unsafe(1, 24)});
    std.debug.print("shr24Unsafe 0x800000>>31 {x:0>6}\n", .{ib.shr24Unsafe(0x800000, 31)});
    std.debug.print("toIntSafe nan {x:0>8}\n", .{@as(u32, @bitCast(ib.toIntSafe(nan)))});
    std.debug.print("toIntUnsafe nan {x:0>8}\n", .{@as(u32, @bitCast(ib.toIntUnsafe(nan)))});
    std.debug.print("toIntUnsafe 2^31 {x:0>8}\n", .{@as(u32, @bitCast(ib.toIntUnsafe(2147483648.0)))});
    var buf = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
    ib.copyOverlapUnsafe(&buf, 4);
    std.debug.print("copyOverlapUnsafe {x}\n", .{buf});
}
