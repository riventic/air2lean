const std = @import("std");
const up = @import("up");
pub fn main() void {
    var x: u2 = 3;
    _ = &x;
    std.debug.print("enumUnsafe(3) = {d}\n", .{up.enumUnsafe(x)});
    var u: up.U = .{ .b = 7 };
    _ = &u;
    std.debug.print("unionUnsafe(.b=7) = {d}\n", .{up.unionUnsafe(u)});
    var b: up.B = .{ .b = 9 };
    _ = &b;
    std.debug.print("bareUnsafe(.b=9) = {d}\n", .{up.bareUnsafe(b)});
    var y: u32 = 11;
    _ = &y;
    std.debug.print("unionLocal(11) = {d}\n", .{up.unionLocal(y)});
    std.debug.print("bareLocal(11) = {d}\n", .{up.bareLocal(y)});
    extra();
}
pub fn extra() void {
    var a: u32 = 7;
    var b: u32 = 0;
    _ = &a;
    _ = &b;
    std.debug.print("divUnsafe(7,0) = {d}\n", .{up.divUnsafe(a, b)});
    var m: u32 = 0xffffffff;
    _ = &m;
    std.debug.print("addUnsafe(max,7) = {d}\n", .{up.addUnsafe(m, a)});
    std.debug.print("intCastUnsafe(0x1ff) = {d}\n", .{up.intCastUnsafe(m)});
}
