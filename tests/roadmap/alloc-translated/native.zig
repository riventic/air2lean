const std = @import("std");
const fba = @import("fba.zig");
const page = @import("page.zig");

pub fn main() void {
    std.debug.print("sum0 ok {d} sum10 ok {d} sum256 ok {d} sum257 ok {d}\n", .{ fba.fba_sum(0), fba.fba_sum(10), fba.fba_sum(256), fba.fba_sum(257) });
    std.debug.print("create ok {d}\n", .{fba.fba_create(7)});
    const b = struct {
        fn f(x: bool) u8 {
            return if (x) 1 else 0;
        }
    }.f;
    std.debug.print("resize ok {d} ok {d} ok {d} ok {d}\n", .{ b(fba.fba_resize(10, 20)), b(fba.fba_resize(10, 300)), b(fba.fba_resize(0, 5)), b(fba.fba_resize(10, 0)) });
    std.debug.print("reset ok {d} ok {d} ok {d}\n", .{ fba.fba_reset(100), fba.fba_reset(200), fba.fba_reset(0) });
    std.debug.print("page_sum ok {d} {d} {d} page_create ok {d} page_resize ok {d} {d} {d}\n", .{ page.page_sum(0), page.page_sum(10), page.page_sum(10000), page.page_create(7), b(page.page_resize(10, 20)), b(page.page_resize(10, 5000)), b(page.page_resize(8192, 10)) });
}
