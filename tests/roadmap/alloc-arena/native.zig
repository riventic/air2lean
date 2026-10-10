const std = @import("std");
const arena = @import("arena.zig");

pub fn main() void {
    const b = struct {
        fn f(x: bool) u8 {
            return if (x) 1 else 0;
        }
    }.f;
    std.debug.print("sum ok {d} ok {d} ok {d} ok {d}\n", .{ arena.arena_sum(1), arena.arena_sum(10), arena.arena_sum(3000), arena.arena_sum(5000) });
    std.debug.print("resize ok {d} ok {d} ok {d} ok {d}\n", .{ b(arena.arena_resize(10, 20)), b(arena.arena_resize(10, 5)), b(arena.arena_resize(10, 100)), b(arena.arena_resize(10, 4000)) });
    std.debug.print("reset ok {d} ok {d} ok {d} ok {d}\n", .{ arena.arena_reset(10, true), arena.arena_reset(10, false), arena.arena_reset(500, true), arena.arena_reset(1500, true) });
    std.debug.print("page ok {d} ok {d}\n", .{ arena.arena_page(10), arena.arena_page(20000) });
}
