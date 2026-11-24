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
    // M02: growth by `remap` (0) and by `realloc` (1): in place after the pages behind the block
    // were freed, within the page, a shrink, an impossible length, and into a neighbour's pages.
    const far = 1 << 47;
    std.debug.print("page_grow remap ok {d} {d} {d} {d} blocked ok {d} realloc ok {d} {d} {d} {d} blocked ok {d}\n", .{
        page.page_grow(81920, 10, 49152, 0), page.page_grow(10, 10, 20, 0), page.page_grow(49152, 49152, 10, 0),
        page.page_grow(10, 10, far, 0),      page.page_grow_blocked(10, 0),
        page.page_grow(81920, 10, 49152, 1), page.page_grow(10, 10, 20, 1), page.page_grow(49152, 49152, 10, 1),
        page.page_grow(10, 10, far, 1),      page.page_grow_blocked(10, 1),
    });
    std.debug.print("page_grow_stale remap {s} realloc {s}\n", .{ stale(0), stale(1) });
}

/// The segfault handler would turn the stale read's fault into a message and an abort.
pub const std_options: std.Options = .{ .enable_segfault_handler = false };

/// `page_grow_stale` in a child process: "ok <result>" when it returns, "fail illegal" when the
/// read of the moved block's old address faults (the model's `.illegal`).
fn stale(how: u8) []const u8 {
    const system = std.posix.system;
    const pid = system.fork();
    if (pid == 0) {
        const r = page.page_grow_stale(10, how);
        system.exit(@intCast(r));
    }
    const Status = if (@import("builtin").link_libc) c_int else u32;
    var status: Status = undefined;
    _ = system.waitpid(@intCast(pid), &status, 0);
    const s: u32 = @bitCast(status);
    const sig = s & 0x7f;
    if (sig == 0) return switch ((s >> 8) & 0xff) {
        0 => "ok 0",
        else => "ok other",
    };
    return if (sig == @intFromEnum(std.posix.SIG.SEGV) or sig == @intFromEnum(std.posix.SIG.BUS)) "fail illegal" else "fail signal";
}
