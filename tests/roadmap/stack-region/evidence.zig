// Native evidence for the stack-region model (docs/architecture-audit/memory-model.md MM-16).
// Prints `key value` lines that check.sh compares; the same on every target and Zig version
// (0.14.1-0.17.0) that was measured.
// E1:  an inlinable callee's escaping local lies above its caller's earlier local (LLVM inlining);
//      a noinline callee's lies below.
// E1': the inlined callee's local and a later local of the caller share one address.
// E2:  sibling calls reuse a dead frame's addresses.
// E3:  a spawned thread's local lies in an anonymous mapping that is not the main stack (Linux:
//      the mapping that std.Thread.spawn mmaps, MM-19).
const std = @import("std");
const builtin = @import("builtin");

var sink: [16]usize = @splat(0);
var childMapped: bool = false;

noinline fn record(i: usize, p: *const u64) void {
    sink[i] = @intFromPtr(p);
}

fn calleeInl() void {
    var y: u64 = 2;
    record(1, &y);
}

fn callerInl() void {
    var x: u64 = 1;
    record(0, &x);
    calleeInl();
    var z: u64 = 3;
    record(2, &z);
}

noinline fn calleeNo() void {
    var y: u64 = 2;
    record(4, &y);
}

noinline fn callerNo() void {
    var x: u64 = 1;
    record(3, &x);
    calleeNo();
}

noinline fn sibling(i: usize) void {
    var y: u64 = 7;
    record(i, &y);
}

fn child() void {
    var c: u64 = 9;
    record(8, &c);
    childMapped = inAnonMapping(sink[8]);
}

/// Linux: the mapping of `/proc/self/maps` that holds `addr` is anonymous and not `[stack]`.
fn inAnonMapping(addr: usize) bool {
    if (builtin.os.tag != .linux) return false;
    var buf: [1 << 16]u8 = undefined;
    const linux = std.os.linux;
    const rc = linux.open("/proc/self/maps", .{}, 0);
    if (@as(isize, @bitCast(rc)) < 0) return false;
    const fd: i32 = @intCast(rc);
    var n: usize = 0;
    while (true) {
        const r = linux.read(fd, buf[n..].ptr, buf.len - n);
        if (@as(isize, @bitCast(r)) <= 0) break;
        n += r;
    }
    var it = std.mem.splitScalar(u8, buf[0..n], '\n');
    while (it.next()) |line| {
        const dash = std.mem.indexOfScalar(u8, line, '-') orelse continue;
        const sp = std.mem.indexOfScalar(u8, line, ' ') orelse continue;
        const lo = std.fmt.parseInt(usize, line[0..dash], 16) catch continue;
        const hi = std.fmt.parseInt(usize, line[dash + 1 .. sp], 16) catch continue;
        if (lo <= addr and addr < hi) {
            // Fields: range perms offset dev inode [path]; an anonymous mapping has no path.
            var fields = std.mem.tokenizeScalar(u8, line, ' ');
            var k: usize = 0;
            while (fields.next()) |_| k += 1;
            return k == 5;
        }
    }
    return false;
}

fn flag(b: bool) u8 {
    return if (b) 1 else 0;
}

pub fn main() void {
    callerInl();
    callerNo();
    sibling(5);
    sibling(6);
    const t = std.Thread.spawn(.{}, child, .{}) catch return;
    t.join();
    std.debug.print("E1 {d}\n", .{flag(sink[1] > sink[0])});
    std.debug.print("E1' {d}\n", .{flag(sink[1] == sink[2])});
    std.debug.print("E1noinline {d}\n", .{flag(sink[4] < sink[3])});
    std.debug.print("E2 {d}\n", .{flag(sink[5] == sink[6])});
    std.debug.print("E3 {s}\n", .{if (builtin.os.tag != .linux) "n/a" else if (childMapped) "1" else "0"});
}
