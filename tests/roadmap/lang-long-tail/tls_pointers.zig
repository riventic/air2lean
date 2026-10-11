//! L12: pointer-bearing `threadlocal` storage (`docs/generated-code.md` §Thread-local storage),
//! the shape of `std.Io.Threaded`'s `threadlocal var current: ?*Thread = null`. Every thread
//! has its own instance of each global below, initialized with the same bytes: null, a pointer
//! to an ordinary global (one object for all threads), a slice of a string constant.
const std = @import("std");

pub const Node = struct { v: u32, next: ?*Node };

var shared: Node = .{ .v = 5, .next = null };
threadlocal var current: ?*Node = null;
threadlocal var cursor: *Node = &shared;
threadlocal var name: []const u8 = "main";

/// The thread's own node, as `Io.Threaded.Thread.current`.
fn currentValue() u32 {
    const node = current orelse return 0;
    return node.v;
}

/// Points this thread's `current` at a stack node and reads it back through a nested call;
/// also reads the initial `cursor` (the shared global) and `name`.
fn worker(out: *u32) void {
    var mine: Node = .{ .v = 40, .next = null };
    const before = currentValue();
    current = &mine;
    out.* = before * 1000 + currentValue() + cursor.v + @as(u32, @intCast(name.len));
    current = null;
}

/// A worker and the main thread set their own `current`; each sees only its own node.
pub fn perThread() !u32 {
    var a: u32 = 0;
    var local: Node = .{ .v = 1, .next = null };
    current = &local;
    const h = try std.Thread.spawn(.{}, worker, .{&a});
    const mainSees = currentValue();
    h.join();
    current = null;
    return a * 100 + mainSees;
}

/// Without threads: the main thread's instances, set and read back.
pub fn mainOnly(x: u32) u32 {
    var local: Node = .{ .v = x, .next = cursor };
    const was = currentValue();
    current = &local;
    cursor = &local;
    const now = currentValue() +% cursor.next.?.v;
    cursor = &shared;
    current = null;
    name = "main-thread";
    return was +% now +% @as(u32, @intCast(name.len));
}

/// A worker leaves its `current` pointing at its dead stack node in its own instance; the
/// instance itself dies with the thread, so a pointer to it read afterwards is a use after free.
fn leakSlot(out: *?*?*Node) void {
    var mine: Node = .{ .v = 9, .next = null };
    current = &mine;
    out.* = &current;
}

pub fn leakedSlot() !u32 {
    var p: ?*?*Node = null;
    const h = try std.Thread.spawn(.{}, leakSlot, .{&p});
    h.join();
    const slot = p orelse return 0;
    return if (slot.*) |n| n.v else 1;
}

comptime {
    _ = &perThread;
    _ = &mainOnly;
    _ = &leakedSlot;
}
