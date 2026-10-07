//! C01: the tuple is a by-value snapshot; pointer fields preserve their identities.
const std = @import("std");
const Io = if (@hasDecl(std, "Io") and @hasDecl(std.Io, "Group")) std.Io else void;

fn zeroWorker() void {}

fn ZeroWorker(comptime T: type) type {
    return struct {
        fn run() void {
            const value: T = 0;
            _ = value;
        }
    };
}

fn mixedWorker(first: u32, out: *u32, second: u32, other: *u32) void {
    out.* = first *% 17 +% second *% 3;
    other.* = first *% 5 +% second *% 11;
}

fn copyWorker(out: *u32, first: u32, second: u32, third: u32) void {
    out.* = first *% 3 +% second *% 5 +% third *% 7;
}

fn atomicWorker(out: *u32, shared: *std.atomic.Value(u32), first: u32, second: u32) void {
    out.* = first +% second;
    _ = shared.fetchAdd(second, .seq_cst);
}

pub fn empty() !void {
    const handle = try std.Thread.spawn(.{}, zeroWorker, .{});
    handle.join();
}

pub fn genericEmpty() !void {
    const handle = try std.Thread.spawn(.{}, ZeroWorker(u8).run, .{});
    handle.join();
}

pub fn mixed(first: u32, second: u32) !u32 {
    var out: u32 = 0;
    var other: u32 = 0;
    const handle = try std.Thread.spawn(.{}, mixedWorker, .{ first, &out, second, &other });
    handle.join();
    return out +% other *% 7;
}

pub fn copied(first: u32, second: u32, third: u32) !u32 {
    var snapshot = first;
    var out: u32 = 0;
    const handle = try std.Thread.spawn(.{}, copyWorker, .{ &out, snapshot, second, third });
    snapshot = 99;
    handle.join();
    return out +% snapshot;
}

pub fn atomicShared(first: u32, second: u32) !u32 {
    var shared = std.atomic.Value(u32).init(0);
    var left: u32 = 0;
    var right: u32 = 0;
    const one = try std.Thread.spawn(.{}, atomicWorker, .{ &left, &shared, first, second });
    errdefer one.join();
    const two = try std.Thread.spawn(.{}, atomicWorker, .{ &right, &shared, second, first });
    one.join();
    two.join();
    return left +% right +% shared.load(.seq_cst);
}

pub fn groupMixed(io: Io, first: u32, second: u32) !u32 {
    var out: u32 = 0;
    var other: u32 = 0;
    var group: Io.Group = .init;
    // Every exit (including a failed `concurrent`) must finish the tasks that
    // write `out` and `other` before this frame is freed. A no-op after `await`.
    defer group.cancel(io);
    group.async(io, zeroWorker, .{});
    group.async(io, mixedWorker, .{ first, &out, second, &other });
    try group.concurrent(io, zeroWorker, .{});
    try group.await(io);
    return out +% other *% 7;
}

comptime {
    _ = &empty;
    _ = &genericEmpty;
    _ = &mixed;
    _ = &copied;
    _ = &atomicShared;
    if (@hasDecl(std, "Io") and @hasDecl(std.Io, "Group")) _ = &groupMixed;
}
