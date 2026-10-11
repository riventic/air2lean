//! Architecture audit (concurrency): native litmus runs on the host (aarch64 macOS).
//! Build: zig build-exe -OReleaseFast native_litmus.zig; run: ./native_litmus [iterations]
//! Prints per-test outcome counts. The model-side counterpart is litmus.zig.
const std = @import("std");

var x = std.atomic.Value(u32).init(0);
var y = std.atomic.Value(u32).init(0);
var data: u32 = 0;
var flag = std.atomic.Value(u32).init(0);
var go_ = std.atomic.Value(u32).init(0);
var done = std.atomic.Value(u32).init(0);
var r1: u32 = 0;
var r2: u32 = 0;
var iters: u32 = 10_000_000;
var which: u32 = 0;

fn barrier(i: u32) void {
    while (go_.load(.acquire) != i) std.atomic.spinLoopHint();
}

fn t1() void {
    var i: u32 = 1;
    while (i <= iters) : (i += 1) {
        barrier(i);
        switch (which) {
            // LB: r1 = x; y = 1
            0 => {
                r1 = x.load(.monotonic);
                y.store(1, .monotonic);
            },
            // MP (relaxed): x = 1; y = 1
            1 => {
                x.store(1, .monotonic);
                y.store(1, .monotonic);
            },
            // SB (seq_cst): x = 1; r1 = y
            else => {
                x.store(1, .seq_cst);
                r1 = y.load(.seq_cst);
            },
        }
        _ = done.fetchAdd(1, .acq_rel);
    }
}

fn t2() void {
    var i: u32 = 1;
    while (i <= iters) : (i += 1) {
        barrier(i);
        switch (which) {
            0 => {
                r2 = y.load(.monotonic);
                x.store(1, .monotonic);
            },
            1 => {
                r1 = y.load(.monotonic);
                r2 = x.load(.monotonic);
            },
            else => {
                y.store(1, .seq_cst);
                r2 = x.load(.seq_cst);
            },
        }
        _ = done.fetchAdd(1, .acq_rel);
    }
}

fn runOne(w: u32) !u64 {
    which = w;
    go_.store(0, .release);
    const a = try std.Thread.spawn(.{}, t1, .{});
    const b = try std.Thread.spawn(.{}, t2, .{});
    var hits: u64 = 0;
    var i: u32 = 1;
    while (i <= iters) : (i += 1) {
        x.store(0, .monotonic);
        y.store(0, .monotonic);
        r1 = 99;
        r2 = 99;
        done.store(0, .release);
        go_.store(i, .release);
        while (done.load(.acquire) != 2) std.atomic.spinLoopHint();
        const hit = switch (w) {
            0 => r1 == 1 and r2 == 1, // LB
            1 => r1 == 1 and r2 == 0, // MP stale
            else => r1 == 0 and r2 == 0, // SB
        };
        if (hit) hits += 1;
    }
    a.join();
    b.join();
    return hits;
}

pub fn main() !void {
    const names = [_][]const u8{ "LB relaxed r1=r2=1", "MP relaxed r1=1,r2=0", "SB seq_cst r1=r2=0" };
    for (names, 0..) |name, w| {
        const hits = try runOne(@intCast(w));
        std.debug.print("{s}: {d}/{d}\n", .{ name, hits, iters });
    }
}
