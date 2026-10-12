//! T04: weak-ordering litmus tests, run natively (`scripts/weak-ordering.py observe`). Each test
//! runs `rounds` times on fresh cells; the threads of a round meet at a relaxed barrier first, so
//! they race. One line per test and ordering variant:
//!
//!   litmus <test> <variant> rounds <n> <outcome>:<count> ...
//!
//! An outcome is the registers r0, r1, ... as decimal digits, in register order. Which outcomes
//! occur depends on the hardware and the run; `Litmus.lean` checks that each one is an outcome of
//! the model's atomics (`ZigLean/Mem/Thread.lean`). Uses only `std.Thread`, `std.atomic` and
//! `std.debug.print`, which every supported Zig version has.
const std = @import("std");
const AO = std.builtin.AtomicOrder;

const rounds = 100_000;
const locs = 2;
const max_regs = 4;

const Op = struct {
    store: bool,
    loc: usize,
    ord: AO,
    /// The stored value, or the register a load writes.
    arg: u32,
};

fn st(loc: usize, v: u32, ord: AO) Op {
    return .{ .store = true, .loc = loc, .ord = ord, .arg = v };
}
fn ld(loc: usize, reg: u32, ord: AO) Op {
    return .{ .store = false, .loc = loc, .ord = ord, .arg = reg };
}

const Test = struct {
    name: []const u8,
    variant: []const u8,
    threads: []const []const Op,
    regs: usize,
};

const x = 0;
const y = 1;
const rlx = AO.monotonic;

/// Must match `Litmus.lean`'s `tests` (same names, threads and operations).
const tests = [_]Test{
    .{ .name = "mp", .variant = "relaxed", .regs = 2, .threads = &.{
        &.{ st(x, 1, rlx), st(y, 1, rlx) },
        &.{ ld(y, 0, rlx), ld(x, 1, rlx) },
    } },
    .{ .name = "mp", .variant = "release_acquire", .regs = 2, .threads = &.{
        &.{ st(x, 1, rlx), st(y, 1, .release) },
        &.{ ld(y, 0, .acquire), ld(x, 1, rlx) },
    } },
    .{ .name = "sb", .variant = "relaxed", .regs = 2, .threads = &.{
        &.{ st(x, 1, rlx), ld(y, 0, rlx) },
        &.{ st(y, 1, rlx), ld(x, 1, rlx) },
    } },
    .{ .name = "sb", .variant = "seq_cst", .regs = 2, .threads = &.{
        &.{ st(x, 1, .seq_cst), ld(y, 0, .seq_cst) },
        &.{ st(y, 1, .seq_cst), ld(x, 1, .seq_cst) },
    } },
    .{ .name = "lb", .variant = "relaxed", .regs = 2, .threads = &.{
        &.{ ld(x, 0, rlx), st(y, 1, rlx) },
        &.{ ld(y, 1, rlx), st(x, 1, rlx) },
    } },
    .{ .name = "corr", .variant = "relaxed", .regs = 2, .threads = &.{
        &.{ st(x, 1, rlx), st(x, 2, rlx) },
        &.{ ld(x, 0, rlx), ld(x, 1, rlx) },
    } },
    .{ .name = "wrc", .variant = "release_acquire", .regs = 3, .threads = &.{
        &.{st(x, 1, .release)},
        &.{ ld(x, 0, .acquire), st(y, 1, .release) },
        &.{ ld(y, 1, .acquire), ld(x, 2, rlx) },
    } },
    .{ .name = "iriw", .variant = "relaxed", .regs = 4, .threads = &.{
        &.{st(x, 1, rlx)},
        &.{st(y, 1, rlx)},
        &.{ ld(x, 0, rlx), ld(y, 1, rlx) },
        &.{ ld(y, 2, rlx), ld(x, 3, rlx) },
    } },
    .{ .name = "iriw", .variant = "acquire", .regs = 4, .threads = &.{
        &.{st(x, 1, rlx)},
        &.{st(y, 1, rlx)},
        &.{ ld(x, 0, .acquire), ld(y, 1, .acquire) },
        &.{ ld(y, 2, .acquire), ld(x, 3, .acquire) },
    } },
};

var cells: [locs][rounds]u32 = undefined;
var regs: [max_regs][rounds]u32 = undefined;
var barrier: [rounds]u32 = undefined;

fn Runner(comptime ops: []const Op, comptime n: u32) type {
    return struct {
        fn go() void {
            for (0..rounds) |i| {
                _ = @atomicRmw(u32, &barrier[i], .Add, 1, .monotonic);
                while (@atomicLoad(u32, &barrier[i], .monotonic) != n) std.atomic.spinLoopHint();
                inline for (ops) |op| {
                    if (op.store) {
                        @atomicStore(u32, &cells[op.loc][i], op.arg, op.ord);
                    } else {
                        regs[op.arg][i] = @atomicLoad(u32, &cells[op.loc][i], op.ord);
                    }
                }
            }
        }
    };
}

fn runTest(comptime t: Test) !void {
    for (&cells) |*c| @memset(c, 0);
    for (&regs) |*r| @memset(r, 0);
    @memset(&barrier, 0);
    var handles: [t.threads.len]std.Thread = undefined;
    inline for (t.threads, 0..) |ops, k| {
        handles[k] = try std.Thread.spawn(.{}, Runner(ops, t.threads.len).go, .{});
    }
    for (handles) |h| h.join();
    // Outcome histogram: every register is 0, 1 or 2 (base 3).
    var counts: [81]u32 = @splat(0);
    for (0..rounds) |i| {
        var key: usize = 0;
        for (0..t.regs) |r| key = key * 3 + @min(regs[r][i], 2);
        counts[key] += 1;
    }
    std.debug.print("litmus {s} {s} rounds {d}", .{ t.name, t.variant, rounds });
    for (counts, 0..) |c, key| {
        if (c == 0) continue;
        var digits: [max_regs]u8 = undefined;
        var rest = key;
        var r = t.regs;
        while (r > 0) {
            r -= 1;
            digits[r] = '0' + @as(u8, @intCast(rest % 3));
            rest /= 3;
        }
        std.debug.print(" {s}:{d}", .{ digits[0..t.regs], c });
    }
    std.debug.print("\n", .{});
}

pub fn main() !void {
    inline for (tests) |t| try runTest(t);
}
