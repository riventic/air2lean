//! C10: sequentially consistent litmus tests, run natively (`docs/research/C10.md`). The harness
//! is that of `tests/roadmap/weak-ordering/litmus.zig` (each test runs `rounds` times on fresh
//! cells; the threads of a round meet at a relaxed barrier first). The tests are those whose
//! outcome sets separate relaxed, acquire-release and `seq_cst`, which the model cannot
//! (`Sc.lean`). One line per test and variant:
//!
//!   litmus <test> <variant> rounds <n> <outcome>:<count> ...
//!
//! `2+2w` has no load: its outcome is the final value of x and y, read after the join.
const std = @import("std");
const AO = std.builtin.AtomicOrder;

const rounds = 200_000;
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
    /// The registers are the final values of x and y after the join.
    final: bool = false,
};

const x = 0;
const y = 1;
const rlx = AO.monotonic;

/// Must match `Sc.lean`'s `tests` (same names, threads and operations).
const tests = [_]Test{
    .{ .name = "sb", .variant = "relaxed", .regs = 2, .threads = &.{
        &.{ st(x, 1, rlx), ld(y, 0, rlx) },
        &.{ st(y, 1, rlx), ld(x, 1, rlx) },
    } },
    .{ .name = "sb", .variant = "release_acquire", .regs = 2, .threads = &.{
        &.{ st(x, 1, .release), ld(y, 0, .acquire) },
        &.{ st(y, 1, .release), ld(x, 1, .acquire) },
    } },
    .{ .name = "sb", .variant = "seq_cst", .regs = 2, .threads = &.{
        &.{ st(x, 1, .seq_cst), ld(y, 0, .seq_cst) },
        &.{ st(y, 1, .seq_cst), ld(x, 1, .seq_cst) },
    } },
    // One thread uses seq_cst, the other release/acquire: RC11 gives no SC guarantee.
    .{ .name = "sb", .variant = "mixed", .regs = 2, .threads = &.{
        &.{ st(x, 1, .seq_cst), ld(y, 0, .seq_cst) },
        &.{ st(y, 1, .release), ld(x, 1, .acquire) },
    } },
    .{ .name = "2+2w", .variant = "relaxed", .regs = 2, .final = true, .threads = &.{
        &.{ st(x, 1, rlx), st(y, 2, rlx) },
        &.{ st(y, 1, rlx), st(x, 2, rlx) },
    } },
    .{ .name = "2+2w", .variant = "release", .regs = 2, .final = true, .threads = &.{
        &.{ st(x, 1, .release), st(y, 2, .release) },
        &.{ st(y, 1, .release), st(x, 2, .release) },
    } },
    .{ .name = "2+2w", .variant = "seq_cst", .regs = 2, .final = true, .threads = &.{
        &.{ st(x, 1, .seq_cst), st(y, 2, .seq_cst) },
        &.{ st(y, 1, .seq_cst), st(x, 2, .seq_cst) },
    } },
    .{ .name = "iriw", .variant = "acquire", .regs = 4, .threads = &.{
        &.{st(x, 1, .release)},
        &.{st(y, 1, .release)},
        &.{ ld(x, 0, .acquire), ld(y, 1, .acquire) },
        &.{ ld(y, 2, .acquire), ld(x, 3, .acquire) },
    } },
    .{ .name = "iriw", .variant = "seq_cst", .regs = 4, .threads = &.{
        &.{st(x, 1, .seq_cst)},
        &.{st(y, 1, .seq_cst)},
        &.{ ld(x, 0, .seq_cst), ld(y, 1, .seq_cst) },
        &.{ ld(y, 2, .seq_cst), ld(x, 3, .seq_cst) },
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
    if (t.final) {
        for (0..rounds) |i| {
            regs[0][i] = cells[x][i];
            regs[1][i] = cells[y][i];
        }
    }
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
