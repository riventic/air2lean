//! Differential-test input generator (docs/generated-code.md names the 8 functions).
//! Run from the repo root: `zig run tests/diff/gen_inputs.zig`.
//!
//! Writes `tests/diff/inputs/<fn>.jsonl`: one JSON array of args per line, N = 300 lines
//! per function. Each file starts with a fixed set of edge-value lines (0, 1, max, min for
//! signed, max-1, empty slice, 1-element slice, and — where an accumulator can overflow —
//! slices crafted to overflow it), then fills up to 300 with values from a seeded PRNG, so
//! the output is byte-identical across runs.
//!
//! None of the 8 functions take a 64-bit parameter, so every argument here fits in a plain
//! JSON number. `tests/diff/harness.zig` and `Diff.lean` write 64-bit *results* (`sum`,
//! `totalWeightedTardiness`) as quoted decimal strings instead, since those can exceed a
//! JS-safe integer; this file has nothing to quote, but follows the same width rule.

const std = @import("std");

const N = 300;
/// Fixed seed: reused across runs, and generator functions run in a fixed order below, so
/// output is deterministic.
const seed: u64 = 0xA17_1EA0_5EED_0001;

const Job = struct { duration: u32, due: u32, weight: u8 };

pub fn main() !void {
    try std.fs.cwd().makePath("tests/diff/inputs");

    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();

    try genScale(rng);
    try genClampAdd(rng);
    try genAbsDiff(rng);
    try genTardiness(rng);
    try genWeightedTardiness(rng);
    try genSum(rng);
    try genTotalWeightedTardiness(rng);
    try genClassify(rng);
}

fn openOut(comptime name: []const u8) !std.fs.File {
    return std.fs.cwd().createFile("tests/diff/inputs/" ++ name ++ ".jsonl", .{});
}

fn edgesU(comptime T: type) [4]T {
    return .{ 0, 1, std.math.maxInt(T) - 1, std.math.maxInt(T) };
}

fn edgesI(comptime T: type) [7]T {
    return .{ 0, 1, -1, std.math.maxInt(T), std.math.maxInt(T) - 1, std.math.minInt(T), std.math.minInt(T) + 1 };
}

fn printJob(writer: anytype, job: Job) !void {
    try writer.print("{{\"duration\":{d},\"due\":{d},\"weight\":{d}}}", .{ job.duration, job.due, job.weight });
}

/// scale(a: u32, b: u8) -> u32. Edges: 4 x 4 = 16 combos, then random fill.
fn genScale(rng: std.Random) !void {
    const file = try openOut("scale");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesU(u32)) |a| {
        for (edgesU(u8)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d},{d}]\n", .{ rng.int(u32), rng.int(u8) });
    }
}

/// clampAdd(a: u16, b: u16) -> u16 (saturating; never panics). Edges: 4 x 4, then random.
fn genClampAdd(rng: std.Random) !void {
    const file = try openOut("clampAdd");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesU(u16)) |a| {
        for (edgesU(u16)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d},{d}]\n", .{ rng.int(u16), rng.int(u16) });
    }
}

/// absDiff(a: i32, b: i32) -> u32. Edges: 7 x 7 = 49 combos (incl. min/max/-1), then random.
fn genAbsDiff(rng: std.Random) !void {
    const file = try openOut("absDiff");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesI(i32)) |a| {
        for (edgesI(i32)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d},{d}]\n", .{ rng.int(i32), rng.int(i32) });
    }
}

/// tardiness(end: u32, due: u32) -> u32. Edges: 4 x 4, then random.
fn genTardiness(rng: std.Random) !void {
    const file = try openOut("tardiness");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesU(u32)) |a| {
        for (edgesU(u32)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d},{d}]\n", .{ rng.int(u32), rng.int(u32) });
    }
}

/// weightedTardiness(job: Job, start: u32) -> u32. Edges: 4 x 4 x 4 x 4 = 256 combos over
/// (duration, due, weight, start), then random fill. `start + job.duration` and
/// `tardiness(..) * job.weight` are both checked; several edge combos (e.g. start=max,
/// duration=1) drive them into overflow.
fn genWeightedTardiness(rng: std.Random) !void {
    const file = try openOut("weightedTardiness");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesU(u32)) |duration| {
        for (edgesU(u32)) |due| {
            for (edgesU(u8)) |weight| {
                for (edgesU(u32)) |start| {
                    try writer.writeAll("[");
                    try printJob(writer, .{ .duration = duration, .due = due, .weight = weight });
                    try writer.print(",{d}]\n", .{start});
                    n += 1;
                }
            }
        }
    }
    while (n < N) : (n += 1) {
        try writer.writeAll("[");
        try printJob(writer, .{ .duration = rng.int(u32), .due = rng.int(u32), .weight = rng.int(u8) });
        try writer.print(",{d}]\n", .{rng.int(u32)});
    }
}

/// sum(xs: []const u32) -> u64. `total` is u64 and elements are u32, so this accumulator
/// cannot overflow at any slice length reachable here (u32::MAX * 2^32 elements would be
/// needed) — the "large sum" edges below exercise the accumulation path without expecting
/// a panic. Edges: empty, 1-element (0 / 1 / max-1 / max), a few long max-valued slices.
fn genSum(rng: std.Random) !void {
    const file = try openOut("sum");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    try writer.writeAll("[[]]\n");
    n += 1;
    for (edgesU(u32)) |v| {
        try writer.print("[[{d}]]\n", .{v});
        n += 1;
    }
    // Long, large-valued slices: stress accumulation, never overflow (see doc comment).
    inline for (.{ 5, 20, 64 }) |len| {
        try writer.writeAll("[[");
        for (0..len) |i| {
            if (i != 0) try writer.writeAll(",");
            try writer.print("{d}", .{std.math.maxInt(u32)});
        }
        try writer.writeAll("]]\n");
        n += 1;
    }
    while (n < N) : (n += 1) {
        const len = rng.intRangeAtMost(usize, 0, 30);
        try writer.writeAll("[[");
        for (0..len) |i| {
            if (i != 0) try writer.writeAll(",");
            try writer.print("{d}", .{rng.int(u32)});
        }
        try writer.writeAll("]]\n");
    }
}

/// totalWeightedTardiness(jobs: []const Job) -> u64. Edges: empty slice; a 1-element slice
/// over the 4 x 4 x 4 = 64 (duration, due, weight) combos; a handful of 2-element slices
/// crafted so the running `t += jobs[i].duration` (u32) overflows, or `weightedTardiness`'s
/// internal add/multiply overflows on its own; then random-length random fill.
fn genTotalWeightedTardiness(rng: std.Random) !void {
    const file = try openOut("totalWeightedTardiness");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    try writer.writeAll("[[]]\n");
    n += 1;
    for (edgesU(u32)) |duration| {
        for (edgesU(u32)) |due| {
            for (edgesU(u8)) |weight| {
                try writer.writeAll("[[");
                try printJob(writer, .{ .duration = duration, .due = due, .weight = weight });
                try writer.writeAll("]]\n");
                n += 1;
            }
        }
    }

    const max = std.math.maxInt(u32);
    const overflow_cases = [_][2]Job{
        // t += duration overflows on the 2nd element (max + max).
        .{ .{ .duration = max, .due = 0, .weight = 1 }, .{ .duration = max, .due = 0, .weight = 1 } },
        .{ .{ .duration = max, .due = 0, .weight = 0 }, .{ .duration = max, .due = 0, .weight = 0 } },
        // start(0) + duration(max) does not overflow; tardiness(max,0) * weight(2) does.
        .{ .{ .duration = max, .due = 0, .weight = 2 }, .{ .duration = 0, .due = 0, .weight = 0 } },
        // start(max) + duration(1) overflows immediately, before any multiply.
        .{ .{ .duration = max, .due = 0, .weight = 0 }, .{ .duration = 1, .due = 0, .weight = 0 } },
    };
    for (overflow_cases) |pair| {
        try writer.writeAll("[[");
        try printJob(writer, pair[0]);
        try writer.writeAll(",");
        try printJob(writer, pair[1]);
        try writer.writeAll("]]\n");
        n += 1;
    }

    while (n < N) : (n += 1) {
        const len = rng.intRangeAtMost(usize, 0, 15);
        try writer.writeAll("[[");
        for (0..len) |i| {
            if (i != 0) try writer.writeAll(",");
            try printJob(writer, .{ .duration = rng.int(u32), .due = rng.int(u32), .weight = rng.int(u8) });
        }
        try writer.writeAll("]]\n");
    }
}

/// classify(x: u8) -> u8. Edges: the switch's own boundaries (0, 1, 9, 10) plus 0/1/max-1/max.
fn genClassify(rng: std.Random) !void {
    const file = try openOut("classify");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for ([_]u8{ 0, 1, 9, 10, 254, 255 }) |x| {
        try writer.print("[{d}]\n", .{x});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.int(u8)});
    }
}
