//! Differential-test input generator (docs/generated-code.md names the 8 functions).
//! Run from the repo root: `zig run tests/diff/gen_inputs.zig`.
//!
//! Writes `tests/diff/basic/inputs/<fn>.jsonl`: one JSON array of args per line, N = 300 lines
//! per function. Each file starts with a fixed set of edge-value lines (0, 1, max, min for
//! signed, max-1, empty slice, 1-element slice, and — where an accumulator can overflow —
//! slices crafted to overflow it), then fills up to 300 with values from a seeded PRNG, so
//! the output is byte-identical across runs.
//!
//! None of the 8 functions take a 64-bit parameter, so every argument here fits in a plain
//! JSON number. `tests/diff/harness.zig` and `Diff.lean` write 64-bit *results* (`sum`,
//! `totalWeightedTardiness`) as quoted decimal strings instead, since those can exceed a
//! JS-safe integer; this file has nothing to quote, but follows the same width rule.
//!
//! Also writes tests/diff/{recursion,options,errors}/inputs/<fn>.jsonl, for the recursion,
//! options and errors examples (examples/recursion, examples/options, examples/errors). Same
//! JSONL style: a slice argument (`[]const u32` or `[]const u8`) is a JSON array of numbers,
//! never a JSON string. isEven/isOdd/fact each recurse n times; see max_recursion_n below for
//! why their inputs stay small. gcd's recursion is O(log(min(a,b))), so it takes any u32.

const std = @import("std");

const N = 300;
/// Fixed seed: reused across runs, and generator functions run in a fixed order below, so
/// output is deterministic.
const seed: u64 = 0xA17_1EA0_5EED_0001;

const Job = struct { duration: u32, due: u32, weight: u8 };

pub fn main() !void {
    try std.fs.cwd().makePath("tests/diff/basic/inputs");
    try std.fs.cwd().makePath("tests/diff/recursion/inputs");
    try std.fs.cwd().makePath("tests/diff/options/inputs");
    try std.fs.cwd().makePath("tests/diff/errors/inputs");

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

    try genGcd(rng);
    try genIsEven(rng);
    try genIsOdd(rng);
    try genFact(rng);

    try genFind(rng);
    try genFindOr(rng);
    try genFirstIndexPlusOne(rng);

    try genParseDigit(rng);
    try genSumDigits(rng);
    try genDigitOrZero(rng);
}

fn openOut(comptime name: []const u8) !std.fs.File {
    return std.fs.cwd().createFile("tests/diff/basic/inputs/" ++ name ++ ".jsonl", .{});
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

// --- examples/recursion, examples/options, examples/errors -----------------------------

fn openOutIn(comptime dir: []const u8, comptime name: []const u8) !std.fs.File {
    return std.fs.cwd().createFile(dir ++ "/" ++ name ++ ".jsonl", .{});
}

/// Writes `xs` as a JSON array of numbers, e.g. `[1,2,3]`. Works for any integer element type
/// (`u32` for the options examples, `u8` for the errors ones).
fn writeIntSlice(writer: anytype, comptime T: type, xs: []const T) !void {
    try writer.writeAll("[");
    for (xs, 0..) |v, i| {
        if (i != 0) try writer.writeAll(",");
        try writer.print("{d}", .{v});
    }
    try writer.writeAll("]");
}

/// isEven/isOdd/fact each recurse n times, with no tail-call elimination guaranteed on either
/// the Zig or the Lean side. Cap n here so neither stack overflows. gcd's recursion is
/// O(log(min(a,b))), so it needs no cap and uses the full u32 range instead.
const max_recursion_n: u32 = 1000;

/// gcd(a: u32, b: u32) -> u32. Edges: 4 x 4 over edgesU(u32), plus consecutive Fibonacci pairs
/// (Euclid's worst case: the most subtraction/mod steps for a given magnitude), then random
/// fill.
fn genGcd(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/recursion/inputs", "gcd");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesU(u32)) |a| {
        for (edgesU(u32)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    const fib_pairs = [_][2]u32{ .{ 1, 1 }, .{ 2, 3 }, .{ 13, 21 }, .{ 832040, 1346269 } };
    for (fib_pairs) |p| {
        try writer.print("[{d},{d}]\n", .{ p[0], p[1] });
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d},{d}]\n", .{ rng.int(u32), rng.int(u32) });
    }
}

/// isEven(n: u32) -> bool. n is capped at max_recursion_n (see doc comment above). Edges:
/// 0, 1, 2, max_recursion_n - 1, max_recursion_n, then random fill in [0, max_recursion_n].
fn genIsEven(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/recursion/inputs", "isEven");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for ([_]u32{ 0, 1, 2, max_recursion_n - 1, max_recursion_n }) |v| {
        try writer.print("[{d}]\n", .{v});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.intRangeAtMost(u32, 0, max_recursion_n)});
    }
}

/// isOdd(n: u32) -> bool. Same shape as genIsEven.
fn genIsOdd(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/recursion/inputs", "isOdd");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for ([_]u32{ 0, 1, 2, max_recursion_n - 1, max_recursion_n }) |v| {
        try writer.print("[{d}]\n", .{v});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.intRangeAtMost(u32, 0, max_recursion_n)});
    }
}

/// fact(n: u32) -> u32. n is capped at max_recursion_n. 12! < 2^32 <= 13!, so the checked
/// multiply overflows (panics) at n=13 and every n above it. Edges: the overflow boundary
/// (11, 12, 13, 14, 20), 0, 1, max_recursion_n - 1, max_recursion_n, then random fill.
fn genFact(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/recursion/inputs", "fact");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for ([_]u32{ 0, 1, 2, 11, 12, 13, 14, 20, max_recursion_n - 1, max_recursion_n }) |v| {
        try writer.print("[{d}]\n", .{v});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.intRangeAtMost(u32, 0, max_recursion_n)});
    }
}

/// (xs, x) edge cases shared by find/findOr/firstIndexPlusOne — they take the same signature.
/// Empty slice; 1-element slice (present/absent); x at the first/middle/last position of a
/// longer slice; x absent from a longer slice; a duplicate (first index must win). Returns the
/// number of lines written.
fn writeOptionsEdges(writer: anytype) !usize {
    const long = [_]u32{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19 };
    var n: usize = 0;

    try writer.writeAll("[[],0]\n");
    n += 1;
    try writer.print("[[],{d}]\n", .{std.math.maxInt(u32)});
    n += 1;
    try writer.writeAll("[[0],0]\n");
    n += 1;
    try writer.writeAll("[[0],1]\n");
    n += 1;
    try writer.print("[[{0d}],{0d}]\n", .{std.math.maxInt(u32)});
    n += 1;
    try writer.writeAll("[[1,2,3],1]\n"); // present, first
    n += 1;
    try writer.writeAll("[[1,2,3],3]\n"); // present, last
    n += 1;
    try writer.writeAll("[[1,2,3],2]\n"); // present, middle
    n += 1;
    try writer.writeAll("[[1,2,3],4]\n"); // absent
    n += 1;
    try writer.writeAll("[[2,2,2],2]\n"); // duplicates: first index wins
    n += 1;
    try writer.writeAll("[");
    try writeIntSlice(writer, u32, &long);
    try writer.writeAll(",0]\n"); // present, first of a long slice
    n += 1;
    try writer.writeAll("[");
    try writeIntSlice(writer, u32, &long);
    try writer.writeAll(",19]\n"); // present, last of a long slice
    n += 1;
    try writer.writeAll("[");
    try writeIntSlice(writer, u32, &long);
    try writer.writeAll(",20]\n"); // absent from a long slice
    n += 1;
    return n;
}

/// Random (xs, x) fill for find/findOr/firstIndexPlusOne: narrow element/x range (0-8) so hits
/// and misses both stay frequent.
fn writeOptionsRandom(writer: anytype, rng: std.Random, n_start: usize) !void {
    var n = n_start;
    while (n < N) : (n += 1) {
        const len = rng.intRangeAtMost(usize, 0, 12);
        var buf: [12]u32 = undefined;
        for (0..len) |i| buf[i] = rng.intRangeAtMost(u32, 0, 8);
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, buf[0..len]);
        try writer.print(",{d}]\n", .{rng.intRangeAtMost(u32, 0, 8)});
    }
}

/// find(xs: []const u32, x: u32) -> ?usize.
fn genFind(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/options/inputs", "find");
    defer file.close();
    const writer = file.deprecatedWriter();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// findOr(xs: []const u32, x: u32) -> usize.
fn genFindOr(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/options/inputs", "findOr");
    defer file.close();
    const writer = file.deprecatedWriter();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// firstIndexPlusOne(xs: []const u32, x: u32) -> usize. Panics (`.?` on null) on the absent
/// cases in writeOptionsEdges/writeOptionsRandom.
fn genFirstIndexPlusOne(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/options/inputs", "firstIndexPlusOne");
    defer file.close();
    const writer = file.deprecatedWriter();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// The ASCII digit-range boundary bytes ('/' = '0' - 1, ':' = '9' + 1) plus 0, 1, 254, 255.
const digit_byte_edges = [_]u8{ 0, 1, '/', '0', '9', ':', 254, 255 };

/// parseDigit(c: u8) -> error{NotDigit}!u8. Edges: digit_byte_edges, then random fill over the
/// full byte range.
fn genParseDigit(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/errors/inputs", "parseDigit");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (digit_byte_edges) |c| {
        try writer.print("[{d}]\n", .{c});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.int(u8)});
    }
}

/// digitOrZero(c: u8) -> u8. Same edges as genParseDigit.
fn genDigitOrZero(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/errors/inputs", "digitOrZero");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (digit_byte_edges) |c| {
        try writer.print("[{d}]\n", .{c});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.int(u8)});
    }
}

/// sumDigits(s: []const u8) -> error{NotDigit}!u32. `s` is a JSON array of byte values (0-255),
/// the same convention as a `[]const u32` slice (writeIntSlice) — this sidesteps JSON string
/// escaping for the 0/255 edge bytes below. `total` (u32) cannot overflow here: max digit
/// value 9 would need about 4.8e8 bytes. Edges: empty slice; an all-digit string; a non-digit
/// at the first/middle/last byte; each boundary byte ('/', ':', 0, 255) spliced into a digit
/// string; then random fill (about 1 in 6 bytes a non-digit, so both success and failure stay
/// frequent).
fn genSumDigits(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/errors/inputs", "sumDigits");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    const fixed = [_][]const u8{
        &.{},
        &.{'0'},
        &.{'9'},
        "0123456789",
        &.{ 'a', '1', '2', '3' }, // non-digit first
        &.{ '1', '2', 'a', '4' }, // non-digit middle
        &.{ '1', '2', '3', 'a' }, // non-digit last
        &.{ '1', '/', '3' }, // '/' = '0' - 1
        &.{ '1', ':', '3' }, // ':' = '9' + 1
        &.{ '1', 0, '3' }, // NUL byte
        &.{ '1', 255, '3' }, // 0xFF byte
    };
    for (fixed) |s| {
        try writer.writeAll("[");
        try writeIntSlice(writer, u8, s);
        try writer.writeAll("]\n");
        n += 1;
    }
    while (n < N) : (n += 1) {
        const len = rng.intRangeAtMost(usize, 0, 10);
        var buf: [10]u8 = undefined;
        for (0..len) |i| {
            buf[i] = if (rng.intRangeAtMost(u8, 0, 5) == 0) 'x' else '0' + rng.intRangeAtMost(u8, 0, 9);
        }
        try writer.writeAll("[");
        try writeIntSlice(writer, u8, buf[0..len]);
        try writer.writeAll("]\n");
    }
}
