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
    try std.fs.cwd().makePath("tests/diff/floatops/inputs");
    try std.fs.cwd().makePath("tests/diff/floatconv/inputs");
    try std.fs.cwd().makePath("tests/diff/floats/inputs");

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
    try genParity(rng, "isEven");
    try genParity(rng, "isOdd");
    try genFact(rng);

    try genFind(rng);
    try genFindOr(rng);
    try genFirstIndexPlusOne(rng);

    try genDigitByte(rng, "parseDigit");
    try genSumDigits(rng);
    try genDigitByte(rng, "digitOrZero");

    // New float generators draw from the same shared `rng` stream. They run last, after every
    // existing call above, so the pre-existing examples' inputs stay byte-identical.
    try genFloatOp(rng, f16, "op16");
    try genFloatOp(rng, f32, "op32");
    try genFloatOp(rng, f64, "op64");
    try genFloatOp(rng, f80, "op80");
    try genFloatOp(rng, f128, "op128");
    try genCmp64(rng);
    try genDivExact64(rng);

    try genFloatConvF(rng, f64, "toI32", i32);
    try genFloatConvF(rng, f32, "toU64", u64);
    try genFloatConvF(rng, f32, "toByte", u8);
    try genFloatConvI(rng, i64, "fromI64");
    try genFloatConvI(rng, u128, "fromU128");
    try genFloatConvF(rng, f64, "f64ToF16", void);
    try genFloatConvF(rng, f16, "f16ToF128", void);
    try genFloatConvF(rng, f80, "f80ToF64", void);
    try genFloatConvF(rng, f32, "bits32", void);
    try genFloatConvI(rng, u64, "ofBits64");

    try genLerp(rng);
    try genClamp(rng);
    try genIsNan(rng);
    try genHypot2(rng);
    try genCelsius(rng);
    try genDot(rng);
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

/// isEven/isOdd(n: u32) -> bool. n is capped at max_recursion_n (see doc comment above). Edges:
/// 0, 1, 2, max_recursion_n - 1, max_recursion_n, then random fill in [0, max_recursion_n].
fn genParity(rng: std.Random, comptime name: []const u8) !void {
    const file = try openOutIn("tests/diff/recursion/inputs", name);
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

/// parseDigit(c: u8) -> error{NotDigit}!u8 and digitOrZero(c: u8) -> u8. Edges:
/// digit_byte_edges, then random fill over the full byte range.
fn genDigitByte(rng: std.Random, comptime name: []const u8) !void {
    const file = try openOutIn("tests/diff/errors/inputs", name);
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

// --- examples/floatops, floatconv, floats -----------------------------------------------
// docs/floats.md's diff protocol: a float is `"0x"` + lowercase hex bits, zero-padded to
// width/4 digits (parsed by tests/diff/common.zig's parseFloatHex); inputs are always hex,
// never "nan" (a NaN input is just its bit pattern). A slice of floats is a JSON array of
// float strings. A u64/u128 plain-int arg is a quoted decimal string, the same "wide" rule
// common.zig already applies to u64/usize results (a bare JSON number loses precision above
// 2^53, and u128 has no exact JSON number representation at all).

fn floatBits(comptime T: type) type {
    return std.meta.Int(.unsigned, @bitSizeOf(T));
}

fn toBits(comptime T: type, x: T) floatBits(T) {
    return @bitCast(x);
}

fn fromBits(comptime T: type, b: floatBits(T)) T {
    return @bitCast(b);
}

/// One ulp below `x` (toward zero, for the positive magnitudes edgesF uses this on).
fn ulpDown(comptime T: type, x: T) T {
    return fromBits(T, toBits(T, x) - 1);
}

/// One ulp above `x` (away from zero, for the positive magnitudes edgesF uses this on).
fn ulpUp(comptime T: type, x: T) T {
    return fromBits(T, toBits(T, x) + 1);
}

// f80's non-IEEE encodings (docs/floats.md): exponent/integer-bit/fraction combinations IEEE
// never produces, that the model still classifies as NaN. Same bit patterns as
// tests/floatprobe/probe.zig's probeF80.
fn f80Unnormal() f80 {
    return @bitCast(@as(u80, 0x0001_0000000000000001));
}
fn f80PseudoInf() f80 {
    return @bitCast(@as(u80, 0x7fff_0000000000000000));
}
fn f80PseudoNan() f80 {
    return @bitCast(@as(u80, 0x7fff_4000000000000000));
}
fn f80PseudoDenormal() f80 {
    return @bitCast(@as(u80, 0x0000_8000000000000000));
}

fn edgesFLen(comptime T: type) usize {
    return if (T == f80) 47 else 43;
}

/// Edge values shared by every float-taking generator below: signed zero/subnormal/normal
/// boundaries, small exact integers, the format's extremes, both infinities, a quiet and a
/// signaling NaN, five magnitudes with the adjacent bit pattern on each side, and
/// 255.5/256/-0.5/-1. The magnitudes are the integer-range bounds 2^31, 2^31-1, 2^32, 2^63,
/// 2^64; f16 cannot hold them (max 65504), so it takes 2^11 (its precision limit), 2^11-1, 2^12,
/// 2^14, 2^15. f80 adds its 4 invalid encodings above.
fn edgesF(comptime T: type) [edgesFLen(T)]T {
    const max_sub = fromBits(T, toBits(T, std.math.floatMin(T)) - 1);
    const small = T == f16;
    const b31: T = if (small) 2048.0 else 2147483648.0;
    const b31m1: T = if (small) 2047.0 else 2147483647.0;
    const b32: T = if (small) 4096.0 else 4294967296.0;
    const b63: T = if (small) 16384.0 else 9223372036854775808.0;
    const b64: T = if (small) 32768.0 else 18446744073709551616.0;
    const base = [_]T{
        0.0,                      -0.0,
        std.math.floatTrueMin(T), -std.math.floatTrueMin(T),
        max_sub,                  -max_sub,
        std.math.floatMin(T),     -std.math.floatMin(T),
        0.5,                      -0.5,
        1.0,                      -1.0,
        1.5,                      -1.5,
        2.5,                      -2.5,
        3.0,                      -3.0,
        std.math.floatMax(T),     -std.math.floatMax(T),
        std.math.inf(T),          -std.math.inf(T),
        std.math.nan(T),          std.math.snan(T),
        ulpDown(T, b31),          b31,                      ulpUp(T, b31),
        ulpDown(T, b31m1),        b31m1,                    ulpUp(T, b31m1),
        ulpDown(T, b32),          b32,                      ulpUp(T, b32),
        ulpDown(T, b63),          b63,                      ulpUp(T, b63),
        ulpDown(T, b64),          b64,                      ulpUp(T, b64),
        255.5,                    256.0,                    -0.5,          -1.0,
    };
    if (T != f80) return base;
    return base ++ [_]T{ f80Unnormal(), f80PseudoInf(), f80PseudoNan(), f80PseudoDenormal() };
}

/// Fully random bit pattern: any sign, magnitude, may land on inf/NaN/subnormal.
fn randFiniteBits(rng: std.Random, comptime T: type) T {
    return fromBits(T, rng.int(floatBits(T)));
}

/// A value with an unbiased exponent in roughly [-12, 12] and a random mantissa, sign per
/// `neg`. Keeps most of the random fill away from inf/NaN/subnormal, which the edge lines
/// above already cover on their own.
fn randExpValue(rng: std.Random, comptime T: type, neg: bool) T {
    const mant = 1.0 + rng.float(f64) * 0.999_999;
    const e: f64 = @floatFromInt(rng.intRangeAtMost(i32, -12, 12));
    var v: T = @floatCast(mant * std.math.pow(f64, 2.0, e));
    if (neg) v = -v;
    return v;
}

/// Writes `x`'s diff-protocol hex token (`"0x..."`, no enclosing array/brackets).
fn floatHexToken(writer: anytype, comptime T: type, x: T) !void {
    const width = @bitSizeOf(T);
    const digits = std.fmt.comptimePrint("{d}", .{width / 4});
    const bits: floatBits(T) = toBits(T, x);
    try writer.print("\"0x{x:0>" ++ digits ++ "}\"", .{bits});
}

fn writeFloatArgLine(writer: anytype, comptime T: type, x: T) !void {
    try writer.writeAll("[");
    try floatHexToken(writer, T, x);
    try writer.writeAll("]\n");
}

fn writeFloatPairLine(writer: anytype, comptime T: type, a: T, b: T) !void {
    try writer.writeAll("[");
    try floatHexToken(writer, T, a);
    try writer.writeAll(",");
    try floatHexToken(writer, T, b);
    try writer.writeAll("]\n");
}

fn writeFloatTripleLine(writer: anytype, comptime T: type, a: T, b: T, c: T) !void {
    try writer.writeAll("[");
    try floatHexToken(writer, T, a);
    try writer.writeAll(",");
    try floatHexToken(writer, T, b);
    try writer.writeAll(",");
    try floatHexToken(writer, T, c);
    try writer.writeAll("]\n");
}

fn writeIntArgLine(writer: anytype, comptime T: type, v: T, wide: bool) !void {
    if (wide) {
        try writer.print("[\"{d}\"]\n", .{v});
    } else {
        try writer.print("[{d}]\n", .{v});
    }
}

fn writeFloatOpLine(writer: anytype, comptime T: type, sel: u8, a: T, b: T, c: T) !void {
    try writer.print("[{d},", .{sel});
    try floatHexToken(writer, T, a);
    try writer.writeAll(",");
    try floatHexToken(writer, T, b);
    try writer.writeAll(",");
    try floatHexToken(writer, T, c);
    try writer.writeAll("]\n");
}

/// op16/op32/op64/op80/op128(sel, a, b, c): 300 lines per sel (0..25), 7,800 lines total. Per
/// sel: 150 lines are the first 150 of (edgesF(T) x edgesF(T)) in row-major order; the
/// remaining 150 split into 75 fully-random bit patterns and 75 values with a controlled
/// exponent — for sel in {5,6,7,8} (divTrunc/divFloor/rem/mod), the controlled-exponent half
/// cycles through all 4 sign combinations of (a, b), since those ops are sign-sensitive.
/// `c` (sel 4's mulAdd addend) draws from the edge/random pools alongside `a`/`b`; every other
/// sel ignores it.
fn genFloatOp(rng: std.Random, comptime T: type, comptime name: []const u8) !void {
    const file = try openOutIn("tests/diff/floatops/inputs", name);
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(T);
    var sel: u16 = 0;
    while (sel <= 25) : (sel += 1) {
        const s: u8 = @intCast(sel);
        const sign_sensitive = s == 5 or s == 6 or s == 7 or s == 8;
        var n: usize = 0;

        edge_loop: for (edges, 0..) |a, ei| {
            for (edges, 0..) |b, ej| {
                if (n >= 150) break :edge_loop;
                const c = if (s == 4) edges[(ei + ej) % edges.len] else @as(T, 0);
                try writeFloatOpLine(writer, T, s, a, b, c);
                n += 1;
            }
        }

        while (n < N) : (n += 1) {
            var a: T = undefined;
            var b: T = undefined;
            if (n < 225) {
                a = randFiniteBits(rng, T);
                b = randFiniteBits(rng, T);
            } else if (sign_sensitive) {
                const combo = (n - 225) % 4;
                a = randExpValue(rng, T, combo & 1 != 0);
                b = randExpValue(rng, T, combo & 2 != 0);
            } else {
                a = randExpValue(rng, T, rng.boolean());
                b = randExpValue(rng, T, rng.boolean());
            }
            const c = if (s == 4) randExpValue(rng, T, rng.boolean()) else @as(T, 0);
            try writeFloatOpLine(writer, T, s, a, b, c);
        }
    }
}

/// cmp64(a, b) -> u8 bitmask. 150 edge pairs (first 150 of edgesF(f64) x edgesF(f64)), then 150
/// random fill split the same random-bits/controlled-exponent way as genFloatOp, cycling all 4
/// sign combinations (comparisons are sign-sensitive by nature).
fn genCmp64(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floatops/inputs", "cmp64");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f64);
    var n: usize = 0;
    edge_loop: for (edges) |a| {
        for (edges) |b| {
            if (n >= 150) break :edge_loop;
            try writeFloatPairLine(writer, f64, a, b);
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        var a: f64 = undefined;
        var b: f64 = undefined;
        if (n < 225) {
            a = randFiniteBits(rng, f64);
            b = randFiniteBits(rng, f64);
        } else {
            const combo = (n - 225) % 4;
            a = randExpValue(rng, f64, combo & 1 != 0);
            b = randExpValue(rng, f64, combo & 2 != 0);
        }
        try writeFloatPairLine(writer, f64, a, b);
    }
}

/// divExact64(a, b) -> f64 (`@divExact`; ReleaseSafe panics `exactDivisionRemainder` unless
/// `a / b` is exact). Edges: 150 pairs from edgesF(f64). Random fill: half exact by
/// construction (`b` random, `a = b * k` for a small integer k, so the safety check passes),
/// half fully random (almost always inexact, so the panic path gets heavy coverage too).
fn genDivExact64(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floatops/inputs", "divExact64");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f64);
    var n: usize = 0;
    edge_loop: for (edges) |a| {
        for (edges) |b| {
            if (n >= 150) break :edge_loop;
            try writeFloatPairLine(writer, f64, a, b);
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        var a: f64 = undefined;
        var b: f64 = undefined;
        if (n % 2 == 0) {
            b = randExpValue(rng, f64, rng.boolean());
            const k: f64 = @floatFromInt(rng.intRangeAtMost(i32, -8, 8));
            a = b * k;
        } else {
            a = randFiniteBits(rng, f64);
            b = randFiniteBits(rng, f64);
        }
        try writeFloatPairLine(writer, f64, a, b);
    }
}

/// Float-argument floatconv functions (toI32, toU64, toByte, f64ToF16, f16ToF128, f80ToF64,
/// bits32): edgesF(FromT), then — where `Bias` is a real type — values around `Bias`'s integer
/// range (only where `@intFromFloat`'s safety check makes the boundary interesting; `void`
/// skips this for the 4 pure cast/bit-reinterpret targets), then random fill.
fn genFloatConvF(rng: std.Random, comptime FromT: type, comptime name: []const u8, comptime Bias: type) !void {
    const file = try openOutIn("tests/diff/floatconv/inputs", name);
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesF(FromT)) |x| {
        try writeFloatArgLine(writer, FromT, x);
        n += 1;
    }
    if (Bias != void) {
        const lo: f64 = @floatFromInt(std.math.minInt(Bias));
        const hi: f64 = @floatFromInt(std.math.maxInt(Bias));
        const around = [_]f64{ lo - 2, lo - 1, lo, lo + 1, hi - 1, hi, hi + 1, hi + 2, (lo + hi) / 2 };
        for (around) |v| {
            const x: FromT = @floatCast(v);
            try writeFloatArgLine(writer, FromT, x);
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        const x: FromT = if (n % 2 == 0) randFiniteBits(rng, FromT) else randExpValue(rng, FromT, rng.boolean());
        try writeFloatArgLine(writer, FromT, x);
    }
}

/// Int-argument floatconv functions (fromI64, fromU128, ofBits64): edges of FromT, then random
/// fill. See the section doc comment above for the wide (>= 64-bit) quoting rule.
fn genFloatConvI(rng: std.Random, comptime FromT: type, comptime name: []const u8) !void {
    const file = try openOutIn("tests/diff/floatconv/inputs", name);
    defer file.close();
    const writer = file.deprecatedWriter();

    const wide = @bitSizeOf(FromT) >= 64;
    var n: usize = 0;
    if (comptime @typeInfo(FromT).int.signedness == .unsigned) {
        for (edgesU(FromT)) |v| {
            try writeIntArgLine(writer, FromT, v, wide);
            n += 1;
        }
    } else {
        for (edgesI(FromT)) |v| {
            try writeIntArgLine(writer, FromT, v, wide);
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        try writeIntArgLine(writer, FromT, rng.int(FromT), wide);
    }
}

/// lerp(a,b,t: f64) -> f64. Edge coverage: 150 (a,b,t) triples built by cycling each argument
/// through edgesF(f64) at a different stride, so each argument alone visits its full edge set
/// repeatedly across decorrelated combinations. Then random fill.
fn genLerp(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "lerp");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f64);
    const e = edges.len;
    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const a = edges[n % e];
        const b = edges[(n / 3) % e];
        const t = edges[(n / 7) % e];
        try writeFloatTripleLine(writer, f64, a, b, t);
    }
    while (n < N) : (n += 1) {
        const a = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        const b = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        const t = randExpValue(rng, f64, rng.boolean());
        try writeFloatTripleLine(writer, f64, a, b, t);
    }
}

/// clamp(x,lo,hi: f32) -> f32. Same strided edge coverage as lerp, then random fill; about a
/// third of the random `lo`/`hi` pairs are swapped (lo > hi) so both clamp directions and the
/// already-in-range branch all get exercised.
fn genClamp(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "clamp");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f32);
    const e = edges.len;
    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const x = edges[n % e];
        const lo = edges[(n / 3) % e];
        const hi = edges[(n / 7) % e];
        try writeFloatTripleLine(writer, f32, x, lo, hi);
    }
    while (n < N) : (n += 1) {
        const x = randExpValue(rng, f32, rng.boolean());
        var lo = randExpValue(rng, f32, rng.boolean());
        var hi = randExpValue(rng, f32, rng.boolean());
        if (lo > hi) {
            const tmp = lo;
            lo = hi;
            hi = tmp;
        }
        try writeFloatTripleLine(writer, f32, x, lo, hi);
    }
}

/// isNan(x: f64) -> bool. edgesF(f64), then random fill.
fn genIsNan(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "isNan");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesF(f64)) |x| {
        try writeFloatArgLine(writer, f64, x);
        n += 1;
    }
    while (n < N) : (n += 1) {
        const x: f64 = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        try writeFloatArgLine(writer, f64, x);
    }
}

/// hypot2(a, b: f64) -> f64. 150 edge pairs (first 150 of edgesF(f64) x edgesF(f64)), then
/// random fill (`@sqrt` of a sum of squares: worth stressing both very large and very small
/// magnitudes, which the random-bits half already reaches).
fn genHypot2(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "hypot2");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f64);
    var n: usize = 0;
    edge_loop: for (edges) |a| {
        for (edges) |b| {
            if (n >= 150) break :edge_loop;
            try writeFloatPairLine(writer, f64, a, b);
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        const a = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        const b = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        try writeFloatPairLine(writer, f64, a, b);
    }
}

/// celsius(k: f32) -> ?f32. edgesF(f32), then random fill.
fn genCelsius(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "celsius");
    defer file.close();
    const writer = file.deprecatedWriter();

    var n: usize = 0;
    for (edgesF(f32)) |k| {
        try writeFloatArgLine(writer, f32, k);
        n += 1;
    }
    while (n < N) : (n += 1) {
        const k: f32 = if (n % 2 == 0) randFiniteBits(rng, f32) else randExpValue(rng, f32, rng.boolean());
        try writeFloatArgLine(writer, f32, k);
    }
}

/// Writes a length-`len` JSON array of float-hex tokens: `edges[(i + offset) % edges.len]`.
fn writeFloatHexSlice(writer: anytype, comptime T: type, edges: anytype, len: usize, offset: usize) !void {
    try writer.writeAll("[");
    for (0..len) |i| {
        if (i != 0) try writer.writeAll(",");
        try floatHexToken(writer, T, edges[(i + offset) % edges.len]);
    }
    try writer.writeAll("]");
}

fn writeRandomFloatSlice(writer: anytype, rng: std.Random, comptime T: type, len: usize) !void {
    try writer.writeAll("[");
    for (0..len) |i| {
        if (i != 0) try writer.writeAll(",");
        const x: T = if (i % 2 == 0) randFiniteBits(rng, T) else randExpValue(rng, T, rng.boolean());
        try floatHexToken(writer, T, x);
    }
    try writer.writeAll("]");
}

/// dot(xs, ys: []const f64) -> f64. Slice lengths cycle 0..8 (docs/floats.md: a slice is a JSON
/// array of float strings): each length gets a few edge-flavored (xs, ys) pairs, offset so xs
/// and ys differ; then random-length (0-8) random fill.
fn genDot(rng: std.Random) !void {
    const file = try openOutIn("tests/diff/floats/inputs", "dot");
    defer file.close();
    const writer = file.deprecatedWriter();

    const edges = edgesF(f64);
    var n: usize = 0;
    var len: usize = 0;
    while (len <= 8) : (len += 1) {
        var round: usize = 0;
        while (round < 4 and n < N) : (round += 1) {
            try writer.writeAll("[");
            try writeFloatHexSlice(writer, f64, edges, len, round);
            try writer.writeAll(",");
            try writeFloatHexSlice(writer, f64, edges, len, round + 1);
            try writer.writeAll("]\n");
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        const len2 = rng.intRangeAtMost(usize, 0, 8);
        try writer.writeAll("[");
        try writeRandomFloatSlice(writer, rng, f64, len2);
        try writer.writeAll(",");
        try writeRandomFloatSlice(writer, rng, f64, len2);
        try writer.writeAll("]\n");
    }
}
