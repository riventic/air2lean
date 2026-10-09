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
const compat = @import("compat.zig");

const N = 300;
/// Fixed seed: reused across runs, and generator functions run in a fixed order below, so
/// output is deterministic.
const seed: u64 = 0xA17_1EA0_5EED_0001;

const Job = struct { duration: u32, due: u32, weight: u8 };

pub fn main() !void {
    try compat.makePath("tests/diff/basic/inputs");
    try compat.makePath("tests/diff/recursion/inputs");
    try compat.makePath("tests/diff/options/inputs");
    try compat.makePath("tests/diff/errors/inputs");
    try compat.makePath("tests/diff/floatops/inputs");
    try compat.makePath("tests/diff/floatconv/inputs");
    try compat.makePath("tests/diff/floats/inputs");
    try compat.makePath("tests/diff/variants/inputs");
    try compat.makePath("tests/diff/pointers/inputs");
    try compat.makePath("tests/diff/slices/inputs");
    try compat.makePath("tests/diff/lists/inputs");
    try compat.makePath("tests/diff/vectors/inputs");

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

    // The variants generators run after every earlier one, so the earlier inputs stay the same.
    try genVariants(rng);

    // The pointers generators run after every earlier one, so the earlier inputs stay the same.
    try genPointers(rng);

    // The slices generators run after every earlier one, so the earlier inputs stay the same.
    try genSlices(rng);

    // The lists generators run last, so the earlier inputs stay the same.
    try genLists(rng);

    // The asm generators run after every earlier one, so the earlier inputs stay the same.
    try compat.makePath("tests/diff/asm/inputs");
    try genBswap32(rng);
    try genPopcnt64(rng);
    try genLzcnt64(rng);

    // The vectors generators run last, so every earlier input stays the same.
    try genFDot(rng);
    try genUDotWrap(rng);
    try genSatAdd(rng);
    try genMaxLane(rng);
    try genReverse(rng);
    try genCheckedAdd(rng);

    // The threads generators run last, so the earlier inputs stay the same.
    try compat.makePath("tests/diff/threads/inputs");
    try genThreads(rng);

    // The vector coverage generators run last, so the earlier inputs stay the same.
    try genVectorCoverage(rng);
    // The layout generators run last, so every earlier input stays the same.
    try compat.makePath("tests/diff/layout/inputs");
    try genLayout(rng);
    // The vector op generators run last, so every earlier input stays the same.
    try genVectorOps(rng);
    try genSentinelArr(rng);
    try genDupeZ(rng);
    try genCtl();
    try genVecMem(rng);
    try genDivmod(rng);
    try genClaim();
    try genAtomics();
    try genSync();
    try genNoArgs("tests/diff/threadsync/inputs", .{ "mutexCounter", "handoff", "waitGroup" });
    try genNoArgs("tests/diff/iogroup/inputs", .{ "groupCounter", "groupConcurrent" });
    // The fitness generator runs last, so every earlier input stays the same.
    try genFitness(rng);
}

fn openOut(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/basic/inputs/" ++ name ++ ".jsonl");
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
    var file = try openOut("scale");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("clampAdd");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("absDiff");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("tardiness");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("weightedTardiness");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("sum");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("totalWeightedTardiness");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOut("classify");
    defer file.close();
    const writer = file.writer();

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

fn openOutIn(comptime dir: []const u8, comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open(dir ++ "/" ++ name ++ ".jsonl");
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
    var file = try openOutIn("tests/diff/recursion/inputs", "gcd");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/recursion/inputs", name);
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/recursion/inputs", "fact");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/options/inputs", "find");
    defer file.close();
    const writer = file.writer();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// findOr(xs: []const u32, x: u32) -> usize.
fn genFindOr(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/options/inputs", "findOr");
    defer file.close();
    const writer = file.writer();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// firstIndexPlusOne(xs: []const u32, x: u32) -> usize. Panics (`.?` on null) on the absent
/// cases in writeOptionsEdges/writeOptionsRandom.
fn genFirstIndexPlusOne(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/options/inputs", "firstIndexPlusOne");
    defer file.close();
    const writer = file.writer();
    const n = try writeOptionsEdges(writer);
    try writeOptionsRandom(writer, rng, n);
}

/// The ASCII digit-range boundary bytes ('/' = '0' - 1, ':' = '9' + 1) plus 0, 1, 254, 255.
const digit_byte_edges = [_]u8{ 0, 1, '/', '0', '9', ':', 254, 255 };

/// parseDigit(c: u8) -> error{NotDigit}!u8 and digitOrZero(c: u8) -> u8. Edges:
/// digit_byte_edges, then random fill over the full byte range.
fn genDigitByte(rng: std.Random, comptime name: []const u8) !void {
    var file = try openOutIn("tests/diff/errors/inputs", name);
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/errors/inputs", "sumDigits");
    defer file.close();
    const writer = file.writer();

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
    const bits = toBits(T, x);
    if (T == f80 and @as(u64, @truncate(bits)) == 0x8000_0000_0000_0000) {
        // x87 stores the integer bit explicitly: crossing an exponent boundary must restore
        // it for the previous normal, or clear it at the normal/subnormal boundary.
        const exponent = bits >> 64;
        return fromBits(T, bits - (if (exponent == 1) @as(u80, 1) << 64 else @as(u80, 1) << 63) - 1);
    }
    return fromBits(T, bits - 1);
}

/// One ulp above `x` (away from zero, for the positive magnitudes edgesF uses this on).
fn ulpUp(comptime T: type, x: T) T {
    const bits = toBits(T, x);
    if (T == f80 and bits == 0x7fff_ffff_ffff_ffff) {
        return fromBits(T, bits + (@as(u80, 1) << 64) + 1);
    }
    if (T == f80 and @as(u64, @truncate(bits)) == std.math.maxInt(u64)) {
        return fromBits(T, bits + (@as(u80, 1) << 63) + 1);
    }
    return fromBits(T, bits + 1);
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
    const max_sub = ulpDown(T, std.math.floatMin(T));
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
        ulpDown(T, b31),          b31,
        ulpUp(T, b31),            ulpDown(T, b31m1),
        b31m1,                    ulpUp(T, b31m1),
        ulpDown(T, b32),          b32,
        ulpUp(T, b32),            ulpDown(T, b63),
        b63,                      ulpUp(T, b63),
        ulpDown(T, b64),          b64,
        ulpUp(T, b64),            255.5,
        256.0,                    -0.5,
        -1.0,
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

/// Deterministic float edge pairs: every edge appears on the left against 1, every edge
/// appears on the right against 1, then diagonal pairs and signed-zero/infinity corners.
/// The 150-row budget holds all three passes and corners for every format (at most 47 edges).
fn floatEdgePair(comptime T: type, n: usize) struct { a: T, b: T, c: T } {
    const edges = edgesF(T);
    const one = 10; // edgesF's exact 1.0, an ordinary operand for every format.
    const corners = [_][2]usize{
        .{ 0, 1 }, .{ 1, 0 }, // opposite signed zeros
        .{ 20, 21 }, .{ 21, 20 }, // opposite infinities
        .{ 20, 0 }, .{ 0, 20 }, .{ 21, 1 }, .{ 1, 21 }, // infinity/zero
        .{ 22, 23 }, // quiet/signaling NaNs
    };
    const diagonal = n >= 2 * edges.len and n < 3 * edges.len;
    const corner = corners[(n -| 3 * edges.len) % corners.len];
    const ai = if (n < edges.len) n else if (n < 2 * edges.len) one else if (diagonal) n - 2 * edges.len else corner[0];
    const bi = if (n < edges.len) one else if (n < 2 * edges.len) n - edges.len else if (diagonal) ai else corner[1];
    return .{ .a = edges[ai], .b = edges[bi], .c = edges[(ai + bi) % edges.len] };
}

/// op16/op32/op64/op80/op128(sel, a, b, c): 300 lines per sel (0..25), 7,800 lines total. Per
/// sel: 150 deterministic edge pairs with complete lhs/rhs coverage; the remaining 150 split
/// into 75 fully-random bit patterns and 75 controlled-exponent values. For sel in {5,6,7,8}
/// (divTrunc/divFloor/rem/mod), the controlled half cycles all 4 sign combinations.
/// `c` (sel 4's mulAdd addend) draws from the edge/random pools; other selectors ignore it.
fn genFloatOp(rng: std.Random, comptime T: type, comptime name: []const u8) !void {
    var file = try openOutIn("tests/diff/floatops/inputs", name);
    defer file.close();
    const writer = file.writer();

    var sel: u16 = 0;
    while (sel <= 25) : (sel += 1) {
        const s: u8 = @intCast(sel);
        const sign_sensitive = s == 5 or s == 6 or s == 7 or s == 8;
        var n: usize = 0;

        while (n < 150) : (n += 1) {
            const pair = floatEdgePair(T, n);
            const c = if (s == 4) pair.c else @as(T, 0);
            try writeFloatOpLine(writer, T, s, pair.a, pair.b, c);
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
    try writeTieRows(writer, T);
}

/// Exact round-half-even ties, appended after the 7,800 rows (no random draw, so every other
/// generated file is unchanged): with `p` the format's precision, `1 + 2^-p` lies halfway
/// between 1 and its successor, so ties-to-even gives 1 (an even quotient) and
/// ties-away-from-zero (scripts/mutate.sh mutation (d)) the successor. Random operands and the
/// edge pairs never hit such a tie. The rows cover both operand orders, a negative sum, a
/// subtraction, and `1 + 3*2^-p` (rounds up to an even successor under both rules).
fn writeTieRows(writer: anytype, comptime T: type) !void {
    const p: i32 = std.math.floatFractionalBits(T) + 1;
    const half_ulp = std.math.ldexp(@as(T, 1), -p);
    const one: T = 1;
    const odd = one + 2 * half_ulp;
    try writeFloatOpLine(writer, T, 0, one, half_ulp, 0); // 1 + 2^-p
    try writeFloatOpLine(writer, T, 0, half_ulp, one, 0);
    try writeFloatOpLine(writer, T, 0, -one, -half_ulp, 0);
    try writeFloatOpLine(writer, T, 1, one, -half_ulp, 0); // 1 - (-2^-p)
    try writeFloatOpLine(writer, T, 0, odd, half_ulp, 0); // odd quotient: rounds up either way
}

/// cmp64(a, b) -> u8 bitmask. 150 edge pairs with full lhs/rhs coverage, then 150
/// random fill split the same random-bits/controlled-exponent way as genFloatOp, cycling all 4
/// sign combinations (comparisons are sign-sensitive by nature).
fn genCmp64(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/floatops/inputs", "cmp64");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const pair = floatEdgePair(f64, n);
        try writeFloatPairLine(writer, f64, pair.a, pair.b);
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
/// `a / b` is exact). Edges: 150 pairs with full lhs/rhs coverage. Random fill: half exact by
/// construction (`b` random, `a = b * k` for a small integer k, so the safety check passes),
/// half fully random (almost always inexact, so the panic path gets heavy coverage too).
fn genDivExact64(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/floatops/inputs", "divExact64");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const pair = floatEdgePair(f64, n);
        try writeFloatPairLine(writer, f64, pair.a, pair.b);
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
    var file = try openOutIn("tests/diff/floatconv/inputs", name);
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/floatconv/inputs", name);
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/floats/inputs", "lerp");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/floats/inputs", "clamp");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/floats/inputs", "isNan");
    defer file.close();
    const writer = file.writer();

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

/// hypot2(a, b: f64) -> f64. 150 edge pairs with full lhs/rhs coverage, then
/// random fill (`@sqrt` of a sum of squares: worth stressing both very large and very small
/// magnitudes, which the random-bits half already reaches).
fn genHypot2(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/floats/inputs", "hypot2");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const pair = floatEdgePair(f64, n);
        try writeFloatPairLine(writer, f64, pair.a, pair.b);
    }
    while (n < N) : (n += 1) {
        const a = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        const b = if (n % 2 == 0) randFiniteBits(rng, f64) else randExpValue(rng, f64, rng.boolean());
        try writeFloatPairLine(writer, f64, a, b);
    }
}

/// celsius(k: f32) -> ?f32. edgesF(f32), then random fill.
fn genCelsius(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/floats/inputs", "celsius");
    defer file.close();
    const writer = file.writer();

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
    var file = try openOutIn("tests/diff/floats/inputs", "dot");
    defer file.close();
    const writer = file.writer();

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

/// fitness(xs, ws: []const f64, target, penalty: f64) -> f64. Like genDot: slice lengths cycle
/// 0..8 with edge-flavored (xs, ws) pairs, target and penalty also from the edges; then
/// random-length (0-8) random fill.
fn genFitness(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/floats/inputs", "fitness");
    defer file.close();
    const writer = file.writer();

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
            try writer.writeAll(",");
            try floatHexToken(writer, f64, edges[(n * 7) % edges.len]);
            try writer.writeAll(",");
            try floatHexToken(writer, f64, edges[(n * 11 + 3) % edges.len]);
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
        try writer.writeAll(",");
        try floatHexToken(writer, f64, randExpValue(rng, f64, rng.boolean()));
        try writer.writeAll(",");
        try floatHexToken(writer, f64, randExpValue(rng, f64, false));
        try writer.writeAll("]\n");
    }
}

// ---- variants (examples/variants/variants.zig) ----
//
// An enum argument is its tag value (a JSON number). A `Shape` is an object with its active
// field: `{"circle":r}`, `{"rect":{"w":w,"h":h}}`, `{"square":a}`, `{"empty":null}`.

fn openVariants(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/variants/inputs/" ++ name ++ ".jsonl");
}

const shape_sizes = [_]u32{ 0, 1, 2, 65535, 65536, std.math.maxInt(u32) - 1, std.math.maxInt(u32) };

fn randSize(rng: std.Random) u32 {
    // Half small (no overflow in area/scale), half any u32.
    return if (rng.boolean()) rng.uintLessThan(u32, 100_000) else rng.int(u32);
}

fn writeShape(writer: anytype, kind: u2, a: u32, b: u32) !void {
    switch (kind) {
        0 => try writer.print("{{\"circle\":{d}}}", .{a}),
        1 => try writer.print("{{\"rect\":{{\"w\":{d},\"h\":{d}}}}}", .{ a, b }),
        2 => try writer.print("{{\"square\":{d}}}", .{a}),
        3 => try writer.writeAll("{\"empty\":null}"),
    }
}

fn writeRandShape(writer: anytype, rng: std.Random) !void {
    try writeShape(writer, rng.int(u2), randSize(rng), randSize(rng));
}

/// Every shape kind with the edge sizes (every pair for `rect`), then random shapes. `with_k`:
/// a second `u32` argument (an edge, or a random one).
fn genShapeFn(rng: std.Random, comptime name: []const u8, comptime with_k: bool) !void {
    var file = try openVariants(name);
    defer file.close();
    const writer = file.writer();
    var n: usize = 0;
    for (0..4) |kind| {
        for (shape_sizes) |a| {
            for (shape_sizes) |b| {
                if (kind != 1 and b != 0) continue;
                try writer.writeAll("[");
                try writeShape(writer, @intCast(kind), a, b);
                if (with_k) try writer.print(",{d}", .{shape_sizes[(n / 3) % shape_sizes.len]});
                try writer.writeAll("]\n");
                n += 1;
            }
        }
    }
    while (n < N) : (n += 1) {
        try writer.writeAll("[");
        try writeRandShape(writer, rng);
        if (with_k) try writer.print(",{d}", .{if (rng.boolean()) rng.uintLessThan(u32, 1000) else rng.int(u32)});
        try writer.writeAll("]\n");
    }
}

fn genVariants(rng: std.Random) !void {
    // next(l: Light), prioValue/isUrgent(p: Prio): every value.
    {
        var file = try openVariants("next");
        defer file.close();
        const writer = file.writer();
        for (0..3) |l| try writer.print("[{d}]\n", .{l});
    }
    inline for (.{ "prioValue", "isUrgent" }) |name| {
        var file = try openVariants(name);
        defer file.close();
        const writer = file.writer();
        for ([_]i8{ -1, 0, 5 }) |p| try writer.print("[{d}]\n", .{p});
    }
    // lightOf/codeOf/severity(x: u8): every u8.
    inline for (.{ "lightOf", "codeOf", "severity" }) |name| {
        var file = try openVariants(name);
        defer file.close();
        const writer = file.writer();
        for (0..256) |x| try writer.print("[{d}]\n", .{x});
    }
    // advance(l: Light, n: u32): small step counts, then random ones below 3000.
    {
        var file = try openVariants("advance");
        defer file.close();
        const writer = file.writer();
        var n: usize = 0;
        for (0..3) |l| {
            for ([_]u32{ 0, 1, 2, 3, 4, 5, 6, 7 }) |k| {
                try writer.print("[{d},{d}]\n", .{ l, k });
                n += 1;
            }
        }
        while (n < N) : (n += 1) try writer.print("[{d},{d}]\n", .{ rng.uintLessThan(u8, 3), rng.uintLessThan(u32, 3000) });
    }
    try genShapeFn(rng, "area", false);
    try genShapeFn(rng, "scale", true);
    try genShapeFn(rng, "radius", false);
    try genShapeFn(rng, "isRound", false);
    // totalArea(shapes: []const Shape): empty, one of each kind, an overflowing sum, random.
    {
        var file = try openVariants("totalArea");
        defer file.close();
        const writer = file.writer();
        try writer.writeAll("[[]]\n");
        var n: usize = 1;
        for (0..4) |kind| {
            try writer.writeAll("[[");
            try writeShape(writer, @intCast(kind), 7, 9);
            try writer.writeAll("]]\n");
            n += 1;
        }
        // Two squares of side 2^32-1: each area fits in u64, the sum does not.
        try writer.writeAll("[[");
        try writeShape(writer, 2, std.math.maxInt(u32), 0);
        try writer.writeAll(",");
        try writeShape(writer, 2, std.math.maxInt(u32), 0);
        try writer.writeAll("]]\n");
        n += 1;
        while (n < N) : (n += 1) {
            const len = rng.uintLessThan(usize, 8);
            try writer.writeAll("[[");
            for (0..len) |i| {
                if (i > 0) try writer.writeAll(",");
                try writeRandShape(writer, rng);
            }
            try writer.writeAll("]]\n");
        }
    }
}

// -- pointers (examples/pointers) ----------------------------------------------------------
//
// An input line of a function that uses memory is `{"bufs":[[<byte>,…],…],"args":[…]}`, and a
// pointer argument is `{"buf":i,"off":o}` into the buffers (docs/generated-code.md
// §Differential test). Every offset is a multiple of the pointee's alignment: the harness makes
// each buffer 16-byte aligned, so the pointers are aligned too.

fn openPointers(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/pointers/inputs/" ++ name ++ ".jsonl");
}

/// Random buffer contents; `setU32` then writes chosen values.
const Bytes = struct {
    b: [32]u8,
    len: usize,

    fn random(rng: std.Random, len: usize) Bytes {
        var r: Bytes = .{ .b = undefined, .len = len };
        rng.bytes(r.b[0..len]);
        return r;
    }

    fn setU32(self: *Bytes, off: usize, v: u32) void {
        std.mem.writeInt(u32, self.b[off..][0..4], v, .little);
    }
};

fn writeBufs(writer: anytype, bufs: []const Bytes) !void {
    try writer.writeAll("{\"bufs\":[");
    for (bufs, 0..) |b, i| {
        if (i > 0) try writer.writeAll(",");
        try writer.writeAll("[");
        for (b.b[0..b.len], 0..) |x, k| {
            if (k > 0) try writer.writeAll(",");
            try writer.print("{d}", .{x});
        }
        try writer.writeAll("]");
    }
    try writer.writeAll("],\"args\":[");
}

fn writePtr(writer: anytype, buf: usize, off: usize) !void {
    try writer.print("{{\"buf\":{d},\"off\":{d}}}", .{ buf, off });
}

/// A u32 that is sometimes an edge value, so that `+=` can overflow.
fn edgyU32(rng: std.Random) u32 {
    return switch (rng.uintLessThan(u8, 4)) {
        0 => edgesU(u32)[rng.uintLessThan(usize, 4)],
        else => rng.int(u32),
    };
}

/// Two pointers to `u32` for `swap`/`same`/`maxPtr`: into two buffers, the same pointer, or
/// two offsets of one buffer (`kind` 0, 1, 2).
fn writeTwoPtrs(writer: anytype, rng: std.Random, kind: usize) !void {
    const a = 4 * rng.uintLessThan(usize, 2);
    const b = 4 * rng.uintLessThan(usize, 2);
    switch (kind) {
        0 => {
            try writeBufs(writer, &.{ Bytes.random(rng, 8), Bytes.random(rng, 8) });
            try writePtr(writer, 0, a);
            try writer.writeAll(",");
            try writePtr(writer, 1, b);
        },
        1 => {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, a);
            try writer.writeAll(",");
            try writePtr(writer, 0, a);
        },
        else => {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 0);
            try writer.writeAll(",");
            try writePtr(writer, 0, 4);
        },
    }
}

fn genPointers(rng: std.Random) !void {
    inline for (.{ "swap", "same" }) |name| {
        var file = try openPointers(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeTwoPtrs(writer, rng, i % 3);
            try writer.writeAll("]}\n");
        }
    }
    // maxPtr(a: ?*const u32, b: ?*const u32): each of a and b null or not.
    {
        var file = try openPointers("maxPtr");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            switch (i % 4) {
                0 => try writer.writeAll("{\"bufs\":[],\"args\":[null,null"),
                1, 2 => {
                    try writeBufs(writer, &.{Bytes.random(rng, 8)});
                    if (i % 4 == 1) try writer.writeAll("null,") else {}
                    try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
                    if (i % 4 == 2) try writer.writeAll(",null");
                },
                else => try writeTwoPtrs(writer, rng, (i / 4) % 3),
            }
            try writer.writeAll("]}\n");
        }
    }
    // delay(j: *Job, d: u32), dueOf(j: *Job): one of two jobs in a 24-byte buffer.
    inline for (.{ "delay", "dueOf" }) |name| {
        var file = try openPointers(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            var b = Bytes.random(rng, 24);
            const off: usize = 12 * rng.uintLessThan(usize, 2);
            b.setU32(off, edgyU32(rng));
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, off);
            if (comptime std.mem.eql(u8, name, "delay")) try writer.print(",{d}", .{edgyU32(rng)});
            try writer.writeAll("]}\n");
        }
    }
    // sumTo(n: u32): no buffers; small counts, then random ones below 2000.
    {
        var file = try openPointers("sumTo");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n: u32 = if (i < 8) @intCast(i) else rng.uintLessThan(u32, 2000);
            try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{n});
        }
    }
    // copyJob(dst: *Job, src: *const Job): two buffers, the same pointer, or the two jobs of
    // one 24-byte buffer.
    {
        var file = try openPointers("copyJob");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            switch (i % 3) {
                0 => {
                    try writeBufs(writer, &.{ Bytes.random(rng, 12), Bytes.random(rng, 12) });
                    try writePtr(writer, 0, 0);
                    try writer.writeAll(",");
                    try writePtr(writer, 1, 0);
                },
                1 => {
                    try writeBufs(writer, &.{Bytes.random(rng, 12)});
                    try writePtr(writer, 0, 0);
                    try writer.writeAll(",");
                    try writePtr(writer, 0, 0);
                },
                else => {
                    const d: usize = 12 * rng.uintLessThan(usize, 2);
                    try writeBufs(writer, &.{Bytes.random(rng, 24)});
                    try writePtr(writer, 0, d);
                    try writer.writeAll(",");
                    try writePtr(writer, 0, 12 - d);
                },
            }
            try writer.writeAll("]}\n");
        }
    }
    // bumpOpt(p: *?u32), setOpt(p: *?u32, x: ?u32): a `?u32` is 8 bytes, the flag (0 or 1) at
    // offset 4.
    // setOptJob(p: *?Job, d: u32): a `?Job` is 16 bytes, the flag at offset 12.
    {
        var file = try openPointers("setOptJob");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            var b = Bytes.random(rng, 16);
            b.b[12] = rng.uintLessThan(u8, 2);
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, 0);
            try writer.print(",{d}]}}\n", .{rng.int(u32)});
        }
    }
    // addDown(acc: *u64, n: u32): a small n; every second start value is close to the maximum,
    // so the sum can overflow.
    {
        var file = try openPointers("addDown");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            var b = Bytes.random(rng, 8);
            if (i % 2 == 0) @memset(b.b[2..8], 0xff);
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, 0);
            try writer.print(",{d}]}}\n", .{rng.uintLessThan(u32, 200)});
        }
    }
    inline for (.{ "bumpOpt", "setOpt" }) |name| {
        var file = try openPointers(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            var b = Bytes.random(rng, 16);
            const off: usize = 8 * rng.uintLessThan(usize, 2);
            b.setU32(off, edgyU32(rng));
            b.b[off + 4] = rng.uintLessThan(u8, 2);
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, off);
            if (comptime std.mem.eql(u8, name, "setOpt")) {
                if (rng.boolean()) try writer.writeAll(",null") else try writer.print(",{d}", .{rng.int(u32)});
            }
            try writer.writeAll("]}\n");
        }
    }
}

fn openSlices(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/slices/inputs/" ++ name ++ ".jsonl");
}

/// `{"bufs":[<bytes>],"args":[` with one buffer: `len` random bytes, each 0 with probability
/// 1/`zeros` (0: no forced zeros).
fn writeBuf(writer: anytype, rng: std.Random, len: usize, zeros: u8) !void {
    try writer.writeAll("{\"bufs\":[[");
    for (0..len) |k| {
        if (k > 0) try writer.writeAll(",");
        const x = if (zeros > 0 and rng.uintLessThan(u8, zeros) == 0) 0 else rng.int(u8);
        try writer.print("{d}", .{x});
    }
    try writer.writeAll("]],\"args\":[");
}

fn writeSlice(writer: anytype, buf: usize, off: usize, len: usize) !void {
    try writer.print("{{\"buf\":{d},\"off\":{d},\"len\":{d}}}", .{ buf, off, len });
}

/// A slice of items of `size` bytes in a random buffer of up to `max` items: an aligned start,
/// and a length up to the end (sometimes 0).
fn writeItemSlice(writer: anytype, rng: std.Random, size: usize, max: usize, zeros: u8) !void {
    const n = rng.uintAtMost(usize, max);
    try writeBuf(writer, rng, n * size, zeros);
    const a = rng.uintAtMost(usize, n);
    try writeSlice(writer, 0, a * size, rng.uintAtMost(usize, n - a));
}

fn genSlices(rng: std.Random) !void {
    // reverse, sumMid: `[]u32`. sumMid overflows on large items, and on an empty slice.
    inline for (.{ "reverse", "sumMid" }) |name| {
        var file = try openSlices(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeItemSlice(writer, rng, 4, 8, if (i % 2 == 0) 0 else 1);
            try writer.writeAll("]}\n");
        }
    }
    // fill(s: []u8, v), clear(s: []u16).
    {
        var file = try openSlices("fill");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeItemSlice(writer, rng, 1, 24, 0);
            try writer.print(",{d}]}}\n", .{rng.int(u8)});
        }
    }
    {
        var file = try openSlices("clear");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeItemSlice(writer, rng, 2, 12, 0);
            try writer.writeAll("]}\n");
        }
    }
    // copyWithin(s: []u32, dst, src, len): the whole buffer; out-of-range values panic.
    {
        var file = try openSlices("copyWithin");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n = rng.uintAtMost(usize, 8);
            try writeBuf(writer, rng, 4 * n, 0);
            try writeSlice(writer, 0, 0, n);
            if (i % 3 == 0) {
                try writer.print(",{d},{d},{d}]}}\n", .{
                    rng.uintAtMost(usize, n + 1), rng.uintAtMost(usize, n + 1), rng.uintAtMost(usize, n + 1),
                });
            } else {
                // In range: the two ranges overlap or not.
                const len = rng.uintAtMost(usize, n);
                try writer.print(",{d},{d},{d}]}}\n", .{
                    rng.uintAtMost(usize, n - len), rng.uintAtMost(usize, n - len), len,
                });
            }
        }
    }
    // copy(dst: []u8, src: []const u8): two parts of one buffer, which can overlap (a panic), and
    // lengths that can differ (a panic).
    {
        var file = try openSlices("copy");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeBuf(writer, rng, 24, 0);
            const len = rng.uintAtMost(usize, 12);
            const len2 = if (i % 5 == 0) rng.uintAtMost(usize, 12) else len;
            try writeSlice(writer, 0, rng.uintAtMost(usize, 24 - len), len);
            try writer.writeAll(",");
            try writeSlice(writer, 0, rng.uintAtMost(usize, 24 - len2), len2);
            try writer.writeAll("]}\n");
        }
    }
    // indexOfScalar(c), failName(n), colorName(c), factorial(n), localArr(i), bump().
    {
        var file = try openSlices("indexOfScalar");
        defer file.close();
        const writer = file.writer();
        const text = "hello, world";
        for (0..N) |i| {
            const c = if (i % 2 == 0) text[rng.uintLessThan(usize, text.len)] else rng.int(u8);
            try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{c});
        }
    }
    {
        var file = try openSlices("failName");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n = if (i % 2 == 0) 0 else rng.int(u8);
            try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{n});
        }
    }
    {
        var file = try openSlices("colorName");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{i % 3});
    }
    {
        var file = try openSlices("factorial");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{i % 10});
    }
    {
        var file = try openSlices("localArr");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const x = if (i % 4 == 0) edgesU(u32)[rng.uintLessThan(usize, 4)] else rng.int(u32);
            try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{x});
        }
    }
    {
        var file = try openSlices("bump");
        defer file.close();
        const writer = file.writer();
        for (0..3) |_| try writer.writeAll("{\"bufs\":[],\"args\":[]}\n");
    }
    // sumZ(p: [*:0]const u8): the last byte is 0, so the items end in the buffer.
    {
        var file = try openSlices("sumZ");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            const n = 1 + rng.uintLessThan(usize, 24);
            try writer.writeAll("{\"bufs\":[[");
            for (0..n) |k| {
                if (k > 0) try writer.writeAll(",");
                const x = if (k == n - 1 or rng.uintLessThan(u8, 6) == 0) 0 else rng.int(u8);
                try writer.print("{d}", .{x});
            }
            try writer.writeAll("]],\"args\":[");
            try writePtr(writer, 0, rng.uintLessThan(usize, n));
            try writer.writeAll("]}\n");
        }
    }
    // subZ(s: []const u8, a, b): the whole buffer; `a > b`, `b >= len` and `s[b] != 0` panic.
    {
        var file = try openSlices("subZ");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n = rng.uintAtMost(usize, 16);
            try writeBuf(writer, rng, n, 2);
            try writeSlice(writer, 0, 0, n);
            if (i % 2 == 0 and n > 0) {
                // `a <= b < len`: only `s[b] != 0` panics.
                const b = rng.uintLessThan(usize, n);
                try writer.print(",{d},{d}]}}\n", .{ rng.uintAtMost(usize, b), b });
            } else {
                try writer.print(",{d},{d}]}}\n", .{ rng.uintAtMost(usize, n + 1), rng.uintAtMost(usize, n + 1) });
            }
        }
    }
    // total(a: *const [3]u32), second and prevItem (two items), at(p, i): items in the buffer.
    {
        var file = try openSlices("total");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeBuf(writer, rng, 16, if (i % 2 == 0) 0 else 1);
            try writePtr(writer, 0, 4 * rng.uintAtMost(usize, 1));
            try writer.writeAll("]}\n");
        }
    }
    inline for (.{ "second", "prevItem" }) |name| {
        var file = try openSlices(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBuf(writer, rng, 16, 0);
            try writePtr(writer, 0, 4 * rng.uintAtMost(usize, 2));
            try writer.writeAll("]}\n");
        }
    }
    {
        var file = try openSlices("at");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            const n = 1 + rng.uintLessThan(usize, 6);
            try writeBuf(writer, rng, 4 * n, 0);
            const a = rng.uintLessThan(usize, n);
            try writePtr(writer, 0, 4 * a);
            try writer.print(",{d}]}}\n", .{rng.uintLessThan(usize, n - a)});
        }
    }
    // bumpAt(a: *[4]u8, i): `i = 4` panics.
    {
        var file = try openSlices("bumpAt");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBuf(writer, rng, 8, 0);
            try writePtr(writer, 0, 4 * rng.uintAtMost(usize, 1));
            try writer.print(",{d}]}}\n", .{rng.uintAtMost(usize, 4)});
        }
    }
    // lenOr(s: ?[]const u8): null, or a slice.
    {
        var file = try openSlices("lenOr");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            if (i % 3 == 0) {
                try writer.writeAll("{\"bufs\":[],\"args\":[null]}\n");
            } else {
                try writeItemSlice(writer, rng, 1, 16, 0);
                try writer.writeAll("]}\n");
            }
        }
    }
}

fn openLists(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/lists/inputs/" ++ name ++ ".jsonl");
}

/// The first argument of a function that takes an allocator: the allocation that fails, `null`
/// on every third line, else a number up to `max`.
fn writeFailAt(writer: anytype, rng: std.Random, i: usize, max: usize) !void {
    if (i % 3 == 0) try writer.writeAll("null") else try writer.print("{d}", .{rng.uintAtMost(usize, max)});
}

fn genLists(rng: std.Random) !void {
    // sumRange(n): small `n`, and sizes that cannot be allocated (more than 1 MiB, or an
    // overflow of `4 * n`). A JSON integer is at most `maxInt(i64)`.
    {
        var file = try openLists("sumRange");
        defer file.close();
        const writer = file.writer();
        const big = [_]usize{ (1 << 18) + 1, 1 << 62, std.math.maxInt(i64) };
        for (0..N) |i| {
            try writer.writeAll("{\"bufs\":[],\"args\":[");
            try writeFailAt(writer, rng, i, 1);
            const n = if (i % 10 == 9) big[rng.uintLessThan(usize, big.len)] else rng.uintAtMost(usize, 40);
            try writer.print(",{d}]}}\n", .{n});
        }
    }
    // dupe(xs: []const u8), evens(xs: []const u32), listSum(xs: []const u32): the allocation that
    // fails is one of the first ones.
    {
        var file = try openLists("dupe");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n = rng.uintAtMost(usize, 24);
            try writeBuf(writer, rng, n, 0);
            try writeFailAt(writer, rng, i, 1);
            try writer.writeAll(",");
            const a = rng.uintAtMost(usize, n);
            try writeSlice(writer, 0, a, rng.uintAtMost(usize, n - a));
            try writer.writeAll("]}\n");
        }
    }
    inline for (.{ .{ "evens", 40, 3 }, .{ "listSum", 10, 11 } }) |g| {
        var file = try openLists(g[0]);
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const n = rng.uintAtMost(usize, g[1]);
            try writeBuf(writer, rng, 4 * n, 0);
            try writeFailAt(writer, rng, i, g[2]);
            try writer.writeAll(",");
            try writeSlice(writer, 0, 0, n);
            try writer.writeAll("]}\n");
        }
    }
}

// --- examples/asm ------------------------------------------------------------------------

/// bswap32(x: u32) -> u32. Edges: 4 over edgesU(u32), then random fill.
fn genBswap32(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/asm/inputs", "bswap32");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    for (edgesU(u32)) |a| {
        try writer.print("[{d}]\n", .{a});
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writer.print("[{d}]\n", .{rng.int(u32)});
    }
}

/// popcnt64(x: u64) -> u64. u64 is wide (>= 64-bit): quoted decimal, same rule as the
/// int-argument floatconv functions above. Edges: 4 over edgesU(u64), plus every single-bit
/// value, then random fill.
fn genPopcnt64(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/asm/inputs", "popcnt64");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    for (edgesU(u64)) |a| {
        try writeIntArgLine(writer, u64, a, true);
        n += 1;
    }
    for (0..64) |bit| {
        try writeIntArgLine(writer, u64, @as(u64, 1) << @intCast(bit), true);
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writeIntArgLine(writer, u64, rng.int(u64), true);
    }
}

/// lzcnt64(x: u64) -> u64. Wide, same quoting as popcnt64 above. Edges: 4 over edgesU(u64), plus
/// every single-bit value (the boundary each leading-zero count changes at), then random fill.
fn genLzcnt64(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/asm/inputs", "lzcnt64");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    for (edgesU(u64)) |a| {
        try writeIntArgLine(writer, u64, a, true);
        n += 1;
    }
    for (0..64) |bit| {
        try writeIntArgLine(writer, u64, @as(u64, 1) << @intCast(bit), true);
        n += 1;
    }
    while (n < N) : (n += 1) {
        try writeIntArgLine(writer, u64, rng.int(u64), true);
    }
}

// --- examples/vectors --------------------------------------------------------------------

fn openOutV(comptime name: []const u8) !compat.OutFile {
    return openOutIn("tests/diff/vectors/inputs", name);
}

/// Writes `xs` as a JSON array of float-hex tokens, e.g. `["0x..","0x.."]` (any length).
fn writeFloatSlice(writer: anytype, comptime T: type, xs: []const T) !void {
    try writer.writeAll("[");
    for (xs, 0..) |x, i| {
        if (i != 0) try writer.writeAll(",");
        try floatHexToken(writer, T, x);
    }
    try writer.writeAll("]");
}

/// fDot(a, b: @Vector(4, f32)) -> f32. Edges: `edgesF(f32)` strided per lane (a different
/// prime stride per lane decorrelates the 4 positions across combos), then random fill.
fn genFDot(rng: std.Random) !void {
    var file = try openOutV("fDot");
    defer file.close();
    const writer = file.writer();

    const edges = edgesF(f32);
    const e = edges.len;
    var n: usize = 0;
    while (n < 150) : (n += 1) {
        const a = [4]f32{ edges[n % e], edges[(n / 3) % e], edges[(n / 7) % e], edges[(n / 11) % e] };
        const b = [4]f32{ edges[(n / 5) % e], edges[(n / 13) % e], edges[n % e], edges[(n / 17) % e] };
        try writer.writeAll("[");
        try writeFloatSlice(writer, f32, &a);
        try writer.writeAll(",");
        try writeFloatSlice(writer, f32, &b);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        var a: [4]f32 = undefined;
        var b: [4]f32 = undefined;
        for (0..4) |i| {
            a[i] = if (i % 2 == 0) randFiniteBits(rng, f32) else randExpValue(rng, f32, rng.boolean());
            b[i] = if (i % 2 == 0) randFiniteBits(rng, f32) else randExpValue(rng, f32, rng.boolean());
        }
        try writer.writeAll("[");
        try writeFloatSlice(writer, f32, &a);
        try writer.writeAll(",");
        try writeFloatSlice(writer, f32, &b);
        try writer.writeAll("]\n");
    }
}

/// uDotWrap(a, b: @Vector(4, u32)) -> u32 (wrapping mul, wrapping-add reduce; never panics).
/// Edges: `edgesU(u32)` strided per lane (values that push both the per-lane product and the
/// accumulated sum past u32's range), then random fill.
fn genUDotWrap(rng: std.Random) !void {
    var file = try openOutV("uDotWrap");
    defer file.close();
    const writer = file.writer();

    const edges = edgesU(u32);
    const e = edges.len;
    var n: usize = 0;
    while (n < 100) : (n += 1) {
        const a = [4]u32{ edges[n % e], edges[(n / 2) % e], edges[(n / 3) % e], edges[(n / 5) % e] };
        const b = [4]u32{ edges[(n / 7) % e], edges[n % e], edges[(n / 11) % e], edges[(n / 13) % e] };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        const a = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        const b = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
}

/// satAdd(a, b: @Vector(4, u32)) -> @Vector(4, u32) (saturating; never panics). Edges: for
/// each lane position, `a`'s lane is `maxInt` and `b`'s is a small positive value so only that
/// lane saturates (the others add ordinary small values); then `edgesU(u32)` strided combos;
/// then random fill.
fn genSatAdd(rng: std.Random) !void {
    var file = try openOutV("satAdd");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    for (0..4) |p| {
        var a = [4]u32{ 0, 1, 2, 3 };
        var b = [4]u32{ 4, 5, 6, 7 };
        a[p] = std.math.maxInt(u32);
        b[p] = 10;
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
        n += 1;
    }
    const edges = edgesU(u32);
    const e = edges.len;
    while (n < 100) : (n += 1) {
        const a = [4]u32{ edges[n % e], edges[(n / 2) % e], edges[(n / 3) % e], edges[(n / 5) % e] };
        const b = [4]u32{ edges[(n / 7) % e], edges[n % e], edges[(n / 11) % e], edges[(n / 13) % e] };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        const a = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        const b = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
}

/// maxLane(v: @Vector(4, i32)) -> i32 (`@reduce(.Max)`). Edges: for each lane position `p`, a
/// vector whose unique maximum (i32's `maxInt`) sits at `p` and the other 3 lanes hold
/// distinct smaller values — this is exactly what a fold that drops the last lane
/// (scripts/mutate.sh mutation (i)) gets wrong when `p = 3`. Then `edgesI(i32)` strided
/// combos, then random fill.
fn genMaxLane(rng: std.Random) !void {
    var file = try openOutV("maxLane");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    const fillers = [_]i32{ std.math.minInt(i32), -1, 0, std.math.minInt(i32) + 1 };
    for (0..4) |p| {
        var v = [4]i32{ fillers[0], fillers[1], fillers[2], fillers[3] };
        v[p] = std.math.maxInt(i32);
        try writer.writeAll("[");
        try writeIntSlice(writer, i32, &v);
        try writer.writeAll("]\n");
        n += 1;
    }
    const edges = edgesI(i32);
    const e = edges.len;
    while (n < 150) : (n += 1) {
        const v = [4]i32{ edges[n % e], edges[(n / 2) % e], edges[(n / 3) % e], edges[(n / 5) % e] };
        try writer.writeAll("[");
        try writeIntSlice(writer, i32, &v);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        const v = [4]i32{ rng.int(i32), rng.int(i32), rng.int(i32), rng.int(i32) };
        try writer.writeAll("[");
        try writeIntSlice(writer, i32, &v);
        try writer.writeAll("]\n");
    }
}

/// reverse(v: @Vector(4, u32)) -> @Vector(4, u32) (`@shuffle`; never panics). Edges:
/// `edgesU(u32)` strided combos, then random fill.
fn genReverse(rng: std.Random) !void {
    var file = try openOutV("reverse");
    defer file.close();
    const writer = file.writer();

    const edges = edgesU(u32);
    const e = edges.len;
    var n: usize = 0;
    while (n < 100) : (n += 1) {
        const v = [4]u32{ edges[n % e], edges[(n / 2) % e], edges[(n / 3) % e], edges[(n / 5) % e] };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &v);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        const v = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &v);
        try writer.writeAll("]\n");
    }
}

/// checkedAdd(a, b: @Vector(4, u32)) -> @Vector(4, u32) (checked; panics if any lane
/// overflows). Edges: no overflow; overflow in exactly one lane, for each of the 4 positions
/// (the shape the milestone brief asks for); overflow in every lane; then `edgesU(u32)`
/// strided combos and random fill (both draw from values spanning the full range, so some
/// combos overflow and some do not).
fn genCheckedAdd(rng: std.Random) !void {
    var file = try openOutV("checkedAdd");
    defer file.close();
    const writer = file.writer();

    var n: usize = 0;
    {
        const a = [4]u32{ 0, 1, 2, 3 };
        const b = [4]u32{ 4, 5, 6, 7 };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
        n += 1;
    }
    for (0..4) |p| {
        var a = [4]u32{ 0, 1, 2, 3 };
        var b = [4]u32{ 4, 5, 6, 7 };
        a[p] = std.math.maxInt(u32);
        b[p] = 1;
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
        n += 1;
    }
    {
        const a = [4]u32{ std.math.maxInt(u32), std.math.maxInt(u32), std.math.maxInt(u32), std.math.maxInt(u32) };
        const b = [4]u32{ 1, 1, 1, 1 };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
        n += 1;
    }
    const edges = edgesU(u32);
    const e = edges.len;
    while (n < 100) : (n += 1) {
        const a = [4]u32{ edges[n % e], edges[(n / 2) % e], edges[(n / 3) % e], edges[(n / 5) % e] };
        const b = [4]u32{ edges[(n / 7) % e], edges[n % e], edges[(n / 11) % e], edges[(n / 13) % e] };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
    while (n < N) : (n += 1) {
        const a = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        const b = [4]u32{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
        try writer.writeAll("[");
        try writeIntSlice(writer, u32, &a);
        try writer.writeAll(",");
        try writeIntSlice(writer, u32, &b);
        try writer.writeAll("]\n");
    }
}

// --- examples/threads --------------------------------------------------------------------

/// parallelCounter(itersPerThread: u32) -> u32. No pointer/allocator args: 4 threads share one
/// atomic counter, so the result is always `4 * itersPerThread`, regardless of interleaving.
/// itersPerThread stays small (0..64): each line spawns 4 real threads that loop that many
/// times, and the differential test runs every line.
fn genThreadsCounter(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/threads/inputs", "parallelCounter");
    defer file.close();
    const writer = file.writer();
    for ([_]u32{ 0, 1 }) |n| try writer.print("[{d}]\n", .{n});
    for (0..N - 2) |_| try writer.print("[{d}]\n", .{rng.uintAtMost(u32, 64)});
}

/// race(a: u32, b: u32) -> u32 and xchgRace(a: u32, b: u32) -> u32: both race two threads on
/// one shared location without an ordering between them (a plain write, an atomic swap). The
/// model gives `.illegal` for race (a data race) and `a` or `b` for xchgRace (by the schedule),
/// so the values only need to exercise the full u32 range.
fn genThreadsRace(rng: std.Random, comptime name: []const u8, comptime mirror_name: ?[]const u8) !void {
    var file = try openOutIn("tests/diff/threads/inputs", name);
    defer file.close();
    const writer = file.writer();
    var mirror: ?compat.OutFile = if (mirror_name) |destination|
        try openOutIn("tests/diff/threads/inputs", destination)
    else
        null;
    const mirror_writer = if (mirror) |*f| f.writer() else null;
    defer if (mirror) |*f| f.close();
    for (edgesU(u32)) |a| {
        for (edgesU(u32)) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            if (mirror_writer) |w| try w.print("[{d},{d}]\n", .{ a, b });
        }
    }
    for (0..N - edgesU(u32).len * edgesU(u32).len) |_| {
        const a = rng.int(u32);
        const b = rng.int(u32);
        try writer.print("[{d},{d}]\n", .{ a, b });
        if (mirror_writer) |w| try w.print("[{d},{d}]\n", .{ a, b });
    }
}

fn genThreads(rng: std.Random) !void {
    try genThreadsCounter(rng);
    try genThreadsRace(rng, "race", "disjoint");
    try genThreadsRace(rng, "xchgRace", null);
}

// --- examples/vectors: coverage of the other vector ops ------------------------------------

/// One `@Vector(4, u32)` of edge values (`edgesU`) for the first lines, then random. Line `n`
/// picks a different edge per lane.
fn vecU(rng: std.Random, n: usize) [4]u32 {
    const e = edgesU(u32);
    if (n < 64) return .{ e[n % 4], e[(n / 4) % 4], e[(n / 16) % 4], e[(n / 2) % 4] };
    // Small values in some lines, so And/Min see equal and near lanes.
    if (n % 3 == 0) return .{ rng.uintLessThan(u32, 8), rng.uintLessThan(u32, 8), rng.uintLessThan(u32, 8), rng.uintLessThan(u32, 8) };
    return .{ rng.int(u32), rng.int(u32), rng.int(u32), rng.int(u32) };
}

fn vecI(rng: std.Random, n: usize) [4]i32 {
    const e = edgesI(i32);
    if (n < 64) return .{ e[n % 7], e[(n / 7) % 7], e[(n / 3) % 7], e[(n / 5) % 7] };
    return .{ rng.int(i32), rng.int(i32), rng.int(i32), rng.int(i32) };
}

/// Float edges (NaN, +-0, +-inf, subnormals: `edgesF`) strided per lane, then random.
fn vecF(rng: std.Random, n: usize) [4]f32 {
    const e = edgesF(f32);
    const l = e.len;
    if (n < 150) return .{ e[n % l], e[(n / 3) % l], e[(n / 7) % l], e[(n / 11) % l] };
    var a: [4]f32 = undefined;
    for (0..4) |i| a[i] = if (i % 2 == 0) randFiniteBits(rng, f32) else randExpValue(rng, f32, rng.boolean());
    return a;
}

fn writeBoolSlice(writer: anytype, xs: []const bool) !void {
    try writer.writeAll("[");
    for (xs, 0..) |x, i| {
        if (i != 0) try writer.writeAll(",");
        try writer.writeAll(if (x) "true" else "false");
    }
    try writer.writeAll("]");
}

/// splatAdd, pick, interleave, andLanes, orLanes, xorLanes, minLane, uMinLane, fMin, fMax,
/// twiceInMem: N lines each.
fn genVectorCoverage(rng: std.Random) !void {
    {
        var file = try openOutV("splatAdd");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeIntSlice(w, u32, &vecU(rng, n));
            const s: u32 = if (n < 64) edgesU(u32)[n % 4] else rng.int(u32);
            try w.print(",{d}]\n", .{s});
        }
    }
    {
        var file = try openOutV("pick");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            // Lines 0..15: every mask.
            const bits: u4 = if (n < 16) @intCast(n) else rng.int(u4);
            var m: [4]bool = undefined;
            for (0..4) |i| m[i] = (bits >> @intCast(i)) & 1 == 1;
            try w.writeAll("[");
            try writeBoolSlice(w, &m);
            try w.writeAll(",");
            try writeIntSlice(w, u32, &vecU(rng, n));
            try w.writeAll(",");
            try writeIntSlice(w, u32, &vecU(rng, n + 7));
            try w.writeAll("]\n");
        }
    }
    {
        var file = try openOutV("interleave");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            // Distinct lanes in every line, so a lane taken from the wrong vector or index shows.
            const a = [4]u32{ @intCast(4 * n), @intCast(4 * n + 1), @intCast(4 * n + 2), @intCast(4 * n + 3) };
            const b = if (n < 100) [4]u32{ a[0] + 100000, a[1] + 100000, a[2] + 100000, a[3] + 100000 } else vecU(rng, n);
            try w.writeAll("[");
            try writeIntSlice(w, u32, &a);
            try w.writeAll(",");
            try writeIntSlice(w, u32, &b);
            try w.writeAll("]\n");
        }
    }
    inline for (.{ "andLanes", "orLanes", "xorLanes", "uMinLane", "twiceInMem" }) |name| {
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeIntSlice(w, u32, &vecU(rng, n));
            try w.writeAll("]\n");
        }
    }
    {
        var file = try openOutV("minLane");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeIntSlice(w, i32, &vecI(rng, n));
            try w.writeAll("]\n");
        }
    }
    inline for (.{ "fMin", "fMax" }) |name| {
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeFloatSlice(w, f32, &vecF(rng, n));
            try w.writeAll("]\n");
        }
    }
}

// -- layout (examples/layout) -------------------------------------------------------------
//
// Every function here uses memory: an input line is `{"bufs":[…],"args":[…]}` (same protocol
// as pointers, above). `ptrFromAddr`'s address argument has no buffer at all: it is a wide
// (quoted) usize, always crafted to panic (`castToNull`/`incorrectAlignment`) — a non-panicking
// `@ptrFromInt` needs a real allocation to read back, so it is tested instead through
// `ptrRoundTrip`, which round-trips a real buffer pointer.

fn openLayout(comptime name: []const u8) !compat.OutFile {
    return compat.OutFile.open("tests/diff/layout/inputs/" ++ name ++ ".jsonl");
}

fn genLayout(rng: std.Random) !void {
    // addrEq(a, b: *const u32): same pattern as pointers' `same` — two buffers, the same
    // pointer, or two offsets of one buffer.
    {
        var file = try openLayout("addrEq");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeTwoPtrs(writer, rng, i % 3);
            try writer.writeAll("]}\n");
        }
    }
    // ptrRoundTrip(p: *u32): one buffer, one aligned offset.
    {
        var file = try openLayout("ptrRoundTrip");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
            try writer.writeAll("]}\n");
        }
    }
    // ptrFromAddr(a: usize): no buffers; every address panics (0, or not a multiple of 4).
    {
        var file = try openLayout("ptrFromAddr");
        defer file.close();
        const writer = file.writer();
        const fixed = [_]u64{ 0, 1, 2, 3, 5, 6, 7, std.math.maxInt(u64), std.math.maxInt(u64) - 2 };
        var n: usize = 0;
        for (fixed) |a| {
            try writer.print("{{\"bufs\":[],\"args\":[\"{d}\"]}}\n", .{a});
            n += 1;
        }
        while (n < N) : (n += 1) {
            // Half null, half a random address whose low 2 bits are not both 0.
            const a: u64 = if (n % 2 == 0) 0 else blk: {
                var v = rng.int(u64);
                if (v % 4 == 0) v +%= 1;
                break :blk v;
            };
            try writer.print("{{\"bufs\":[],\"args\":[\"{d}\"]}}\n", .{a});
        }
    }
    // asConst/dropConst/asVolatile(p: *u32): one buffer, one aligned offset (same pattern as
    // pointers' `dueOf`, without the two-job choice).
    inline for (.{ "asConst", "dropConst", "asVolatile" }) |name| {
        var file = try openLayout(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
            try writer.writeAll("]}\n");
        }
    }
    // align4(p: *align(1) u32): one 8-byte buffer, an offset 0..4 — half aligned to 4
    // (succeeds), half not (panics `incorrectAlignment`).
    {
        var file = try openLayout("align4");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            const off: usize = if (i % 2 == 0) 4 * rng.uintLessThan(usize, 2) else 1 + rng.uintLessThan(usize, 3);
            try writePtr(writer, 0, off);
            try writer.writeAll("]}\n");
        }
    }
    // parentOfX/parentOfY(p: *u32): a 12-byte buffer (room for 3 u32 slots at 0, 4, 8).
    // parentOfX's offset can be any of the 3 (offset - 0 never underflows); parentOfY's must be
    // 4 or 8 (offset - 4 must stay >= 0).
    {
        var file = try openLayout("parentOfX");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 12)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 3));
            try writer.writeAll("]}\n");
        }
    }
    {
        var file = try openLayout("parentOfY");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 12)});
            try writePtr(writer, 0, 4 * (1 + rng.uintLessThan(usize, 2)));
            try writer.writeAll("]}\n");
        }
    }
    // flagsToByte(f: Flags), byteToFlags(b: u8): every byte (both harnesses build `f` field by
    // field from the byte, not with `@bitCast`).
    inline for (.{ "flagsToByte", "byteToFlags" }) |name| {
        var file = try openLayout(name);
        defer file.close();
        const writer = file.writer();
        for (0..256) |b| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{b});
    }
    // setMode(b: u8, m: u2): every pair.
    {
        var file = try openLayout("setMode");
        defer file.close();
        const writer = file.writer();
        for (0..256) |b| for (0..4) |m| try writer.print("{{\"bufs\":[],\"args\":[{d},{d}]}}\n", .{ b, m });
    }
    // incCount/isOk(p: *Flags): a 3-byte buffer, the flags at offset 0, 1 or 2 (the other
    // bytes must not change).
    inline for (.{ "incCount", "isOk" }) |name| {
        var file = try openLayout(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 3)});
            try writePtr(writer, 0, rng.uintLessThan(usize, 3));
            try writer.writeAll("]}\n");
        }
    }
    // headerLen(bytes: []const u8): a buffer of 0..12 bytes, half with the magic number at the
    // slice start; the slice starts at 0..2 and runs to the buffer end.
    {
        var file = try openLayout("headerLen");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            var b = Bytes.random(rng, rng.uintAtMost(usize, 12));
            const off = rng.uintAtMost(usize, @min(2, b.len));
            if (i % 2 == 0 and b.len - off >= 4) b.setU32(off, 0x4C52_4941);
            try writeBufs(writer, &.{b});
            try writeSlice(writer, 0, off, b.len - off);
            try writer.writeAll("]}\n");
        }
    }
    // readHeader(bytes: []const u8): 8..12 bytes, an 8-byte slice at 0..len-8 (never too short).
    {
        var file = try openLayout("readHeader");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            const b = Bytes.random(rng, 8 + rng.uintAtMost(usize, 4));
            try writeBufs(writer, &.{b});
            try writeSlice(writer, 0, rng.uintAtMost(usize, b.len - 8), 8);
            try writer.writeAll("]}\n");
        }
    }
    // floatBits(p: *const f32): an 8-byte buffer, offset 0 or 4.
    {
        var file = try openLayout("floatBits");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
            try writer.writeAll("]}\n");
        }
    }
    // bitsToFloat(p: *f32, bits: u32): as floatBits, and the bits of an edge float (NaN, inf,
    // subnormal, ±0) or random bits.
    {
        var file = try openLayout("bitsToFloat");
        defer file.close();
        const writer = file.writer();
        const e = edgesF(f32);
        for (0..N) |i| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
            const bits: u32 = if (i < e.len) @bitCast(e[i]) else rng.int(u32);
            try writer.print(",{d}]}}\n", .{bits});
        }
    }
    // applyOp(i: usize, x: u32): `i` in 0..4 (3 and 4 are out of bounds), an edge or random `x`.
    {
        var file = try openLayout("applyOp");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| try writer.print("{{\"bufs\":[],\"args\":[{d},{d}]}}\n", .{ i % 5, edgyU32(rng) });
    }
    // twice(sq: bool, x: u32).
    {
        var file = try openLayout("twice");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| try writer.print("{{\"bufs\":[],\"args\":[{s},{d}]}}\n", .{ if (i % 2 == 0) "true" else "false", edgyU32(rng) });
    }
    // setCircle(p: *Shape, r: u32), shapeArea(p: *const Shape), growCircle(p: *Shape): `Shape`
    // is 8 bytes (payload at 0, tag at 4), in a 12-byte buffer at offset 0 or 4. The tag byte
    // is a valid tag (0..2), or 3 (no tag: illegal) in 1 line of 10.
    inline for (.{ "setCircle", "shapeArea", "growCircle" }) |name| {
        var file = try openLayout(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            var b = Bytes.random(rng, 12);
            const off = 4 * rng.uintLessThan(usize, 2);
            b.b[off + 4] = if (i % 10 == 9) 3 else rng.uintLessThan(u8, 3);
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, off);
            if (comptime std.mem.eql(u8, name, "setCircle")) try writer.print(",{d}", .{edgyU32(rng)});
            try writer.writeAll("]}\n");
        }
    }
    // bumpDigit(c: u8): 0 (error.Empty), 1..9, 10..15 (error.TooBig).
    {
        var file = try openLayout("bumpDigit");
        defer file.close();
        const writer = file.writer();
        for (0..16) |c| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{c});
    }
    // setNum(p: *Num, big: bool, v: u32) and numInt(p: *const Num): one 8-byte buffer (the
    // payload at 0, the hidden tag at 4); the tag byte is 0, 1 or, one time in 10, 2 (a set bit
    // above the 1-bit tag: `.unspecified`).
    inline for (.{ "setNum", "numInt" }) |name| {
        var file = try openLayout(name);
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            var b = Bytes.random(rng, 8);
            b.b[4] = if (i % 10 == 9) 2 else rng.uintLessThan(u8, 2);
            try writeBufs(writer, &.{b});
            try writePtr(writer, 0, 0);
            if (comptime std.mem.eql(u8, name, "setNum"))
                try writer.print(",{},{d}", .{ rng.boolean(), edgyU32(rng) });
            try writer.writeAll("]}\n");
        }
    }
    // numRoundTrip(big: bool, v: u32).
    {
        var file = try openLayout("numRoundTrip");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| try writer.print("{{\"bufs\":[],\"args\":[{},{d}]}}\n", .{ rng.boolean(), edgyU32(rng) });
    }
    // wordByte(v: u32, i: u2).
    {
        var file = try openLayout("wordByte");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| try writer.print("{{\"bufs\":[],\"args\":[{d},{d}]}}\n", .{ edgyU32(rng), rng.uintLessThan(u8, 4) });
    }
    // setHalf(p: *Word, v: u16): one 8-byte buffer, an aligned offset.
    {
        var file = try openLayout("setHalf");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 8)});
            try writePtr(writer, 0, 4 * rng.uintLessThan(usize, 2));
            try writer.print(",{d}]}}\n", .{rng.int(u16)});
        }
    }
    // regSigned(v: u8): every byte.
    {
        var file = try openLayout("regSigned");
        defer file.close();
        const writer = file.writer();
        for (0..256) |v| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{v});
    }
    // setRegFlags(p: *Reg, f: Flags): one 2-byte buffer, both offsets; `f` as its byte.
    {
        var file = try openLayout("setRegFlags");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 2)});
            try writePtr(writer, 0, rng.uintLessThan(usize, 2));
            try writer.print(",{d}]}}\n", .{rng.int(u8)});
        }
    }
    // wordHalf(v: u32).
    {
        var file = try openLayout("wordHalf");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{edgyU32(rng)});
    }
    // writeTable(i: usize, v: u32): 0..2 (a write to a `const` global), 3..4 (out of bounds).
    {
        var file = try openLayout("writeTable");
        defer file.close();
        const writer = file.writer();
        for (0..5) |i| try writer.print("{{\"bufs\":[],\"args\":[{d},{d}]}}\n", .{ i, edgyU32(rng) });
    }

    // wordArg(v: u32).
    {
        var file = try openLayout("wordArg");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{edgyU32(rng)});
    }

    // nibArg(v: u4): every value.
    {
        var file = try openLayout("nibArg");
        defer file.close();
        const writer = file.writer();
        for (0..16) |v| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{v});
    }

    // setNib(p: *Nib, v: u4): one 2-byte buffer, both offsets.
    {
        var file = try openLayout("setNib");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 2)});
            try writePtr(writer, 0, rng.uintLessThan(usize, 2));
            try writer.print(",{d}]}}\n", .{rng.int(u4)});
        }
    }

    // bumpPair(p: *Pair, bits: u6): one 2-byte buffer, both offsets.
    {
        var file = try openLayout("bumpPair");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 2)});
            try writePtr(writer, 0, rng.uintLessThan(usize, 2));
            try writer.print(",{d}]}}\n", .{rng.int(u6)});
        }
    }
}

// --- examples/vectors: the other lane-wise ops ---------------------------------------------

/// Two `@Vector(4, i32)` per line: the first 8 rows isolate overflow and division by zero
/// in each lane when `guarded` (division/modulo), with safe divisors in the other lanes.
/// Later rows mix edge values, then random values, without changing the shared PRNG stream.
fn writeVecPairI(w: anytype, rng: std.Random, n: usize, comptime guarded: bool) !void {
    const e = edgesI(i32);
    var b = vecI(rng, n + 3);
    var a = vecI(rng, n);
    if (guarded and n < 8) {
        a = .{ 6, 8, 10, 12 };
        b = .{ 2, 2, 2, 2 };
        if (n < 4) {
            a[n] = std.math.minInt(i32);
            b[n] = -1;
        } else {
            b[n - 4] = 0;
        }
    } else if (n < 49) b = .{ e[n % 7], e[(n / 7) % 7], e[(n + 3) % 7], e[(n / 7 + 2) % 7] };
    try w.writeAll("[");
    try writeIntSlice(w, i32, &a);
    try w.writeAll(",");
    try writeIntSlice(w, i32, &b);
    try w.writeAll("]\n");
}

/// vDiv .. vToFloat: N lines each.
fn genVectorOps(rng: std.Random) !void {
    inline for (.{ "vDiv", "vMod", "vMinMax", "vLess" }) |name| {
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        for (0..N) |n| try writeVecPairI(w, rng, n, std.mem.eql(u8, name, "vDiv") or std.mem.eql(u8, name, "vMod"));
    }
    inline for (.{ "vBits", "vOverflow" }) |name| {
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeIntSlice(w, u32, &vecU(rng, n));
            try w.writeAll(",");
            try writeIntSlice(w, u32, &vecU(rng, n + 5));
            try w.writeAll("]\n");
        }
    }
    {
        var file = try openOutV("vShift");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            // Lines 0..31: every shift amount; later lines also set bits above the 5 used.
            var s: [4]u32 = undefined;
            for (0..4) |i| s[i] = if (n < 32) @intCast((n + 8 * i) % 32) else rng.int(u32);
            try w.writeAll("[");
            try writeIntSlice(w, u32, &vecU(rng, n));
            try w.writeAll(",");
            try writeIntSlice(w, u32, &s);
            try w.writeAll("]\n");
        }
    }
    inline for (.{ "vNeg", "vAbs", "vToFloat" }) |name| {
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            try w.writeAll("[");
            try writeIntSlice(w, i32, &vecI(rng, n));
            try w.writeAll("]\n");
        }
    }
    inline for (.{ "sRem", "sMod" }) |name| {
        // Lines 0..48: every pair of `edgesI`; then random, with small divisors of both signs.
        var file = try openOutV(name);
        defer file.close();
        const w = file.writer();
        const e = edgesI(i32);
        for (0..N) |n| {
            const a: i32 = if (n < 49) e[n % 7] else rng.int(i32);
            const b: i32 = if (n < 49) e[n / 7] else rng.intRangeAtMost(i32, -9, 9);
            try w.print("[{d},{d}]\n", .{ a, b });
        }
    }
    {
        // Small values in some lines, so most lines fit in an `i16`.
        var file = try openOutV("vNarrow");
        defer file.close();
        const w = file.writer();
        for (0..N) |n| {
            var a = vecI(rng, n);
            if (n >= 64 and n % 2 == 0) {
                for (0..4) |i| a[i] = rng.intRangeAtMost(i32, -40000, 40000);
            }
            try w.writeAll("[");
            try writeIntSlice(w, i32, &a);
            try w.writeAll("]\n");
        }
    }
}

/// sentinelArr(i): `i = 3` reads the sentinel; `i > 3` panics. Last, so that the shared `rng`
/// stream of every earlier generator does not change.
fn genSentinelArr(rng: std.Random) !void {
    var file = try openSlices("sentinelArr");
    defer file.close();
    const writer = file.writer();
    for (0..N) |i| {
        const x = if (i % 4 == 0) edgesU(u32)[rng.uintLessThan(usize, 4)] else rng.uintLessThan(u32, 6);
        try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{x});
    }
}

/// dupeZLen(xs: []const u8): some bytes are 0; the one allocation fails in some inputs.
fn genDupeZ(rng: std.Random) !void {
    var file = try openLists("dupeZLen");
    defer file.close();
    const writer = file.writer();
    for (0..N) |i| {
        const n = rng.uintAtMost(usize, 24);
        try writeBuf(writer, rng, n, 6);
        try writeFailAt(writer, rng, i, 1);
        try writer.writeAll(",");
        const a = rng.uintAtMost(usize, n);
        try writeSlice(writer, 0, a, rng.uintAtMost(usize, n - a));
        try writer.writeAll("]}\n");
    }
}

/// ctlSum(b: u8), ctlMode(p: *const Ctl): every byte (a mode of 3 has no name).
fn genCtl() !void {
    {
        var file = try openLayout("ctlSum");
        defer file.close();
        const writer = file.writer();
        for (0..256) |b| try writer.print("{{\"bufs\":[],\"args\":[{d}]}}\n", .{b});
    }
    {
        var file = try openLayout("ctlMode");
        defer file.close();
        const writer = file.writer();
        for (0..256) |b| try writer.print("{{\"bufs\":[[{d}]],\"args\":[{{\"buf\":0,\"off\":0}}]}}\n", .{b});
    }
}

/// maskStore(p: *@Vector(4, bool), a: u32), maskCount(p), laneSet(r: *@Vector(4, u32), x: u32).
fn genVecMem(rng: std.Random) !void {
    {
        var file = try openLayout("maskStore");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 1)});
            try writePtr(writer, 0, 0);
            try writer.print(",{d}]}}\n", .{rng.int(u32)});
        }
    }
    {
        // Half of the bytes have no set padding bit (the high 4 bits).
        var file = try openLayout("maskCount");
        defer file.close();
        const writer = file.writer();
        for (0..N) |i| {
            const b = if (i % 2 == 0) rng.uintLessThan(u8, 16) else rng.int(u8);
            try writer.print("{{\"bufs\":[[{d}]],\"args\":[", .{b});
            try writePtr(writer, 0, 0);
            try writer.writeAll("]}\n");
        }
    }
    {
        var file = try openLayout("laneSet");
        defer file.close();
        const writer = file.writer();
        for (0..N) |_| {
            try writeBufs(writer, &.{Bytes.random(rng, 16)});
            try writePtr(writer, 0, 0);
            try writer.print(",{d}]}}\n", .{edgyU32(rng)});
        }
    }
}

/// divmod(a: u32, b: u32): edges of `a` with small and large `b`, random fill with `b > 0`, then
/// the edges of `a` with `b = 0`: `divl` faults (#DE, SIGFPE), the model throws `Zig.Error.trap`
/// (S7). The zero-divisor rows come last and use no PRNG output, so every other input stays the
/// same.
fn genDivmod(rng: std.Random) !void {
    var file = try openOutIn("tests/diff/asm/inputs", "divmod");
    defer file.close();
    const writer = file.writer();
    var n: usize = 0;
    for (edgesU(u32)) |a| {
        for ([_]u32{ 1, 2, 7, 0xffff_ffff }) |b| {
            try writer.print("[{d},{d}]\n", .{ a, b });
            n += 1;
        }
    }
    while (n < N) : (n += 1) {
        const b = if (n % 2 == 0) rng.intRangeAtMost(u32, 1, 100) else rng.intRangeAtMost(u32, 1, 0xffff_ffff);
        try writer.print("[{d},{d}]\n", .{ rng.int(u32), b });
    }
    for (edgesU(u32)) |a| try writer.print("[{d},0]\n", .{a});
}

/// claimOnce(): no argument; 20 runs, each with the OS scheduler's own interleaving.
fn genClaim() !void {
    var file = try openOutIn("tests/diff/threads/inputs", "claimOnce");
    defer file.close();
    const writer = file.writer();
    for (0..20) |_| try writer.writeAll("[]\n");
}

/// No-argument concurrent functions: each line is one run with the OS scheduler.
fn genNoArgs(comptime dir: []const u8, comptime names: anytype) !void {
    try compat.makePath(dir);
    inline for (names) |name| {
        var file = try openOutIn(dir, name);
        defer file.close();
        const writer = file.writer();
        for (0..20) |_| try writer.writeAll("[]\n");
    }
}

/// atomics: no argument; 20 runs of each function.
fn genAtomics() !void {
    try genNoArgs("tests/diff/atomics/inputs", .{ "mpRelAcq", "mpRelaxed", "sbRelaxed", "twoPlusTwoW", "stackPush" });
}

/// sync: the `std.Io` argument only; 20 runs of each function.
fn genSync() !void {
    try genNoArgs("tests/diff/sync/inputs", .{ "mutexCounter", "handoff", "semaphoreCounter", "rwLockRead" });
}
