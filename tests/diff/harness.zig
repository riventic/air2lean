//! Differential-test Zig-side runner (docs/generated-code.md names the 8 functions).
//! Build with the STOCK system zig (scripts/diff.sh does this):
//!   zig build-exe -OReleaseSafe -femit-bin=<out> \
//!     --dep basic -Mroot=tests/diff/harness.zig -Mbasic=examples/basic/basic.zig
//! Two named modules, not a single-file `zig run`: single-file mode roots the module at the
//! entry file's directory and refuses an `@import` that escapes it (`../../examples/...`).
//! ReleaseSafe applies to this whole compilation unit, so `basic.zig`'s own overflow/bounds
//! checks stay active — the same semantics the AIR exporter captured.
//!
//! Reads `tests/diff/inputs/<fn>.jsonl` (tests/diff/gen_inputs.zig), calls the real function
//! for each input, and writes `tests/diff/out/zig/<fn>.jsonl`: one line per input, either
//! `{"ok": <result>}` or `{"fail": true}`. A safety panic aborts the child process (each call
//! runs in its own fork, so one panic never crashes the run); `sum` and `totalWeightedTardiness`
//! return u64, quoted as a decimal string for JS-safety — same convention as gen_inputs.zig.
//!
//! Each call's stderr (the panic trace macOS/Linux print on the aborting child) is redirected
//! to /dev/null: the input corpus deliberately contains many overflow cases, and letting every
//! one print a full stack trace would flood the terminal without adding information beyond the
//! {"fail": true} line already recorded.

const std = @import("std");
// Named module "basic", wired up on the command line (see scripts/diff.sh):
//   --dep basic -Mroot=tests/diff/harness.zig -Mbasic=examples/basic/basic.zig
// `zig run`'s single-file mode roots the module at the entry file's directory and refuses an
// `@import` path that escapes it, so a relative `../../examples/...` path does not work here.
const basic = @import("basic");

// `scale`, `clampAdd`, `absDiff` are `export fn` without `pub` in basic.zig: `export` gives them
// a C symbol but not cross-file visibility, so `basic.scale` etc. does not resolve. Declare them
// as `extern fn` instead — `extern`/`export` default to the C calling convention, so these link
// directly against the symbols basic.zig already exports into this same executable.
extern fn scale(a: u32, b: u8) u32;
extern fn clampAdd(a: u16, b: u16) u16;
extern fn absDiff(a: i32, b: i32) u32;

const Outcome = union(enum) { ok: u64, fail };

/// Runs `func(args)` in a forked child; the child never returns to this function on the parent
/// side. `Args` must be `std.meta.ArgsTuple(@TypeOf(func))`. The child writes its result as a
/// decimal string to a pipe and exits 0; if the child instead panics (safety check trip) it is
/// killed/aborted by the runtime, and the parent reports `.fail` once `waitpid` shows a
/// non-zero exit or a signal.
fn forkCall(comptime Args: type, args: Args, comptime func: anytype) !Outcome {
    const fds = try std.posix.pipe();
    const pid = try std.posix.fork();
    if (pid == 0) {
        // Child: silence the panic trace, compute, report, exit. Never returns.
        std.posix.close(fds[0]);
        if (std.fs.openFileAbsolute("/dev/null", .{ .mode = .write_only })) |devnull| {
            std.posix.dup2(devnull.handle, std.posix.STDERR_FILENO) catch {};
        } else |_| {}

        const raw = @call(.auto, func, args);
        const result: u64 = @intCast(raw);
        var buf: [24]u8 = undefined;
        const text = std.fmt.bufPrint(&buf, "{d}", .{result}) catch unreachable;
        _ = std.posix.write(fds[1], text) catch {};
        std.posix.exit(0);
    }

    // Parent.
    std.posix.close(fds[1]);
    defer std.posix.close(fds[0]);
    var buf: [24]u8 = undefined;
    var total: usize = 0;
    while (total < buf.len) {
        const n = std.posix.read(fds[0], buf[total..]) catch break;
        if (n == 0) break;
        total += n;
    }
    const wr = std.posix.waitpid(pid, 0);
    if (std.posix.W.IFEXITED(wr.status) and std.posix.W.EXITSTATUS(wr.status) == 0 and total > 0) {
        const val = std.fmt.parseInt(u64, buf[0..total], 10) catch return error.BadChildOutput;
        return .{ .ok = val };
    }
    return .fail;
}

fn writeResult(writer: anytype, outcome: Outcome, quote_wide: bool) !void {
    switch (outcome) {
        .ok => |v| if (quote_wide)
            try writer.print("{{\"ok\":\"{d}\"}}\n", .{v})
        else
            try writer.print("{{\"ok\":{d}}}\n", .{v}),
        .fail => try writer.writeAll("{\"fail\":true}\n"),
    }
}

fn jobFromJson(v: std.json.Value) basic.Job {
    return .{
        .duration = @intCast(v.object.get("duration").?.integer),
        .due = @intCast(v.object.get("due").?.integer),
        .weight = @intCast(v.object.get("weight").?.integer),
    };
}

/// Reads `tests/diff/inputs/<name>.jsonl`, opens `tests/diff/out/zig/<name>.jsonl`, and calls
/// `perLine` for each non-empty input line with the parsed JSON array and the output writer.
fn forEachLine(
    gpa: std.mem.Allocator,
    comptime name: []const u8,
    perLine: anytype,
) !void {
    const in_path = "tests/diff/inputs/" ++ name ++ ".jsonl";
    const out_path = "tests/diff/out/zig/" ++ name ++ ".jsonl";

    const content = try std.fs.cwd().readFileAlloc(gpa, in_path, 4 << 20);
    defer gpa.free(content);
    const out_file = try std.fs.cwd().createFile(out_path, .{});
    defer out_file.close();
    const writer = out_file.deprecatedWriter();

    var lines = std.mem.splitScalar(u8, content, '\n');
    while (lines.next()) |line| {
        if (line.len == 0) continue;
        var parsed = try std.json.parseFromSlice(std.json.Value, gpa, line, .{});
        defer parsed.deinit();
        try perLine(gpa, parsed.value.array.items, writer);
    }
}

fn runScale(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "scale", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u8 = @intCast(items[1].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(scale)), .{ a, b }, scale);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

fn runClampAdd(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "clampAdd", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u16 = @intCast(items[0].integer);
            const b: u16 = @intCast(items[1].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(clampAdd)), .{ a, b }, clampAdd);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

fn runAbsDiff(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "absDiff", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: i32 = @intCast(items[0].integer);
            const b: i32 = @intCast(items[1].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(absDiff)), .{ a, b }, absDiff);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

fn runTardiness(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "tardiness", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u32 = @intCast(items[1].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(basic.tardiness)), .{ a, b }, basic.tardiness);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

fn runWeightedTardiness(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "weightedTardiness", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const job = jobFromJson(items[0]);
            const start: u32 = @intCast(items[1].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(basic.weightedTardiness)), .{ job, start }, basic.weightedTardiness);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

fn runSum(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "sum", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const xs_json = items[0].array.items;
            const xs = try a.alloc(u32, xs_json.len);
            defer a.free(xs);
            for (xs_json, 0..) |v, i| xs[i] = @intCast(v.integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(basic.sum)), .{xs}, basic.sum);
            try writeResult(writer, outcome, true);
        }
    }.call);
}

fn runTotalWeightedTardiness(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "totalWeightedTardiness", struct {
        fn call(a: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const jobs_json = items[0].array.items;
            const jobs = try a.alloc(basic.Job, jobs_json.len);
            defer a.free(jobs);
            for (jobs_json, 0..) |jv, i| jobs[i] = jobFromJson(jv);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(basic.totalWeightedTardiness)), .{jobs}, basic.totalWeightedTardiness);
            try writeResult(writer, outcome, true);
        }
    }.call);
}

fn runClassify(gpa: std.mem.Allocator) !void {
    try forEachLine(gpa, "classify", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x: u8 = @intCast(items[0].integer);
            const outcome = try forkCall(std.meta.ArgsTuple(@TypeOf(basic.classify)), .{x}, basic.classify);
            try writeResult(writer, outcome, false);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try std.fs.cwd().makePath("tests/diff/out/zig");

    try runScale(gpa);
    try runClampAdd(gpa);
    try runAbsDiff(gpa);
    try runTardiness(gpa);
    try runWeightedTardiness(gpa);
    try runSum(gpa);
    try runTotalWeightedTardiness(gpa);
    try runClassify(gpa);
}
