//! slices's differential-test dispatch (examples/slices/slices.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! Every function uses the memory protocol (`{"bufs":[…],"args":[…]}`), also the pure
//! `factorial` (with no buffers). A slice argument is `{"buf":i,"off":o,"len":n}`
//! (common.sliceArg). A result slice into the buffers has the same form; a result slice into a
//! global (`@tagName`, `@errorName`) is `{"bytes":"<hex>"}`.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep slices --dep common -Mroot=tests/diff/slices/harness.zig \
//   -Mslices=examples/slices/slices.zig -Mcommon=tests/diff/common.zig
const slices = @import("slices");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

const ptr = common.ptrArg;
const slice = common.sliceArg;

fn int(comptime T: type, v: std.json.Value) T {
    return @intCast(v.integer);
}

/// Runs `func` on each input line of `name`; `args` builds its argument tuple from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime quote_wide: bool, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "slices", name, struct {
        fn call(_: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCallBufs(Args, args(bufs, items), func, quote_wide, bufs);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argReverse(b: []common.Buf, it: []std.json.Value) struct { []u32 } {
    return .{slice([]u32, b, it[0])};
}
fn argFill(b: []common.Buf, it: []std.json.Value) struct { []u8, u8 } {
    return .{ slice([]u8, b, it[0]), int(u8, it[1]) };
}
fn argClear(b: []common.Buf, it: []std.json.Value) struct { []u16 } {
    return .{slice([]u16, b, it[0])};
}
fn argCopyWithin(b: []common.Buf, it: []std.json.Value) struct { []u32, usize, usize, usize } {
    return .{ slice([]u32, b, it[0]), int(usize, it[1]), int(usize, it[2]), int(usize, it[3]) };
}
fn argCopy(b: []common.Buf, it: []std.json.Value) struct { []u8, []const u8 } {
    return .{ slice([]u8, b, it[0]), slice([]const u8, b, it[1]) };
}
fn argU8(_: []common.Buf, it: []std.json.Value) struct { u8 } {
    return .{int(u8, it[0])};
}
fn argUsize(_: []common.Buf, it: []std.json.Value) struct { usize } {
    return .{int(usize, it[0])};
}
fn argNone(_: []common.Buf, _: []std.json.Value) std.meta.ArgsTuple(@TypeOf(slices.bump)) {
    return .{};
}
fn argSumZ(b: []common.Buf, it: []std.json.Value) struct { [*:0]const u8 } {
    return .{ptr([*:0]const u8, b, it[0])};
}
fn argSubZ(b: []common.Buf, it: []std.json.Value) struct { []const u8, usize, usize } {
    return .{ slice([]const u8, b, it[0]), int(usize, it[1]), int(usize, it[2]) };
}
fn argTotal(b: []common.Buf, it: []std.json.Value) struct { *const [3]u32 } {
    return .{ptr(*const [3]u32, b, it[0])};
}
fn argAt(b: []common.Buf, it: []std.json.Value) struct { [*]const u32, usize } {
    return .{ ptr([*]const u32, b, it[0]), int(usize, it[1]) };
}
fn argMany(b: []common.Buf, it: []std.json.Value) struct { [*]const u32 } {
    return .{ptr([*]const u32, b, it[0])};
}
fn argColor(_: []common.Buf, it: []std.json.Value) struct { slices.Color } {
    return .{@enumFromInt(int(u8, it[0]))};
}
fn argBumpAt(b: []common.Buf, it: []std.json.Value) struct { *[4]u8, usize } {
    return .{ ptr(*[4]u8, b, it[0]), int(usize, it[1]) };
}
fn argLenOr(b: []common.Buf, it: []std.json.Value) struct { ?[]const u8 } {
    return .{slice(?[]const u8, b, it[0])};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/slices");

    try run(gpa, "reverse", slices.reverse, false, argReverse);
    try run(gpa, "fill", slices.fill, false, argFill);
    try run(gpa, "clear", slices.clear, false, argClear);
    try run(gpa, "copyWithin", slices.copyWithin, false, argCopyWithin);
    try run(gpa, "copy", slices.copy, false, argCopy);
    try run(gpa, "indexOfScalar", slices.indexOfScalar, true, argU8);
    try run(gpa, "factorial", slices.factorial, false, argUsize);
    try run(gpa, "bump", slices.bump, false, argNone);
    try run(gpa, "sumZ", slices.sumZ, false, argSumZ);
    try run(gpa, "subZ", slices.subZ, false, argSubZ);
    try run(gpa, "sumMid", slices.sumMid, false, argReverse);
    try run(gpa, "total", slices.total, false, argTotal);
    try run(gpa, "at", slices.at, false, argAt);
    try run(gpa, "second", slices.second, false, argMany);
    try run(gpa, "prevItem", slices.prevItem, false, argMany);
    try run(gpa, "colorName", slices.colorName, false, argColor);
    try run(gpa, "failName", slices.failName, false, argU8);
    try run(gpa, "bumpAt", slices.bumpAt, false, argBumpAt);
    try run(gpa, "localArr", slices.localArr, false, argUsize);
    try run(gpa, "sentinelArr", slices.sentinelArr, false, argUsize);
    try run(gpa, "lenOr", slices.lenOr, true, argLenOr);
}
