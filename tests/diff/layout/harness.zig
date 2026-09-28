//! layout's differential-test dispatch (examples/layout/layout.zig). Shared runner code
//! (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc comment for
//! the build command and protocol.
//!
//! Every function here uses memory: an input line is `{"bufs":[…],"args":[…]}`, a pointer
//! argument is `{"buf":i,"off":o}` into those buffers (common.forkCallBufs). `ptrFromAddr`'s
//! address argument is a plain usize, quoted (docs/generated-code.md's wide-int convention),
//! since it is not a pointer into any buffer.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep layout --dep common -Mroot=tests/diff/layout/harness.zig \
//   -Mlayout=examples/layout/layout.zig -Mcommon=tests/diff/common.zig
const layout = @import("layout");
const common = @import("common");

// This is the compilation's root module (see the build command above).
pub const panic = common.panic;

const ptr = common.ptrArg;

/// Runs `func` on each input line of `name`; `args` builds its argument tuple from the line.
fn run(gpa: std.mem.Allocator, comptime name: []const u8, comptime func: anytype, comptime args: anytype) !void {
    try common.forEachMemLine(gpa, "layout", name, struct {
        fn call(_: std.mem.Allocator, bufs: []common.Buf, items: []std.json.Value, writer: anytype) !void {
            const Args = std.meta.ArgsTuple(@TypeOf(func));
            const outcome = try common.forkCallBufs(Args, args(bufs, items), func, false, bufs);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn argAddrEq(b: []common.Buf, it: []std.json.Value) struct { *const u32, *const u32 } {
    return .{ ptr(*const u32, b, it[0]), ptr(*const u32, b, it[1]) };
}
fn argPtrRoundTrip(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argPtrFromAddr(_: []common.Buf, it: []std.json.Value) struct { usize } {
    return .{std.fmt.parseInt(usize, it[0].string, 10) catch unreachable};
}
fn argAsConst(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argDropConst(b: []common.Buf, it: []std.json.Value) struct { *const u32 } {
    return .{ptr(*const u32, b, it[0])};
}
fn argAsVolatile(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argAlign4(b: []common.Buf, it: []std.json.Value) struct { *align(1) u32 } {
    return .{ptr(*align(1) u32, b, it[0])};
}
fn argParentOfX(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}
fn argParentOfY(b: []common.Buf, it: []std.json.Value) struct { *u32 } {
    return .{ptr(*u32, b, it[0])};
}

/// The flags of `b`, field by field (not with `@bitCast`, which is what the tests check).
fn flagsOf(b: u8) layout.Flags {
    return .{
        .ready = b & 1 != 0,
        .err = b & 2 != 0,
        .mode = @intCast((b >> 2) & 3),
        .count = @intCast(b >> 4),
    };
}
fn argFlagsToByte(_: []common.Buf, it: []std.json.Value) struct { layout.Flags } {
    return .{flagsOf(@intCast(it[0].integer))};
}
fn argByteToFlags(_: []common.Buf, it: []std.json.Value) struct { u8 } {
    return .{@intCast(it[0].integer)};
}
fn argSetMode(_: []common.Buf, it: []std.json.Value) struct { u8, u2 } {
    return .{ @intCast(it[0].integer), @intCast(it[1].integer) };
}
fn argIncCount(b: []common.Buf, it: []std.json.Value) struct { *layout.Flags } {
    return .{ptr(*layout.Flags, b, it[0])};
}
fn argIsOk(b: []common.Buf, it: []std.json.Value) struct { *const layout.Flags } {
    return .{ptr(*const layout.Flags, b, it[0])};
}

fn argHeader(b: []common.Buf, it: []std.json.Value) struct { []const u8 } {
    return .{common.sliceArg([]const u8, b, it[0])};
}
fn argFloatBits(b: []common.Buf, it: []std.json.Value) struct { *const f32 } {
    return .{ptr(*const f32, b, it[0])};
}
fn argBitsToFloat(b: []common.Buf, it: []std.json.Value) struct { *f32, u32 } {
    return .{ ptr(*f32, b, it[0]), @intCast(it[1].integer) };
}

fn argApplyOp(_: []common.Buf, it: []std.json.Value) struct { usize, u32 } {
    return .{ @intCast(it[0].integer), @intCast(it[1].integer) };
}
fn argTwice(_: []common.Buf, it: []std.json.Value) struct { bool, u32 } {
    return .{ it[0].bool, @intCast(it[1].integer) };
}

fn argSetCircle(b: []common.Buf, it: []std.json.Value) struct { *layout.Shape, u32 } {
    return .{ ptr(*layout.Shape, b, it[0]), @intCast(it[1].integer) };
}
fn argShapeArea(b: []common.Buf, it: []std.json.Value) struct { *const layout.Shape } {
    return .{ptr(*const layout.Shape, b, it[0])};
}
fn argGrowCircle(b: []common.Buf, it: []std.json.Value) struct { *layout.Shape } {
    return .{ptr(*layout.Shape, b, it[0])};
}
fn argBumpDigit(_: []common.Buf, it: []std.json.Value) struct { u8 } {
    return .{@intCast(it[0].integer)};
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/layout");

    try run(gpa, "addrEq", layout.addrEq, argAddrEq);
    try run(gpa, "ptrRoundTrip", layout.ptrRoundTrip, argPtrRoundTrip);
    try run(gpa, "ptrFromAddr", layout.ptrFromAddr, argPtrFromAddr);
    try run(gpa, "asConst", layout.asConst, argAsConst);
    try run(gpa, "dropConst", layout.dropConst, argDropConst);
    try run(gpa, "asVolatile", layout.asVolatile, argAsVolatile);
    try run(gpa, "align4", layout.align4, argAlign4);
    try run(gpa, "parentOfX", layout.parentOfX, argParentOfX);
    try run(gpa, "parentOfY", layout.parentOfY, argParentOfY);
    try run(gpa, "flagsToByte", layout.flagsToByte, argFlagsToByte);
    try run(gpa, "byteToFlags", layout.byteToFlags, argByteToFlags);
    try run(gpa, "setMode", layout.setMode, argSetMode);
    try run(gpa, "incCount", layout.incCount, argIncCount);
    try run(gpa, "isOk", layout.isOk, argIsOk);
    try run(gpa, "headerLen", layout.headerLen, argHeader);
    try run(gpa, "readHeader", layout.readHeader, argHeader);
    try run(gpa, "floatBits", layout.floatBits, argFloatBits);
    try run(gpa, "bitsToFloat", layout.bitsToFloat, argBitsToFloat);
    try run(gpa, "applyOp", layout.applyOp, argApplyOp);
    try run(gpa, "twice", layout.twice, argTwice);
    try run(gpa, "setCircle", layout.setCircle, argSetCircle);
    try run(gpa, "shapeArea", layout.shapeArea, argShapeArea);
    try run(gpa, "growCircle", layout.growCircle, argGrowCircle);
    try run(gpa, "bumpDigit", layout.bumpDigit, argBumpDigit);
}
