//! asm's differential-test dispatch (examples/asm/asm.zig: bswap32, popcnt64, lzcnt64). Shared
//! runner code (fork/panic/render/JSONL plumbing) lives in tests/diff/common.zig; see its doc
//! comment for the build command and protocol.
//!
//! None of the three panics -- inline asm with register operands only has no bounds/overflow
//! check to trip. `popcnt64`/`lzcnt64` take and return `u64`: wide (>= 64-bit), so both the
//! argument and the result are quoted decimal (tests/diff/gen_inputs.zig's doc comment on the
//! floatconv int-argument functions states the same rule; `common.forkCall`'s `quote_wide`
//! covers the result side, `items[0].string` + `std.fmt.parseInt` the argument side, same as
//! tests/diff/floatconv/harness.zig's `runIntArg`). `bswap32` is `u32`: neither is quoted.
//!
//! examples/asm/asm.zig is x86_64 only (its doc comment); this harness is built by the STOCK
//! host zig (scripts/diff.sh), so it only runs on an x86_64 host -- excluded elsewhere via
//! AIR2LEAN_EXAMPLES, same as the example itself.

const std = @import("std");
// Named modules, wired up on the command line (see scripts/diff.sh):
//   --dep asm --dep common -Mroot=tests/diff/asm/harness.zig \
//   -Masm=examples/asm/asm.zig -Mcommon=tests/diff/common.zig
const asm_ex = @import("asm");
const common = @import("common");

pub const panic = common.panic;

fn runBswap32(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "asm", "bswap32", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x: u32 = @intCast(items[0].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(asm_ex.bswap32)), .{x}, asm_ex.bswap32, false);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runPopcnt64(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "asm", "popcnt64", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = std.fmt.parseInt(u64, items[0].string, 10) catch unreachable;
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(asm_ex.popcnt64)), .{x}, asm_ex.popcnt64, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runLzcnt64(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "asm", "lzcnt64", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const x = std.fmt.parseInt(u64, items[0].string, 10) catch unreachable;
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(asm_ex.lzcnt64)), .{x}, asm_ex.lzcnt64, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

fn runDivmod(gpa: std.mem.Allocator) !void {
    try common.forEachLine(gpa, "asm", "divmod", struct {
        fn call(_: std.mem.Allocator, items: []std.json.Value, writer: anytype) !void {
            const a: u32 = @intCast(items[0].integer);
            const b: u32 = @intCast(items[1].integer);
            const outcome = try common.forkCall(std.meta.ArgsTuple(@TypeOf(asm_ex.divmod)), .{ a, b }, asm_ex.divmod, true);
            try common.writeResult(writer, outcome);
        }
    }.call);
}

pub fn main() !void {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    try common.makePath("tests/diff/out/zig/asm");

    try runBswap32(gpa);
    try runPopcnt64(gpa);
    try runLzcnt64(gpa);
    try runDivmod(gpa);
}
