// Architecture audit (memory model) counterexamples. Each function is exported to AIR with the
// patched compiler (ReleaseSafe), translated, run in Lean from the empty memory, and compared
// with the native ReleaseSafe build of `main` below (see check.sh / README in this directory).
const std = @import("std");

// MM-1: the model gives every block a fixed address (first block at 4096), so the result of
// `@intFromPtr` is a constant that Lean can prove; natively it is a stack address.
pub noinline fn addrOfLocal() usize {
    var x: u8 = 7;
    const p: *u8 = &x;
    p.* +%= 1;
    return @intFromPtr(p);
}

// MM-2: an over-aligning `@alignCast` passes in the model (the block lands on 4096) and panics
// natively ("incorrect alignment") because the native stack slot is not 4096-aligned.
pub noinline fn overAlign() u8 {
    var buf: [2]u8 = .{ 1, 2 };
    const p: *align(4096) [2]u8 = @alignCast(&buf);
    return p[1];
}

// MM-4: `==` on ordinary pointers is structural (block, offset) while `@intFromPtr` is the
// address. Two pointers made from the same integer compare unequal in the model once a block
// is allocated over that address in between; natively both comparisons are true (result 3).
noinline fn eqLater(p1: *u8, n: usize) u8 {
    var b: [128]u8 = undefined;
    @memset(&b, 0);
    const pb: [*]u8 = &b;
    pb[0] = 1;
    const p2: *u8 = @ptrFromInt(n);
    const eq_ptr: u8 = @intFromBool(p1 == p2);
    const eq_int: u8 = @intFromBool(@intFromPtr(p1) == @intFromPtr(p2));
    return eq_ptr * 2 + eq_int + (pb[0] - 1);
}
pub noinline fn eqVsAddr() u8 {
    var a: [4]u8 = .{ 1, 2, 3, 4 };
    const pa: *u8 = &a[0];
    pa.* = 1;
    const n = @intFromPtr(pa) + 64;
    const p1: *u8 = @ptrFromInt(n);
    return eqLater(p1, n);
}

// MM-1 (order): the order of two blocks is the model's allocation order; natively the stack layout
// decides it.
pub noinline fn crossOrder() bool {
    var a: [16]u8 = undefined;
    var b: [16]u8 = undefined;
    @memset(&a, 1);
    @memset(&b, 2);
    const pa: [*]u8 = &a;
    const pb: [*]u8 = &b;
    return @intFromPtr(pa) < @intFromPtr(pb);
}

// MM-1 (distance): an integer round trip through a computed cross-block address. The model resolves the
// address to whatever block its layout puts there (deterministically), so this "reads b
// through a" with a fixed answer; natively the distance between the two stack slots differs.
pub noinline fn crossDistance() usize {
    var a: [8]u8 = undefined;
    var b: [8]u8 = undefined;
    @memset(&a, 1);
    @memset(&b, 2);
    const pa: [*]u8 = &a;
    const pb: [*]u8 = &b;
    return @intFromPtr(pb) -% @intFromPtr(pa);
}

pub fn main() void {
    std.debug.print("addrOfLocal {d}\n", .{addrOfLocal()});
    std.debug.print("eqVsAddr {d}\n", .{eqVsAddr()});
    std.debug.print("crossOrder {d}\n", .{@intFromBool(crossOrder())});
    std.debug.print("crossDistance {d}\n", .{crossDistance()});
    // Last: natively this panics ("incorrect alignment"); the model returns 2.
    std.debug.print("overAlign {d}\n", .{overAlign()});
}
