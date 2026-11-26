//! T04: one atomic op on an `f80` cell. `scripts/aarch64-abi.py` builds this file once per op,
//! with a generated module `op` (`pub const name: []const u8 = "<op>";`), and records whether it
//! compiles and, if it runs, whether the cell and the returned value are those of the same op done
//! without atomics (the model's value). Only the selected op is analyzed (the `if` chain is
//! comptime), so an op the compiler rejects does not keep the others from building.
//!
//! The exit code is the result, independent of the std printing API of each Zig version: bit 0 is
//! set when the cell holds the model's value, bit 1 when the returned value is the model's.
const std = @import("std");
const op: []const u8 = @import("op").name;

var cell: f80 = 1.5;
const operand: f80 = 2.5;

fn is(comptime name: []const u8) bool {
    return comptime std.mem.eql(u8, op, name);
}

/// The op on `p`; returns what it returns (the old value, the loaded value, or `0` for a store).
noinline fn atomic(p: *f80, v: f80) f80 {
    if (comptime is("load_monotonic")) return @atomicLoad(f80, p, .monotonic);
    if (comptime is("load_acquire")) return @atomicLoad(f80, p, .acquire);
    if (comptime is("load_seq_cst")) return @atomicLoad(f80, p, .seq_cst);
    if (comptime is("store_monotonic")) @atomicStore(f80, p, v, .monotonic);
    if (comptime is("store_release")) @atomicStore(f80, p, v, .release);
    if (comptime is("store_seq_cst")) @atomicStore(f80, p, v, .seq_cst);
    if (comptime is("rmw_Xchg")) return @atomicRmw(f80, p, .Xchg, v, .seq_cst);
    if (comptime is("rmw_Add")) return @atomicRmw(f80, p, .Add, v, .seq_cst);
    if (comptime is("rmw_Sub")) return @atomicRmw(f80, p, .Sub, v, .seq_cst);
    if (comptime is("rmw_Max")) return @atomicRmw(f80, p, .Max, v, .seq_cst);
    if (comptime is("rmw_Min")) return @atomicRmw(f80, p, .Min, v, .seq_cst);
    if (comptime is("cmpxchg_strong")) return @cmpxchgStrong(f80, p, 1.5, v, .seq_cst, .seq_cst) orelse 0;
    if (comptime is("cmpxchg_weak")) return @cmpxchgWeak(f80, p, 1.5, v, .seq_cst, .seq_cst) orelse 0;
    return 0;
}

/// The same op without atomics: the cell afterwards and the returned value.
fn model(old: f80, v: f80) struct { f80, f80 } {
    if (comptime std.mem.startsWith(u8, op, "load_")) return .{ old, old };
    if (comptime std.mem.startsWith(u8, op, "store_")) return .{ v, 0 };
    if (comptime is("rmw_Xchg")) return .{ v, old };
    if (comptime is("rmw_Add")) return .{ old + v, old };
    if (comptime is("rmw_Sub")) return .{ old - v, old };
    if (comptime is("rmw_Max")) return .{ @max(old, v), old };
    if (comptime is("rmw_Min")) return .{ @min(old, v), old };
    // A `cmpxchg` whose expected value is the cell succeeds and returns `null` (`0` here).
    return .{ v, 0 };
}

fn bits(x: f80) u80 {
    return @bitCast(x);
}

pub fn main() u8 {
    const old = cell;
    const returned = atomic(&cell, operand);
    const want = model(old, operand);
    return @as(u8, @intFromBool(bits(cell) == bits(want[0]))) |
        @as(u8, @intFromBool(bits(returned) == bits(want[1]))) << 1;
}
