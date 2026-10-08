const std = @import("std");

pub noinline fn cNull(address: usize) bool {
    const p: [*c]const u8 = @ptrFromInt(address);
    return p == null;
}
pub noinline fn allowzeroAddress(address: usize) usize {
    const p: *allowzero const u8 = @ptrFromInt(address);
    return @intFromPtr(p);
}
pub noinline fn allowzeroManyAddress(address: usize) usize {
    const p: [*]allowzero const u8 = @ptrFromInt(address);
    return @intFromPtr(p);
}
pub noinline fn castChecked(address: usize) bool {
    const p: [*c]const u8 = @ptrFromInt(address);
    if (p == null) return false;
    const q: *const u8 = @ptrCast(p);
    return @intFromPtr(q) == address;
}
pub noinline fn cRead(p: [*c]const u8) u8 {
    if (p == null) return 0;
    return p.*;
}
pub noinline fn cZero() [*c]const u8 { return null; }

// L05 storage, aggregate, projection and optional-conversion cases (compare Generate.lean).
pub const Node = extern struct { next: [*c]u8, val: u8 };
pub noinline fn storeLoad(slot: *[*c]u8, p: [*c]u8) [*c]u8 {
    slot.* = p;
    return slot.*;
}
pub noinline fn storedIsNull(slot: *[*c]u8) bool { return slot.* == null; }
pub noinline fn allowzeroStoreLoad(slot: **allowzero u8, p: *allowzero u8) *allowzero u8 {
    slot.* = p;
    return slot.*;
}
pub noinline fn nodeNext(n: [*c]Node) [*c]u8 { return n.*.next; }
pub noinline fn nodeVal(n: [*c]Node) u8 { return n.*.val; }
pub noinline fn nodeRoundTrip(slot: *Node, v: u8) u8 {
    slot.* = .{ .next = null, .val = v };
    const r = slot.*;
    return if (r.next == null) r.val else 0;
}
pub noinline fn arrayItem(a: *[2][*c]u8, i: usize) [*c]u8 { return a[i]; }
pub noinline fn cAdd(p: [*c]u8, n: usize) [*c]u8 { return p + n; }
pub noinline fn cSub(p: [*c]u8, n: usize) [*c]u8 { return p - n; }
pub noinline fn cIndex(p: [*c]u8, i: usize) [*c]u8 { return &p[i]; }
pub noinline fn cElem(p: [*c]u8, i: usize) u8 { return p[i]; }
pub noinline fn nextPtr(n: [*c]Node) [*c][*c]u8 { return &n.*.next; }
pub noinline fn valPtr(n: [*c]Node) [*c]u8 { return &n.*.val; }
pub noinline fn allowzeroNextPtr(n: *allowzero Node) *allowzero [*c]u8 { return &n.next; }
pub noinline fn allowzeroAdd(p: [*]allowzero u8, n: usize) [*]allowzero u8 { return p + n; }
pub noinline fn toOptional(p: [*c]u8) ?*u8 { return p; }
pub noinline fn fromOptional(p: ?*u8) [*c]u8 { return p; }
/// A nonzero offset from address zero: by address arithmetic `p + n` is nonnull for n = 1,
/// but the inbounds offset lets LLVM fold the test to `p == null`.
pub noinline fn addIsNull(p: [*c]u8, n: usize) bool { return (p + n) == null; }

fn addr(p: anytype) usize { return @intFromPtr(p); }
var runtime_one: usize = 1;
var runtime_zero: usize = 0;

pub fn main() void {
    for ([_]usize{ 0, 1, 8, 4095, 65535, std.math.maxInt(usize) }) |n| {
        std.debug.print("{d} {d} {d} {d} {d}\n", .{ n, @intFromBool(cNull(n)), allowzeroAddress(n), allowzeroManyAddress(n), @intFromBool(castChecked(n)) });
    }
    const byte: u8 = 37;
    std.debug.print("read {d} {d}\n", .{ cRead(null), cRead(@ptrCast(&byte)) });
    std.debug.print("zero {d}\n", .{@intFromPtr(cZero())});
    const one = @as(*volatile usize, &runtime_one).*;
    // Runtime null: a constant would let LLVM propagate it into the callees.
    const nul: [*c]u8 = @ptrFromInt(@as(*volatile usize, &runtime_zero).*);
    const nul_node: [*c]Node = null;
    var byte2 = [2]u8{ 7, 9 };
    const live: [*c]u8 = &byte2;
    var slot: [*c]u8 = live;
    std.debug.print("storeLoad {d} {d}\n", .{ addr(storeLoad(&slot, null)), @intFromBool(storeLoad(&slot, live) == live) });
    slot = null;
    std.debug.print("storedIsNull {d}", .{@intFromBool(storedIsNull(&slot))});
    slot = live;
    std.debug.print(" {d}\n", .{@intFromBool(storedIsNull(&slot))});
    var az_slot: *allowzero u8 = @ptrCast(live);
    std.debug.print("allowzeroStoreLoad {d} {d}\n", .{ addr(allowzeroStoreLoad(&az_slot, @ptrFromInt(0))), @intFromBool(addr(allowzeroStoreLoad(&az_slot, @ptrCast(live))) == addr(live)) });
    var node = Node{ .next = null, .val = 0 };
    std.debug.print("nodeNext {d}", .{addr(nodeNext(&node))});
    node = .{ .next = live, .val = 5 };
    std.debug.print(" {d} nodeVal {d}\n", .{ @intFromBool(nodeNext(&node) == live), nodeVal(&node) });
    std.debug.print("nodeRoundTrip {d}\n", .{nodeRoundTrip(&node, 9)});
    var items = [2][*c]u8{ live, null };
    std.debug.print("arrayItem {d} {d}\n", .{ @intFromBool(arrayItem(&items, 0) == live), addr(arrayItem(&items, 1)) });
    std.debug.print("cAdd {d} {d}\n", .{ addr(cAdd(nul, 0)), addr(cAdd(live, 1)) - addr(live) });
    std.debug.print("cSub {d} {d}\n", .{ addr(cSub(nul, 0)), addr(live) - addr(cSub(live + 1, 1)) });
    std.debug.print("cIndex {d} {d}\n", .{ addr(cIndex(nul, 0)), addr(cIndex(live, 1)) - addr(live) });
    std.debug.print("cElem {d} {d}\n", .{ cElem(live, 0), cElem(live, 1) });
    std.debug.print("nextPtr {d} {d}\n", .{ addr(nextPtr(nul_node)), addr(nextPtr(&node)) - addr(&node) });
    std.debug.print("valPtr {d}\n", .{addr(valPtr(&node)) - addr(&node)});
    std.debug.print("allowzeroNextPtr {d}\n", .{addr(allowzeroNextPtr(@ptrFromInt(0)))});
    std.debug.print("allowzeroAdd {d} {d}\n", .{ addr(allowzeroAdd(@ptrFromInt(0), 0)), addr(allowzeroAdd(@ptrCast(live), 1)) - addr(live) });
    std.debug.print("toOptional {d} {d}\n", .{ @intFromBool(toOptional(nul) == null), @intFromBool(toOptional(live).? == @as(*u8, @ptrCast(live))) });
    std.debug.print("fromOptional {d} {d}\n", .{ addr(fromOptional(null)), @intFromBool(fromOptional(@ptrCast(live)) == live) });
    // Address arithmetic says `null + 1` is nonnull; an observed `true` contradicts it.
    std.debug.print("addIsNull {d} {s}\n", .{ @intFromBool(addIsNull(nul, 0)), if (addIsNull(nul, one)) "illegal" else "address" });
}
