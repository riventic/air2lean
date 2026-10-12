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

// L05 completion: optionals of nullable pointers (a separate flag), nullable pointers in unions
// and error unions, nullable slices, bulk memory, parent recovery and provenance-free offsets.
pub const Box = union(enum) { ptr: [*c]u8, num: u32 };
pub const Parent = extern struct { first: u64, second: u64 };
pub noinline fn optIsNull(p: ?*allowzero u8) bool { return p == null; }
pub noinline fn optUnwrap(p: ?*allowzero u8) usize { return @intFromPtr(p.?); }
pub noinline fn optWrap(p: *allowzero u8) ?*allowzero u8 { return p; }
pub noinline fn optEq(a: ?*allowzero u8, b: ?*allowzero u8) bool { return a == b; }
pub noinline fn optStoreLoad(slot: *?*allowzero u8, p: ?*allowzero u8) ?*allowzero u8 {
    slot.* = p;
    return slot.*;
}
pub noinline fn optPayloadPtr(slot: *?*allowzero u8) usize {
    if (slot.*) |*x| return @intFromPtr(x.*);
    return 1;
}
pub noinline fn optCIsNull(p: ?[*c]u8) bool { return p == null; }
/// `?*u8` → `?*allowzero u8`: Sema casts the payload, so null becomes a nonnull address zero.
pub noinline fn optFromOrdinary(p: ?*u8) ?*allowzero u8 { return p; }
pub noinline fn boxPtr(b: *const Box) usize {
    return switch (b.*) {
        .ptr => |p| @intFromPtr(p),
        .num => |n| n,
    };
}
pub noinline fn boxSet(b: *Box, p: [*c]u8) void { b.* = .{ .ptr = p }; }
pub noinline fn pairMake(p: [*c]u8) struct { [*c]u8, u8 } { return .{ p, 1 }; }
pub noinline fn pairFirst(p: [*c]u8) usize { return @intFromPtr(pairMake(p)[0]); }
pub noinline fn errPtr(fail: bool, p: [*c]u8) error{Bad}![*c]u8 {
    if (fail) return error.Bad;
    return p;
}
pub noinline fn errStore(slot: *(error{Bad}![*c]u8), p: [*c]u8) usize {
    slot.* = p;
    const q = slot.* catch return 7;
    return @intFromPtr(q);
}
pub noinline fn sliceAz(p: [*]allowzero u8, a: usize, b: usize) []allowzero u8 { return p[a..b]; }
pub noinline fn arrayAz(p: *allowzero [2]u8) []allowzero u8 { return p; }
/// Sema forms `p + a` before its null check: with a null `p` the check panics first.
pub noinline fn sliceC(p: [*c]u8, a: usize, b: usize) []u8 { return p[a..b]; }
pub noinline fn memsetAz(s: []allowzero u8, v: u8) void { @memset(s, v); }
pub noinline fn memcpyAz(d: []allowzero u8, s: []allowzero const u8) void { @memcpy(d, s); }
pub noinline fn memsetC(p: [*c]u8, n: usize, v: u8) void { @memset(p[0..n], v); }
pub noinline fn parentFirst(p: *allowzero u64) *allowzero Parent { return @fieldParentPtr("first", p); }
pub noinline fn parentSecond(p: *allowzero u64) *allowzero Parent { return @fieldParentPtr("second", p); }
/// A nonzero offset from a provenance-free address (`@ptrFromInt`, MMIO without a declared
/// device window): by address arithmetic `(2^64 - 4) + 4` is null.
pub noinline fn mmioIsNull(a: usize, n: usize) bool {
    const p: [*c]u32 = @ptrFromInt(a);
    return (p + n) == null;
}

fn addr(p: anytype) usize { return @intFromPtr(p); }
var runtime_one: usize = 1;
var runtime_zero: usize = 0;

/// `check.sh --native` builds one variant per case (`const case = "<name>";`): each ends the
/// process with a safety panic or a fault, so it cannot share `main`'s run.
const case = "main";
fn runCase() void {
    const nul: [*c]u8 = @ptrFromInt(@as(*volatile usize, &runtime_zero).*);
    const nul_many: [*]allowzero u8 = @ptrFromInt(@as(*volatile usize, &runtime_zero).*);
    const one = @as(*volatile usize, &runtime_one).*;
    const eql = std.mem.eql;
    if (comptime eql(u8, case, "sliceCNull")) std.debug.print("{d}\n", .{sliceC(nul, one, one).len});
    if (comptime eql(u8, case, "memsetCNull")) memsetC(nul, 0, 1);
    if (comptime eql(u8, case, "optUnwrapNull")) std.debug.print("{d}\n", .{optUnwrap(null)});
    if (comptime eql(u8, case, "memsetAzNull")) memsetAz(sliceAz(nul_many, 0, one), 1);
}

pub fn main() void {
    if (comptime !std.mem.eql(u8, case, "main")) return runCase();
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
    std.debug.print("nextPtr {d}\n", .{addr(nextPtr(&node)) - addr(&node)});
    std.debug.print("valPtr {d}\n", .{addr(valPtr(&node)) - addr(&node)});
    std.debug.print("allowzeroNextPtr {d}\n", .{addr(allowzeroNextPtr(@ptrFromInt(0)))});
    std.debug.print("allowzeroAdd {d} {d}\n", .{ addr(allowzeroAdd(@ptrFromInt(0), 0)), addr(allowzeroAdd(@ptrCast(live), 1)) - addr(live) });
    std.debug.print("toOptional {d} {d}\n", .{ @intFromBool(toOptional(nul) == null), @intFromBool(toOptional(live).? == @as(*u8, @ptrCast(live))) });
    std.debug.print("fromOptional {d} {d}\n", .{ addr(fromOptional(null)), @intFromBool(fromOptional(@ptrCast(live)) == live) });
    // Address arithmetic says `null + 1` is nonnull; an observed `true` contradicts it.
    std.debug.print("addIsNull {d} {s}\n", .{ @intFromBool(addIsNull(nul, 0)), if (addIsNull(nul, one)) "illegal" else "address" });
    // L05 completion.
    const some_zero: ?*allowzero u8 = @as(*allowzero u8, @ptrFromInt(@as(*volatile usize, &runtime_zero).*));
    const none_az: ?*allowzero u8 = null;
    const live_az: ?*allowzero u8 = @as(*allowzero u8, @ptrCast(live));
    std.debug.print("optional {d} {d} {d} {d} {d} {d} {d}\n", .{ @intFromBool(optIsNull(none_az)), @intFromBool(optIsNull(some_zero)), optUnwrap(some_zero), @intFromBool(optEq(none_az, some_zero)), @intFromBool(optEq(some_zero, some_zero)), @intFromBool(optEq(none_az, none_az)), @intFromBool(optEq(some_zero, live_az)) });
    std.debug.print("optWrap {d} {d}\n", .{ @intFromBool(optWrap(@ptrFromInt(@as(*volatile usize, &runtime_zero).*)) == null), addr(optWrap(@ptrCast(live)).?) - addr(live) });
    var opt_slot: ?*allowzero u8 = live_az;
    std.debug.print("optStoreLoad {d} {d} {d}\n", .{ @intFromBool(optStoreLoad(&opt_slot, none_az) == null), addr(optStoreLoad(&opt_slot, some_zero).?), @intFromBool(optStoreLoad(&opt_slot, live_az) == live_az) });
    opt_slot = some_zero;
    std.debug.print("optPayloadPtr {d}", .{optPayloadPtr(&opt_slot)});
    opt_slot = null;
    std.debug.print(" {d}\n", .{optPayloadPtr(&opt_slot)});
    std.debug.print("optC {d} {d}\n", .{ @intFromBool(optCIsNull(null)), @intFromBool(optCIsNull(nul)) });
    std.debug.print("optFromOrdinary {d} {d}\n", .{ @intFromBool(optFromOrdinary(null) == null), addr(optFromOrdinary(null).?) });
    var box = Box{ .ptr = null };
    std.debug.print("box {d}", .{boxPtr(&box)});
    boxSet(&box, live);
    std.debug.print(" {d}", .{@intFromBool(boxPtr(&box) == addr(live))});
    box = .{ .num = 5 };
    std.debug.print(" {d}\n", .{boxPtr(&box)});
    std.debug.print("pair {d} {d}\n", .{ pairFirst(nul), @intFromBool(pairFirst(live) == addr(live)) });
    var err_slot: error{Bad}![*c]u8 = error.Bad;
    std.debug.print("errPtr {d} {d} errStore {d} {d}\n", .{ if (errPtr(false, nul)) |p| addr(p) else |_| 99, if (errPtr(true, live)) |p| addr(p) else |_| 99, errStore(&err_slot, nul), @intFromBool(errStore(&err_slot, live) == addr(live)) });
    const nul_many: [*]allowzero u8 = @ptrFromInt(@as(*volatile usize, &runtime_zero).*);
    const live_many: [*]allowzero u8 = @ptrCast(live);
    const empty = sliceAz(nul_many, 0, 0);
    const part = sliceAz(live_many, 1, 2);
    const whole = arrayAz(@ptrFromInt(@as(*volatile usize, &runtime_zero).*));
    std.debug.print("sliceAz {d} {d} {d} {d} arrayAz {d} {d}\n", .{ addr(empty.ptr), empty.len, addr(part.ptr) - addr(live), part.len, addr(whole.ptr), whole.len });
    memsetAz(empty, 1);
    memcpyAz(empty, empty);
    memsetAz(sliceAz(live_many, 0, 2), 5);
    std.debug.print("memsetAz {d} {d}", .{ byte2[0], byte2[1] });
    byte2[1] = 6;
    memcpyAz(sliceAz(live_many, 0, 1), sliceAz(live_many, 1, 2));
    std.debug.print(" memcpyAz {d}", .{byte2[0]});
    memsetC(live, 2, 3);
    std.debug.print(" memsetC {d} {d} sliceC {d}\n", .{ byte2[0], byte2[1], sliceC(live, 0, 2).len });
    var parent = Parent{ .first = 1, .second = 2 };
    std.debug.print("parent {d} {d}\n", .{ @intFromBool(parentSecond(&parent.second) == &parent), addr(parentFirst(@ptrFromInt(@as(*volatile usize, &runtime_zero).*))) });
    // Address arithmetic says `(2^64 - 4) + 4` is null; an observed `false` contradicts it.
    std.debug.print("mmioIsNull {d} {s}\n", .{ @intFromBool(mmioIsNull(4096, 0)), if (mmioIsNull(std.math.maxInt(usize) - 3, one)) "address" else "illegal" });
    // Last: Zig 0.17.0 checks `&n.*.next` of a null `[*c]Node` and panics here.
    std.debug.print("nullNextPtr {d}\n", .{addr(nextPtr(nul_node))});
}
