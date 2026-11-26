//! Pointers to declared `opaque {}` types (README.md). A pointer to an opaque type
//! is a value: it is copied, compared, tested for null, wrapped in and unwrapped from an optional,
//! passed, returned, stored in memory and cast. Nothing is loaded or stored through it.
//! `main` (stock Zig, `check.sh --native`) prints what Runner.lean prints from the translation.
const std = @import("std");

pub const Handle = opaque {
    /// A method of the opaque type: the handle is a `*u32` behind the interface.
    pub noinline fn value(h: *Handle) u32 {
        const p: *u32 = @ptrCast(@alignCast(h));
        return p.*;
    }
};
pub const Other = opaque {};

/// A generic opaque type: one type per `T`, with a name the compiler makes (`Typed(u32)`).
pub fn Typed(comptime T: type) type {
    return opaque {
        pub noinline fn of(p: *T) *@This() {
            return @ptrCast(p);
        }
    };
}

pub const Cell = struct { h: *Handle, o: ?*Handle, n: u32 };

pub noinline fn typedOf(p: *u32) *Typed(u32) {
    return Typed(u32).of(p);
}
pub noinline fn typedSame(a: *Typed(u32), b: *Typed(u32)) bool {
    return a == b;
}
pub noinline fn typedToHandle(t: *Typed(u32)) *Handle {
    return @ptrCast(t);
}

// Copy, comparison, null test, optional wrap and unwrap.
pub noinline fn copy(h: *Handle) *Handle {
    return h;
}
pub noinline fn same(a: *Handle, b: *Handle) bool {
    return a == b;
}
pub noinline fn constSame(a: *const Handle, b: *Handle) bool {
    return a == b;
}
pub noinline fn isNull(h: ?*Handle) bool {
    return h == null;
}
pub noinline fn wrap(h: *Handle) ?*Handle {
    return h;
}
pub noinline fn unwrap(h: ?*Handle) *Handle {
    return h.?;
}
pub noinline fn orElse(h: ?*Handle, d: *Handle) *Handle {
    return h orelse d;
}
pub noinline fn optSame(a: ?*Handle, b: ?*Handle) bool {
    return a == b;
}

// The pointer in memory: a slot, a struct field, an optional field, an array item, a slice item.
pub noinline fn slotSwap(slot: **Handle, h: *Handle) *Handle {
    const old = slot.*;
    slot.* = h;
    return old;
}
pub noinline fn cellPut(c: *Cell, h: *Handle, o: ?*Handle) void {
    c.h = h;
    c.o = o;
}
pub noinline fn cellGet(c: *const Cell) *Handle {
    return c.h;
}
pub noinline fn cellOpt(c: *const Cell) ?*Handle {
    return c.o;
}
pub noinline fn item(hs: []const *Handle, i: usize) *Handle {
    return hs[i];
}
pub noinline fn pair(a: *Handle, b: *Handle) [2]*Handle {
    return .{ a, b };
}

// Casts to an opaque pointer: from a typed pointer, between opaque types, to and from
// `*anyopaque`, and a qualifier change.
pub noinline fn erase(p: *u32) *Handle {
    return @ptrCast(p);
}
pub noinline fn toAny(h: *Handle) *anyopaque {
    return h;
}
pub noinline fn fromAny(p: *anyopaque) *Handle {
    return @ptrCast(p);
}
pub noinline fn toOther(h: *Handle) *Other {
    return @ptrCast(h);
}
pub noinline fn toConst(h: *Handle) *const Handle {
    return h;
}
pub noinline fn optErase(p: ?*u32) ?*Handle {
    return @ptrCast(p);
}
pub noinline fn address(h: *Handle) usize {
    return @intFromPtr(h);
}
// A pointer to an opaque type has alignment 1; a stricter one is a checked `@alignCast`.
pub noinline fn alignUp(h: *Handle) *align(4) Handle {
    return @alignCast(h);
}
pub noinline fn alignDown(h: *align(4) Handle) *Handle {
    return h;
}

// A handle through a function pointer.
pub noinline fn apply(f: *const fn (*Handle) *Handle, h: *Handle) *Handle {
    return f(h);
}
pub fn pass(h: *Handle) *Handle {
    return h;
}
pub noinline fn viaApply(h: *Handle) bool {
    return apply(pass, h) == h;
}

// Recovering the typed pointer (`--allocator-model translated` only, as for `*anyopaque`).
pub noinline fn recover(h: *Handle) *u32 {
    return @ptrCast(@alignCast(h));
}
pub noinline fn roundTrip(p: *u32) u32 {
    const h = erase(p);
    recover(h).* += 1;
    return h.value();
}

fn bit(b: bool) u8 {
    return @intFromBool(b);
}

pub fn main() void {
    var x: u32 = 41;
    var y: u32 = 7;
    const hx = erase(&x);
    const hy = erase(&y);
    std.debug.print("copy {d} same {d} {d} constSame {d}\n", .{ bit(copy(hx) == hx), bit(same(hx, hx)), bit(same(hx, hy)), bit(constSame(hx, hx)) });
    std.debug.print("isNull {d} {d} wrap {d} unwrap {d}\n", .{ bit(isNull(null)), bit(isNull(hx)), bit(wrap(hx) == hx), bit(unwrap(hy) == hy) });
    std.debug.print("orElse {d} {d} optSame {d} {d} {d}\n", .{ bit(orElse(null, hy) == hy), bit(orElse(hx, hy) == hx), bit(optSame(null, null)), bit(optSame(hx, null)), bit(optSame(hx, hx)) });
    var slot: *Handle = hx;
    const old = slotSwap(&slot, hy);
    std.debug.print("slotSwap {d} {d}\n", .{ bit(old == hx), bit(slot == hy) });
    var cell = Cell{ .h = hx, .o = null, .n = 3 };
    cellPut(&cell, hy, hx);
    std.debug.print("cell {d} {d} {d}", .{ bit(cellGet(&cell) == hy), bit(cellOpt(&cell) == hx), cell.n });
    cellPut(&cell, hx, null);
    std.debug.print(" {d} {d}\n", .{ bit(cellGet(&cell) == hx), bit(cellOpt(&cell) == null) });
    const hs = pair(hx, hy);
    std.debug.print("pair {d} {d} item {d} {d}\n", .{ bit(hs[0] == hx), bit(hs[1] == hy), bit(item(&hs, 0) == hx), bit(item(&hs, 1) == hy) });
    std.debug.print("casts {d} {d} {d} {d} {d} {d}\n", .{ bit(fromAny(toAny(hx)) == hx), bit(@intFromPtr(toOther(hx)) == @intFromPtr(hx)), bit(toConst(hx) == hx), bit(optErase(null) == null), bit(optErase(&y) == hy), bit(address(hx) == @intFromPtr(&x)) });
    std.debug.print("align {d}\n", .{bit(alignDown(alignUp(hx)) == hx)});
    std.debug.print("typed {d} {d} {d}\n", .{ bit(typedSame(typedOf(&x), typedOf(&x))), bit(typedSame(typedOf(&x), typedOf(&y))), bit(typedToHandle(typedOf(&x)) == hx) });
    std.debug.print("viaApply {d}\n", .{bit(viaApply(hx))});
    std.debug.print("value {d} roundTrip {d} {d}\n", .{ hx.value(), roundTrip(&x), x });
}
