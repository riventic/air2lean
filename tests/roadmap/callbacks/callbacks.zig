//! E02 fixture: function-pointer call sites bound to registered contracts.

/// A callback implemented outside the program: bound to a registry contract (E02).
extern fn ext_visit(ctx: *u32, x: u32) callconv(.c) bool;

pub const Visitor = *const fn (*u32, u32) callconv(.c) bool;

/// A vtable: one function-pointer field.
pub const Ops = struct { visit: Visitor };

fn sumVisit(ctx: *u32, x: u32) callconv(.c) bool {
    ctx.* +%= x;
    return true;
}

const ext_ops: Ops = .{ .visit = &ext_visit };
const sum_ops: Ops = .{ .visit = &sumVisit };

/// The observer: calls `cb` on each element until it asks to stop.
pub fn forEach(xs: []const u32, ctx: *u32, cb: Visitor) bool {
    for (xs) |x| {
        if (!cb(ctx, x)) return false;
    }
    return true;
}

/// A call through a vtable field.
pub fn viaOps(ops: *const Ops, xs: []const u32, ctx: *u32) bool {
    return forEach(xs, ctx, ops.visit);
}

/// A call through a vtable field loaded from memory.
pub fn callOps(ops: *const Ops, ctx: *u32, x: u32) bool {
    return ops.visit(ctx, x);
}

/// The evaluator: one call through the pointer.
pub fn evaluate(cb: Visitor, ctx: *u32, x: u32) bool {
    return cb(ctx, x);
}

pub fn runExternal(xs: []const u32, ctx: *u32) bool {
    return viaOps(&ext_ops, xs, ctx);
}

pub fn runLocal(xs: []const u32, ctx: *u32) bool {
    return viaOps(&sum_ops, xs, ctx);
}

comptime {
    _ = &forEach;
    _ = &viaOps;
    _ = &callOps;
    _ = &evaluate;
    _ = &runExternal;
    _ = &runLocal;
}
