//! Fields of a std model handle (check.sh). In the default allocator model `std.mem.Allocator`
//! and `std.Thread` are one whole model value each (`Zig.Allocator`, a thread id) without the
//! native fields, so a field of the *value* (read, addressed in a local, or set by a literal)
//! has no translation and the checker rejects it. A field pointer into memory is an address and
//! translates; under `--allocator-model translated` `mem.Allocator` is the ordinary struct.
const std = @import("std");
const Allocator = std.mem.Allocator;

// Rejected in the default allocator model: `struct_field_val` of the handle.
pub fn ctxOf(a: Allocator) usize {
    return @intFromPtr(a.ptr);
}

pub fn vtableOf(a: Allocator) usize {
    return @intFromPtr(a.vtable);
}

const Holder = struct { a: Allocator, n: u32 };

pub fn nested(h: Holder) usize {
    return @intFromPtr(h.a.ptr);
}

// Rejected: `struct_field_ptr` into a local that the model holds as a value.
pub fn localCtx(a: Allocator) usize {
    var c = a;
    _ = &c;
    return @intFromPtr(c.ptr);
}

pub fn localNested(a: Allocator) usize {
    var h: Holder = .{ .a = a, .n = 1 };
    _ = &h;
    return @intFromPtr(h.a.vtable);
}

// Rejected: `aggregate_init` of the handle.
pub fn make(p: *anyopaque, v: *const Allocator.VTable) Allocator {
    return .{ .ptr = p, .vtable = v };
}

// Translated in both allocator models: the field's address in memory.
pub fn vtableAddr(a: *Allocator) usize {
    return @intFromPtr(&a.vtable) - @intFromPtr(a);
}

pub fn implAddr(t: *std.Thread) usize {
    return @intFromPtr(&t.impl) - @intFromPtr(t);
}

// Translated: the holder's own fields.
pub fn count(h: Holder) u32 {
    return h.n;
}

pub fn pass(h: Holder) Allocator {
    return h.a;
}

comptime {
    _ = &ctxOf;
    _ = &vtableOf;
    _ = &nested;
    _ = &localCtx;
    _ = &localNested;
    _ = &make;
    _ = &vtableAddr;
    _ = &implAddr;
    _ = &count;
    _ = &pass;
}
