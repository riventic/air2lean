//! Fields of the `std.Io` model handles (check.sh; `Io` is Zig 0.16.0 and later): `std.Io` and
//! `std.Io.Future(T)` are one whole model value each (`Zig.Io`, `Zig.Future`), in both allocator
//! models, so a field of the *value* has no translation and the checker rejects it. A field
//! pointer into memory is an address and translates.
const std = @import("std");
const Io = std.Io;

// Rejected: `struct_field_val` of the handle.
pub fn userdata(io: Io) bool {
    return io.userdata != null;
}

pub fn vtableOf(io: Io) usize {
    return @intFromPtr(io.vtable);
}

pub fn resultOf(f: Io.Future(u32)) u32 {
    return f.result;
}

// Rejected: `struct_field_ptr` into a local that the model holds as a value.
pub fn localResult(f: Io.Future(u32)) u32 {
    var c = f;
    _ = &c;
    return c.result;
}

// Rejected: `aggregate_init` of the handle.
pub fn make(p: ?*anyopaque, v: *const Io.VTable) Io {
    return .{ .userdata = p, .vtable = v };
}

// Translated: the field's address in memory.
pub fn vtableAddr(io: *Io) usize {
    return @intFromPtr(&io.vtable) - @intFromPtr(io);
}

pub fn resultAddr(f: *Io.Future(u32)) usize {
    return @intFromPtr(&f.result) - @intFromPtr(f);
}

comptime {
    _ = &userdata;
    _ = &vtableOf;
    _ = &resultOf;
    _ = &localResult;
    _ = &make;
    _ = &vtableAddr;
    _ = &resultAddr;
}
