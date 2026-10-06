const std = @import("std");
const storage = @import("storage.zig");

// Return the source constant addresses so Sema must retain their pointer bases in AIR.
// The exporter filter covers only this public client; no private compiler AIR is supplied.
pub fn optionalPtr() *const u8 { return storage.optional_ptr; }
pub fn smallPtr() *const u8 { return storage.small_ptr; }
pub fn widePtr() *const u64 { return storage.wide_ptr; }
pub fn equalPtr() *const u16 { return storage.equal_ptr; }
pub fn sameOptionalPtr() *const u8 { return &storage.frozen.inner.optional.?.value; }
pub fn optionalSlice() []const u8 {
    const one: *const [1]u8 = @ptrCast(storage.optional_ptr);
    return one;
}
pub fn optionalRead() u8 { return storage.optional_ptr.*; }
pub fn smallRead() u8 { return storage.small_ptr.*; }
pub fn wideRead() u64 { return storage.wide_ptr.*; }

// The mutable case uses runtime projection from the same global identity. The model's
// independently resolved constant addresses must alias these projected addresses.
pub fn writeOptional(value: u8) u8 {
    storage.mutable.inner.optional.?.value = value;
    return storage.mutable.inner.optional.?.value;
}
pub fn writeSmall(value: u8) u8 {
    const p = &(storage.mutable.inner.small catch unreachable);
    p.* = value;
    return storage.mutable.inner.small catch unreachable;
}
pub fn writeWide(value: u64) u64 {
    const p = &(storage.mutable.inner.wide catch unreachable);
    p.* = value;
    return storage.mutable.inner.wide catch unreachable;
}

test "constant payload pointers alias exact nested offsets and retain shared identity" {
    const base = @intFromPtr(&storage.frozen);
    const inner = @offsetOf(storage.Outer, "inner");
    const opt = inner + @offsetOf(storage.Inner, "optional");
    try std.testing.expectEqual(base + opt + @offsetOf(storage.Payload, "value"), @intFromPtr(optionalPtr()));
    try std.testing.expectEqual(base + inner + @offsetOf(storage.Inner, "small") + 2, @intFromPtr(smallPtr()));
    try std.testing.expectEqual(base + inner + @offsetOf(storage.Inner, "wide"), @intFromPtr(widePtr()));
    try std.testing.expectEqual(base + inner + @offsetOf(storage.Inner, "equal"), @intFromPtr(equalPtr()));
    try std.testing.expectEqual(@as(u16, 23), equalPtr().*);
    try std.testing.expect(optionalPtr() == sameOptionalPtr());
    try std.testing.expect(optionalSlice().ptr == optionalPtr());
    try std.testing.expectEqual(@as(u8, 7), optionalRead());
    try std.testing.expectEqual(@as(u8, 19), smallRead());
    try std.testing.expectEqual(@as(u64, 41), wideRead());
}

test "mutable runtime projections preserve tag and unrelated fields" {
    storage.mutable = storage.frozen;
    try std.testing.expectEqual(@as(u8, 23), writeOptional(23));
    try std.testing.expectEqual(@as(u8, 31), writeSmall(31));
    try std.testing.expectEqual(@as(u64, 123), writeWide(123));
    try std.testing.expectEqual(storage.frozen.before, storage.mutable.before);
    try std.testing.expectEqual(storage.frozen.after, storage.mutable.after);
    try std.testing.expectEqual(storage.frozen.inner.optional.?.guard, storage.mutable.inner.optional.?.guard);
}

comptime {
    _ = &optionalPtr; _ = &smallPtr; _ = &widePtr; _ = &equalPtr; _ = &sameOptionalPtr;
    _ = &optionalSlice; _ = &optionalRead; _ = &smallRead; _ = &wideRead;
    _ = &writeOptional; _ = &writeSmall; _ = &writeWide;
}
