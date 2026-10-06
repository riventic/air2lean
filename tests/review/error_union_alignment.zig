//! Native ABI oracle. Expected offsets come from the approved compiler helpers;
//! error numbers are read from @intFromError, never assumed from declaration order.
const std = @import("std");
const builtin = @import("builtin");
const E = error{Bad};
const Pair = extern struct { first: u16, second: u16 };

fn check(comptime T: type, payload: T, comptime eo: usize, comptime po: usize,
    comptime size: usize, comptime alignment: usize) !void {
    errdefer std.debug.print("error-union ABI case: {s}\n", .{@typeName(T)});
    try std.testing.expectEqual(size, @sizeOf(E!T));
    try std.testing.expectEqual(alignment, @alignOf(E!T));
    var ok: E!T = payload;
    const pp: *T = if (ok) |*p| p else |_| unreachable;
    try std.testing.expectEqual(po, @intFromPtr(pp) - @intFromPtr(&ok));
    const ok_bytes = std.mem.asBytes(&ok);
    try std.testing.expectEqualSlices(u8, std.mem.asBytes(&payload),
        ok_bytes[po .. po + @sizeOf(T)]);
    try std.testing.expectEqual(@as(u8, 0), ok_bytes[eo]);
    try std.testing.expectEqual(@as(u8, 0), ok_bytes[eo + 1]);
    var bad: E!T = error.Bad;
    const bad_bytes = std.mem.asBytes(&bad);
    const code: u16 = @intFromError(error.Bad);
    try std.testing.expectEqual(@as(u8, @truncate(code)), bad_bytes[eo]);
    try std.testing.expectEqual(@as(u8, @truncate(code >> 8)), bad_bytes[eo + 1]);
}

test "error union ABI equal alignment and zero payload" {
    try check(u8, 0x34, 0, 2, 4, 2);
    try check(u16, 0x1234, 2, 0, 4, 2);
    try check(f16, 1.5, 2, 0, 4, 2);
    try check(Pair, .{ .first = 0x1234, .second = 0x5678 }, 4, 0, 6, 2);
    try check([2]u16, .{ 0x1234, 0x5678 }, 4, 0, 6, 2);
    try check(u64, 0x12345678, 8, 0, 16, 8);
    try check(void, {}, 0, 0, 2, 2);
    // 0.14/0.15 lazy @alignOf reports 8, but eager exporter ABI is (size=2, align=2).
    // 0.16 consistently reports (size=8, align=8); the model targets that representation.
    const zero_array_size: usize = if (builtin.zig_version.minor >= 16) 8 else 2;
    try check([0]u64, .{}, 0, 0, zero_array_size, 8);
}

// Public fixtures for AIR export and generated Lean qualification.
export fn scalar(x: *E!u16) u16 { return x.* catch 0; }
export fn pair(x: *E!Pair) u16 { const p = x.* catch return 0; return p.first; }
export fn array(x: *E![2]u16) u16 { const p = x.* catch return 0; return p[1]; }
export fn writeScalar(x: *E!u16, value: u16) void { x.* = value; }
export fn payloadPointer(x: *E!u16) *u16 {
    return if (x.*) |*p| p else |_| unreachable;
}
comptime { _ = &scalar; _ = &pair; _ = &array; _ = &writeScalar; _ = &payloadPointer; }
