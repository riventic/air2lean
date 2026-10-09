//! Bounded integer/pointer/layout observations; no float or synchronization qualification.
const std = @import("std");
const builtin = @import("builtin");
const compat = @import("compat");
const Packed = packed struct(u32) { low: u9, high: u23 };
const Record = extern struct { tag: u8, count: u32, pointer: *const u32 };
fn rt(comptime T: type, value: T) T {
    var storage = value;
    const pointer: *volatile T = &storage;
    return pointer.*;
}
/// `builtin.mode` in the 0.16.0 tag spelling (`ReleaseSafe`), which scripts/abi-probe.py expects:
/// Zig 0.17.0 renamed the tags (`safe`) and kept the old names as declarations.
fn modeName() []const u8 {
    const Mode = @TypeOf(builtin.mode);
    inline for (.{ "Debug", "ReleaseSafe", "ReleaseFast", "ReleaseSmall" }) |name| {
        if (builtin.mode == @field(Mode, name)) return name;
    }
    unreachable;
}
/// The in-memory bytes of `value` (at most 8) as a little-endian integer, without the padding
/// bits past `@bitSizeOf(T)`.
fn image(comptime T: type, value: *const T) u64 {
    const bytes: *const volatile [@sizeOf(T)]u8 = @ptrCast(value);
    var result: u64 = 0;
    for (0..@sizeOf(T)) |i| result |= @as(u64, bytes[i]) << @intCast(8 * i);
    return result & ((@as(u64, 1) << @bitSizeOf(T)) - 1);
}
/// Output collected with std.fmt.bufPrint and written with compat.write: the same code
/// builds on Zig 0.14.1 (no std.Io.Writer), 0.15.2 and 0.16.0.
const Out = struct {
    buffer: [16384]u8 = undefined,
    len: usize = 0,
    fn print(self: *Out, comptime format: []const u8, args: anytype) !void {
        self.len += (try std.fmt.bufPrint(self.buffer[self.len..], format, args)).len;
    }
    fn flush(self: *Out) !void {
        var done: usize = 0;
        while (done < self.len) {
            const written = try compat.write(1, self.buffer[done..self.len]);
            if (written == 0) return error.BrokenPipe;
            done += written;
        }
    }
};
fn layout(out: *Out, comptime name: []const u8, comptime T: type) !void {
    try out.print("layout {s} {d} {d}\n", .{ name, @sizeOf(T), @alignOf(T) });
}
pub fn main() !void {
    var output: Out = .{};
    const out = &output;
    try out.print("meta arch {s}\nmeta os {s}\nmeta abi {s}\nmeta endian {s}\n", .{
        @tagName(builtin.cpu.arch), @tagName(builtin.os.tag), @tagName(builtin.abi),
        @tagName(builtin.cpu.arch.endian()),
    });
    try out.print("meta backend {s}\nmeta mode {s}\nmeta cpu {s}\nmeta zig {s}\n", .{
        @tagName(builtin.zig_backend), modeName(), builtin.cpu.model.name,
        builtin.zig_version_string,
    });
    try out.print("meta pointer_bits {d}\n", .{@bitSizeOf(usize)});
    try out.print("meta error_set_bits {d}\nmeta error_tracing {}\n", .{
        // Observe the current trace in main's !void error-return context. Zig 0.16
        // exposes this builtin, not a builtin.error_return_tracing declaration.
        @bitSizeOf(anyerror), @errorReturnTrace() != null,
    });
    for (builtin.cpu.arch.allFeaturesList()) |feature| {
        if (builtin.cpu.features.isEnabled(feature.index))
            try out.print("feature {s} 1\n", .{feature.name});
    }
    inline for (.{ u9, u24, u40, u128 }) |T| try layout(out, @typeName(T), T);
    try layout(out, "pointer", *const u32);
    try layout(out, "packed32", Packed);
    try layout(out, "vector4", @Vector(4, u32));
    try layout(out, "vector_u9x4", @Vector(4, u9));
    try layout(out, "vector_u24x3", @Vector(3, u24));
    try layout(out, "vector_u40x2", @Vector(2, u40));
    try layout(out, "vector_bool5", @Vector(5, bool));
    try layout(out, "record", Record);
    try out.print("offset record_count {d}\noffset record_pointer {d}\n", .{
        @offsetOf(Record, "count"), @offsetOf(Record, "pointer"),
    });
    const odd = rt(u24, 0xffffff) +% rt(u24, 2);
    const packed_value = Packed{ .low = rt(u9, 257), .high = rt(u23, 3) };
    const vector: @Vector(4, u32) = .{ rt(u32, 1), rt(u32, 2), rt(u32, 3), rt(u32, 4) };
    // Bit-packed lanes: lane i at bit i * @bitSizeOf(lane), and a lane store keeps the others.
    var nine: @Vector(4, u9) = .{ rt(u9, 0x1ff), rt(u9, 0), rt(u9, 0x1ff), rt(u9, 1) };
    const nine_image = image(@Vector(4, u9), &nine);
    const nine_lane = &nine[2];
    nine_lane.* = rt(u9, 0x0aa);
    var pair: @Vector(2, u24) = .{ rt(u24, 0xabcdef), rt(u24, 0x123456) };
    try out.print("value vector_u9_image {d}\nvalue vector_u9_lane_write {d}\nvalue vector_u24_image {d}\n", .{
        nine_image, image(@Vector(4, u9), &nine), image(@Vector(2, u24), &pair),
    });
    var value = rt(u32, 1234567);
    const pointer: *volatile u32 = &value;
    try out.print("value wrapping24 {d}\nvalue packed_bits {d}\nvalue vector_sum {d}\nvalue pointer_load {d}\n", .{
        odd, @as(u32, @bitCast(packed_value)), @reduce(.Add, vector), pointer.*,
    });
    try out.flush();
}
