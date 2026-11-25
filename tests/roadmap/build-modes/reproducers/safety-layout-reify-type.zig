//! Probe (Zig 0.14.1, 0.15.2): a bare union reified with `@Type` gets the safety tag like a
//! declared one (Sema `zirReify`, `wantSafeTypes`). Companion of `safety-layout-probe.zig`.
const std = @import("std");

const R = @Type(.{ .@"union" = .{
    .layout = .auto,
    .tag_type = null,
    .fields = &.{
        .{ .name = "int", .type = u32, .alignment = @alignOf(u32) },
        .{ .name = "small", .type = u8, .alignment = @alignOf(u8) },
    },
    .decls = &.{},
} });

pub fn main() void {
    std.debug.print("mode {s}\nreified bare union (@Type) size {d}\n", .{ @tagName(@import("builtin").mode), @sizeOf(R) });
}
