//! Probe (Zig 0.16.0, 0.17.1): a bare union reified with `@Union` gets the safety tag like a
//! declared one (Sema `zirReifyUnion`, `wantSafeTypes`). Companion of `safety-layout-probe.zig`.
const std = @import("std");

const R = @Union(.auto, null, &.{ "int", "small" }, &.{ u32, u8 }, &@splat(.{}));

pub fn main() void {
    std.debug.print("mode {s}\nreified bare union (@Union) size {d}\n", .{ @tagName(@import("builtin").mode), @sizeOf(R) });
}
