//! Native values of `noreturn_variants.zig`; `NoreturnVariants/Proofs.lean` proves the same
//! values of the translation. Run with a stock Zig: `zig test native.zig`.
const std = @import("std");
const s = @import("noreturn_variants.zig");
const eq = std.testing.expectEqual;

test "noreturn variants" {
    try eq(@as(u32, 7), s.get(s.mk(7)));
    try eq(@as(u32, 8), s.roundTrip(7));
    try eq(@as(u32, 256), s.roundTrip(255));
    try eq(@as(u32, 9), s.memRoundTrip(7));
    try eq(@as(u32, 257), s.memRoundTrip(255));
    try eq(@as(u16, 500), s.vValue(s.mkV(500)));
    try eq(@as(u16, 0), s.vValue(s.mkV(0)));
    try eq(@as(u8, 3), s.vTag(500));
    try eq(@as(u8, 9), s.vTag(0));
    try eq(@as(u16, 1234), s.memV(1234));
    try eq(@as(u16, 0), s.memV(0));
    try eq(@as(u16, 65535), s.oneRoundTrip(65535));
    try eq(true, s.colorOf(1));
    try eq(false, s.colorOf(0));
    try eq(@as(u32, 6), s.holderRoundTrip(true, 5));
    try eq(@as(u32, 5), s.holderRoundTrip(false, 5));
    // The variant adds no payload bytes; the tag keeps its slot.
    try eq(8, @sizeOf(s.U));
    try eq(4, @sizeOf(s.V));
    // 0.16.0 stores no tag when only one variant can be active (`reject.zig`); 0.15.2 does.
    try eq(if (@import("builtin").zig_version.minor >= 16) 2 else 4, @sizeOf(s.One));
    try eq(1, @sizeOf(s.Mode));
}
