const std = @import("std");

/// Byte-buffer source lowering probe, not a qualified allocator feature.
/// The frame is allocated before the buffer, so the resized buffer is latest.
pub fn exercise(a: std.mem.Allocator) !u32 {
    const frame = try a.alloc(u8, 1);
    defer a.free(frame);
    frame[0] = 41;
    var bytes = try a.alloc(u8, 4);
    defer a.free(bytes);
    bytes[0] = 3;
    bytes[1] = 5;
    bytes[2] = 7;
    bytes[3] = 11;
    var outcome: u32 = 3;
    if (a.remap(bytes, 8)) |grown| {
        outcome = if (grown.ptr == bytes.ptr) 1 else 2;
        bytes = grown;
        bytes[4] = 13;
        bytes[5] = 13;
        bytes[6] = 13;
        bytes[7] = 13;
    }
    if (bytes[0] != 3 or bytes[1] != 5 or bytes[2] != 7 or bytes[3] != 11 or frame[0] != 41)
        return 0;
    if (outcome != 3 and (bytes.len != 8 or bytes[4] != 13 or bytes[5] != 13 or bytes[6] != 13 or bytes[7] != 13))
        return 0;
    if (outcome == 3 and bytes.len != 4) return 0;
    return 100 * outcome + 1;
}

comptime { _ = &exercise; }
