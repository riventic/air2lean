const storage = @import("storage.zig");
const empty: storage.Failure!void = {};
pub fn zeroPayload() *const void { return &(empty catch unreachable); }
pub fn volatilePayload() *volatile const u8 { return storage.small_ptr; }
comptime { _ = &zeroPayload; _ = &volatilePayload; }
