const storage = @import("storage.zig");
const equal: storage.Failure!u16 = 23;
pub fn equalAlignment() *const u16 { return &(equal catch unreachable); }
pub fn volatilePayload() *volatile const u8 { return storage.small_ptr; }
comptime { _ = &equalAlignment; _ = &volatilePayload; }
