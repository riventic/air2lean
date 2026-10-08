// Exported roots force analysis without calling unsafe native operations.
export fn optional(p: *?*allowzero u8) bool { return p.* == null; }
export fn fixed() [*c]u8 { return @ptrFromInt(1); }
