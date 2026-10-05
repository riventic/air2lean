// Exported roots force analysis without calling unsafe native operations.
export fn stored(p: *[*c]u8) [*c]u8 { return p.*; }
export fn fixed() [*c]u8 { return @ptrFromInt(1); }
