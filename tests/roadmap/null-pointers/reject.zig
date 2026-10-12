// Exported roots force analysis without calling unsafe native operations.
// Zig 0.16.0/0.17.0 miscompile a cast of an optional nullable pointer (docs/upstream).
export fn optionalCast(p: *const ?*allowzero u8) ?*u8 { return @ptrCast(p.*); }
export fn fixed() [*c]u8 { return @ptrFromInt(1); }
