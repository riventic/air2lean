//! Definitions of the two symbols abi_calls.zig declares with other types, in the style of
//! Zig's libc: `@export`ed, weak and hidden, with Zig types (`u8`, `[*:0]const c_char`).

comptime {
    @export(&fill, .{ .name = "abi_fill", .linkage = .weak, .visibility = .hidden });
    @export(&len, .{ .name = "abi_len", .linkage = .weak, .visibility = .hidden });
}

fn fill(dest: ?[*]u8, c: u8, n: usize) callconv(.c) ?[*]u8 {
    var i: usize = 0;
    while (i < n) : (i += 1) dest.?[i] = c;
    return dest;
}

fn len(s: [*:0]const c_char) callconv(.c) usize {
    var i: usize = 0;
    while (s[i] != 0) : (i += 1) {}
    return i;
}
