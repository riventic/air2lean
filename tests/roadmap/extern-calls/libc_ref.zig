//! Reference definitions of two libc symbols, compiled into the same AIR set as the program
//! that calls them through `extern` declarations. They stand in for translated musl code: the
//! translator binds an extern call to the `export fn` of the same symbol.

export fn memset(dest: [*]u8, c: c_int, n: usize) [*]u8 {
    const byte: u8 = @truncate(@as(c_uint, @bitCast(c)));
    var i: usize = 0;
    while (i < n) : (i += 1) dest[i] = byte;
    return dest;
}

export fn strlen(s: [*:0]const u8) usize {
    var i: usize = 0;
    while (s[i] != 0) : (i += 1) {}
    return i;
}
