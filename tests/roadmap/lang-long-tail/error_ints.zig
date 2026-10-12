//! L10: integer/error casts (`@intFromError`, `@errorFromInt`) over the compilation's error
//! numbering, which the patched compiler exports after analysis (`error-table.air2lean`,
//! `docs/air-json.md` §Error table). The width is the profile's (`--error-limit`).
pub const E = error{ Alpha, Beta, Gamma };

/// The error integer of this compilation (`u16` by default).
pub const Code = @TypeOf(@intFromError(error.Alpha));

/// The code of `e` in the compilation's numbering.
pub fn code(e: E) Code {
    return @intFromError(e);
}

/// The error of code `c`; code 0 and codes without an error are the safety panic
/// `invalid error code`.
pub fn back(c: Code) anyerror {
    return @errorFromInt(c);
}

/// The name of the error of code `c` (`@errorName` of `@errorFromInt`).
pub fn nameOf(c: Code) []const u8 {
    return @errorName(@errorFromInt(c));
}

/// The round trip through the integer keeps the error.
pub fn roundTrip(e: E) bool {
    return @errorFromInt(@intFromError(e)) == e;
}

/// A code stored in memory as an integer and read back as an error.
pub fn viaMemory(e: E) bool {
    var cells: [2]Code = .{ @intFromError(e), 0 };
    cells[1] = cells[0];
    return @errorFromInt(cells[1]) == e;
}

comptime {
    _ = &code;
    _ = &back;
    _ = &nameOf;
    _ = &roundTrip;
    _ = &viaMemory;
}
