//! Zig 0.17.0 error/integer casts: the compiler-exported coverage fixture for the
//! `int_from_error` and `error_from_int` AIR tags (provenance.json). Export:
//!
//!   ZIG_AIR_JSON_DIR=<empty dir> ZIG_AIR_JSON_FILTER=casts. \
//!     zig-air-0.17.0/bin/zig build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
//!     -target x86_64-linux -mcpu=baseline tests/roadmap/zig017/casts/casts.zig
pub fn errorCode(e: anyerror) u16 {
    return @intFromError(e);
}
pub fn errorOfCode(code: u16) anyerror {
    return @errorFromInt(code);
}

comptime {
    _ = &errorCode;
    _ = &errorOfCode;
}
