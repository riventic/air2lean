//! Uses of an opaque type that Zig compiles and the translator rejects (check.sh).
pub const Handle = opaque {};

// A variable of an opaque type exists only as an `extern`: its storage is unknown.
extern var global_handle: Handle;
pub noinline fn externHandle() *Handle {
    return &global_handle;
}

// An address is no provenance for the handle, as for `*anyopaque`.
pub noinline fn fromInt(a: usize) *Handle {
    return @ptrFromInt(a);
}

comptime {
    _ = &externHandle;
    _ = &fromInt;
}
