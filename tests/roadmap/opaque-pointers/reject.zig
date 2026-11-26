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

// A handle as a constant: the address of a global behind the opaque type. A constant pointer
// to a global needs the global's storage behind its pointee type, as for `*anyopaque`.
var backing: u32 = 5;
const backing_handle: *Handle = @ptrCast(&backing);
pub noinline fn globalHandle() *Handle {
    return backing_handle;
}

comptime {
    _ = &externHandle;
    _ = &fromInt;
    _ = &globalHandle;
}
