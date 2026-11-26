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

// A global that holds a handle: the alias proof of a global needs the storage behind every
// pointer it can hold, and an opaque pointee has none to state, as for `?*anyopaque`.
var current: ?*Handle = null;
pub noinline fn setGlobal(h: ?*Handle) void {
    current = h;
}
pub noinline fn getGlobal() ?*Handle {
    return current;
}

// Erasing storage that can hold an error value: the bytes behind the handle would lose their
// symbolic errors, as for `*anyopaque`.
pub noinline fn eraseError(p: *anyerror!u32) *Handle {
    return @ptrCast(p);
}

comptime {
    _ = &setGlobal;
    _ = &getGlobal;
    _ = &eraseError;
    _ = &externHandle;
    _ = &fromInt;
    _ = &globalHandle;
}
