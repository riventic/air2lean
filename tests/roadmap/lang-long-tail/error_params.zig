//! L10: error values as runtime parameters (`docs/generated-code.md` §Errors). A one-name error
//! set (`error{Boom}`) has a runtime value in every supported Zig version (Zig's
//! `Type.onePossibleValue` is null for every error set and error union), so its parameter has an
//! AIR `arg`, as `std.Io.Threaded`'s `Syscall.fail(s, err: anytype)` instances need. The
//! functions are `pub` and referenced in a `comptime` block: error sets are not C ABI types.
pub const Boom = error{Boom};
pub const Two = error{ Left, Right };

/// The error `e` or `x`: a one-name error set parameter read at run time.
pub fn orBoom(x: u32, e: Boom) Boom!u32 {
    if (x == 0) return e;
    return x;
}

/// A generic instance with an `anytype` error, as `Syscall.fail`.
fn fail(tag: u32, err: anytype) @TypeOf(err)!u32 {
    if (tag == 0) return err;
    return tag + 1;
}

/// Calls the instance with a one-name error set (`error{Boom}`) and the one with two names.
pub fn viaFail(x: u32) u32 {
    const a = fail(x, error.Boom) catch return 100;
    const b = fail(x -% 1, @as(Two, error.Right)) catch |e| return switch (e) {
        error.Left => 200,
        error.Right => 201,
    };
    return a + b;
}

/// An error union parameter with an empty error set: one runtime value per payload.
pub fn unwrapEmpty(r: error{}!u32) u32 {
    const v = r catch unreachable;
    return v;
}

/// An unused one-name error set parameter before a used one: the `arg`s keep their slots.
pub fn skipFirst(_: Boom, x: u32) u32 {
    return x *% 3;
}

/// Passes the one-name error on through a second call.
pub fn forward(x: u32) Boom!u32 {
    return orBoom(x, error.Boom);
}

comptime {
    _ = &orBoom;
    _ = &viaFail;
    _ = &unwrapEmpty;
    _ = &skipFirst;
    _ = &forward;
}
