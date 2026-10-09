const std = @import("std");
const Io = std.Io;

fn square(x: u32) u32 {
    return x *% x;
}

const Fail = error{Zero};

fn checked(x: u32) Fail!u32 {
    if (x == 0) return error.Zero;
    return x - 1;
}

fn fill(out: *u32, v: u32) void {
    out.* = v;
}

fn cancellable(io: Io, x: u32) Io.Cancelable!u32 {
    try io.checkCancel();
    return x +% 1;
}

pub fn awaitValue(io: Io, x: u32) u32 {
    var f = io.async(square, .{x});
    return f.await(io);
}

pub fn awaitError(io: Io, x: u32) Fail!u32 {
    var f = io.async(checked, .{x});
    return f.await(io);
}

pub fn awaitOwned(io: Io, v: u32) u32 {
    var out: u32 = 0;
    var f = io.async(fill, .{ &out, v });
    f.await(io);
    return out;
}

pub fn cancelValue(io: Io, x: u32) Io.Cancelable!u32 {
    var f = io.async(cancellable, .{ io, x });
    return f.cancel(io);
}

pub fn awaitTwice(io: Io, x: u32) u32 {
    var f = io.async(square, .{x});
    const a = f.await(io);
    const b = f.await(io);
    return a +% b;
}

comptime {
    _ = &awaitValue;
    _ = &awaitError;
    _ = &awaitOwned;
    _ = &cancelValue;
    _ = &awaitTwice;
}
