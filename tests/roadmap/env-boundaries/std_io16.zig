const std = @import("std");
const posix = std.posix;

fn readClose(fd: posix.fd_t, buf: []u8) posix.ReadError!usize {
    defer std.Io.Threaded.closeFd(fd);
    return posix.read(fd, buf);
}

comptime {
    _ = &readClose;
}
