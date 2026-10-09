const std = @import("std");
const File = std.fs.File;

fn writeAllClose(file: File, bytes: []const u8) File.WriteError!void {
    defer file.close();
    try file.writeAll(bytes);
}

fn readAllClose(file: File, buf: []u8) File.ReadError!usize {
    defer file.close();
    return file.readAll(buf);
}

comptime {
    _ = &writeAllClose;
    _ = &readAllClose;
}
