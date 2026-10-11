// The root and std modules both have a function `ascii.isDigit`. Both are exported under
// their historical file name `ascii.isDigit.json`, so the exporter must fail closed.
const std = @import("std");
const ascii = @import("ascii.zig");

export fn entry(c: u8) bool {
    return std.ascii.isDigit(c) or ascii.isDigit(c);
}
