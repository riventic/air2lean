//! Fault-injected parent allocation must terminate and reap its owned child.
const std = @import("std");
const common = @import("common");
pub const panic = common.panic;

var control_pipe: [2]std.posix.fd_t = undefined;

fn blocked() u32 {
    _ = std.posix.system.close(control_pipe[1]);
    var byte: [1]u8 = undefined;
    _ = std.posix.read(control_pipe[0], &byte) catch @panic("control read failed");
    return 7;
}

pub fn main() !void {
    if (std.c.pipe(&control_pipe) != 0) return error.ControlPipeFailed;
    defer _ = std.posix.system.close(control_pipe[0]);
    defer _ = std.posix.system.close(control_pipe[1]);
    const outcome = common.forkCall(std.meta.ArgsTuple(@TypeOf(blocked)), .{}, blocked, false) catch |err| {
        if (err != error.OutOfMemory) return err;
        var status: c_int = undefined;
        const waited = std.c.waitpid(-1, &status, @intCast(std.posix.W.NOHANG));
        if (waited != -1 or std.posix.errno(waited) != .CHILD)
            return error.ChildNotReaped;
        return;
    };
    _ = outcome;
    return error.ParentAllocationUnexpectedSuccess;
}
