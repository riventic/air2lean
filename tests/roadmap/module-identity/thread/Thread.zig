//! A user file named like `std.Thread`: its struct is `Thread` and its function
//! `Thread.spawn`, the fully qualified names of the std model's handle type and function.
const Thread = @This();

id: u32,

pub fn spawn(t: Thread, x: u32) u32 {
    return t.id +% x;
}
