/// A user file that happens to be named like `std.atomic`. Its fully qualified
/// names collide with std's (`atomic.spinLoopHint`).
pub fn spinLoopHint() void {
    @panic("user spinLoopHint always panics");
}
