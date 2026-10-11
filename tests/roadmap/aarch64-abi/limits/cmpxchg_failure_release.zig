pub fn main() void {
    var x: u32 = 0;
    _ = @cmpxchgStrong(u32, &x, 0, 1, .seq_cst, .release);
}
