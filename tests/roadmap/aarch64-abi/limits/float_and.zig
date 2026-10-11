pub fn main() void {
    var x: f32 = 0;
    _ = @atomicRmw(f32, &x, .And, 1, .seq_cst);
}
