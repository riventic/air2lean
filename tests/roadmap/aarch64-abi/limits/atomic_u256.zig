pub fn main() void {
    var x: u256 = 0;
    _ = @atomicRmw(u256, &x, .Add, 1, .seq_cst);
}
