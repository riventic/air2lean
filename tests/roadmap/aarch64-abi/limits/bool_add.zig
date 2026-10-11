pub fn main() void {
    var x: bool = false;
    _ = @atomicRmw(bool, &x, .Add, true, .seq_cst);
}
