pub fn main() void {
    var x: [2]u8 = undefined;
    _ = @atomicLoad([2]u8, &x, .seq_cst);
}
