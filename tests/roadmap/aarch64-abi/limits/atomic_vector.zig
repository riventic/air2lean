pub fn main() void {
    var x: @Vector(2, u32) = undefined;
    _ = @atomicLoad(@Vector(2, u32), &x, .seq_cst);
}
