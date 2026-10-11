pub fn main() void {
    var x: u32 = 0;
    _ = @atomicLoad(u32, &x, .acq_rel);
}
