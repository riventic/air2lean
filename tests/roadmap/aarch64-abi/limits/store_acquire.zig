pub fn main() void {
    var x: u32 = 0;
    @atomicStore(u32, &x, 1, .acquire);
}
