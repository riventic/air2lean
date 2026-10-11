pub fn main() void {
    var x: u32 = 0;
    _ = @atomicRmw(u32, &x, .Add, 1, .unordered);
}
