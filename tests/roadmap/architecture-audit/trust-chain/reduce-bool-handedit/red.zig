export fn anyLane(a: u32, b: u32) bool {
    const v: @Vector(2, u32) = .{ a, b };
    const zero: @Vector(2, u32) = @splat(0);
    return @reduce(.Or, v == zero);
}
