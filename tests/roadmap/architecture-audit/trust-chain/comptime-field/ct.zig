const S = struct { v: u32, comptime k: u32 = 7 };

fn mk(v: u32) S {
    return .{ .v = v };
}

fn sum(s: S) u32 {
    return s.k + s.v;
}

export fn go(x: u32) u32 {
    var s = mk(x);
    s.v +%= 1;
    return sum(s);
}
