//! Source of the shiftRhsTooBig CLI regression fixtures (test_cli.py), exported with runtime
//! safety on. u40's shift count type u6 holds 40..63, so `<<` and `>>` carry Zig's
//! `shiftRhsTooBig` safety check; u64's count type u6 cannot exceed the width (no check).
pub export fn shl40(x: u64, n: u8) u64 {
    const a: u40 = @truncate(x);
    return a << @as(u6, @truncate(n));
}

pub export fn shr40(x: u64, n: u8) u64 {
    const a: i40 = @bitCast(@as(u40, @truncate(x)));
    return @as(u40, @bitCast(a >> @as(u6, @truncate(n))));
}

pub export fn shl64(x: u64, n: u8) u64 {
    return x << @as(u6, @truncate(n));
}
