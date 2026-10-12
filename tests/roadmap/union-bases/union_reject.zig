//! L06 union-member constant bases that stay outside the model (air-reject/<version>,
//! test_cli.py): each export must be rejected with the recorded diagnostic.
const std = @import("std");

pub const Failure = error{Bad};
/// An explicitly aligned member: the compiler puts the payload first (alignment 4 > 1), the
/// model's natural layout would put the tag first. The exporter writes `union_field`.
pub const Odd = union(enum) { a: u8 align(4), b: u8 };
pub const odd: Odd = .{ .b = 7 };
pub fn oddPtr() *const u8 {
    return &odd.b;
}

/// A member with error storage: symbolic error bytes inside a union member.
pub const Res = union(enum) { res: Failure!u32, raw: u32 };
pub const res: Res = .{ .res = 5 };
pub fn resPtr() *const Failure!u32 {
    return &res.res;
}

comptime {
    _ = &oddPtr; _ = &resPtr;
}
