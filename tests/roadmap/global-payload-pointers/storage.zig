pub const Failure = error{Bad};
pub const Payload = struct { guard: u32, value: u8 };
pub const Inner = struct {
    optional: ?Payload,
    small: Failure!u8,
    wide: Failure!u64,
};
pub const Outer = struct { before: u64, inner: Inner, after: u64 };
pub const frozen: Outer = .{
    .before = 0x0102030405060708,
    .inner = .{ .optional = .{ .guard = 0xabcdef01, .value = 7 }, .small = 19, .wide = 41 },
    .after = 0x1112131415161718,
};
pub var mutable: Outer = frozen;

pub const optional_ptr = &frozen.inner.optional.?.value;
pub const small_ptr = &(frozen.inner.small catch unreachable);
pub const wide_ptr = &(frozen.inner.wide catch unreachable);
