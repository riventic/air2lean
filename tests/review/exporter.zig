// Compiler-exporter regressions, dumped with -fno-emit-bin. No native execution required.
const Node = struct { next: ?*Node, x: u32 };
export fn lazySize(n: usize) usize {
    return n + @sizeOf(Node);
}
export fn lazyAlign(n: usize) usize {
    return n + @alignOf(Node);
}

const E = enum(u2) { a = 0, b = 1, c = 2 };
const Packed = packed struct { e: E, x: u6 };
const packed_value: Packed = .{ .e = .b, .x = 17 };
pub fn packedConstant() Packed {
    return packed_value;
}
export fn packedRead(n: u8) u8 {
    return n + @intFromEnum(packedConstant().e);
}

const Inner = packed struct { signed: i3, flag: bool };
const Nested = packed struct { inner: Inner, x: u4 };
const nested_value: Nested = .{ .inner = .{ .signed = -2, .flag = true }, .x = 9 };
pub fn nestedConstant() Nested {
    return nested_value;
}
export fn nestedRead(n: i8) i8 {
    return n + nestedConstant().inner.signed;
}

pub fn leadingVoid(_: void, n: u32) u32 {
    return n + 1;
}
pub fn leadingZero(_: u0, n: u32) u32 {
    return n + 2;
}
pub fn genericVoid(comptime T: type, _: void, n: T) T {
    return n + 3;
}
export fn callVoid(n: u32) u32 {
    return leadingVoid({}, n);
}
export fn callZero(n: u32) u32 {
    return leadingZero(0, n);
}
export fn callGenericVoid(n: u32) u32 {
    return genericVoid(u32, {}, n);
}
