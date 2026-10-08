//! L09 lane reads through a vector pointer: `v.*[i]` of a bit-packed vector. 0.16.0 exports
//! `ptr_elem_ptr` (a lane pointer) then `load`, which the translator reads with `Zig.loadLane`;
//! 0.15.2 exports a whole-vector `load` then `array_elem_val`, which canonicalization leaves
//! unfolded for bit-packed lanes (never a byte-strided `ptr_elem_val`). `test_lane_reads.py`
//! checks both translations against the native values below, and that hand-made
//! `ptr_elem_val` reads and runtime-index lane pointers into bit-packed vectors are rejected
//! (Zig 0.16.0 itself rejects a runtime `v.*[i]`: "vector index not comptime known").
const std = @import("std");

const V3 = @Vector(8, u3);
const B5 = @Vector(5, bool);

export fn u3Read(v: *const V3) u8 {
    return v.*[5];
}

export fn boolRead(v: *const B5) bool {
    return v.*[3];
}

test "lane reads" {
    const v: V3 = .{ 0, 1, 2, 3, 4, 5, 6, 7 };
    const b: B5 = .{ false, true, false, true, false };
    try std.testing.expectEqual(@as(u8, 5), u3Read(&v));
    try std.testing.expect(boolRead(&b));
}
