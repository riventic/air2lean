//! L14 fixture requests: candidate source for AIR tags whose coverage disposition is
//! `emitted-unfixtured` (no selected golden or reviewed roadmap compiler export contains
//! them). `scripts/coverage.py` FIXTURE_REQUESTS maps each such tag to one function here.
//!
//! NOT EVIDENCE. Nothing here has been exported; the expected tags come from reading
//! Sema, not from an AIR dump. Export with a patched compiler (docs/coverage.md §L14):
//!
//!   ZIG_AIR_JSON_DIR=<empty dir> ZIG_AIR_JSON_FILTER=runtime_tags. \
//!     zig-air-<version>/bin/zig build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
//!     -target x86_64-linux -mcpu=baseline tests/roadmap/runtime-tags/runtime_tags.zig
//!
//! then commit the dump under tests/golden only through an example (examples/<name>) or a
//! reviewed COMPILER_FIXTURE_ROOTS entry with provenance, and regenerate coverage.

pub const Failure = error{ Bad, Other };
pub const Pair = struct { a: u32, b: u32 };
pub const Wide = struct { f0: u8, f1: u8, f2: u8, f3: u8, f4: u32 };
pub const Color = enum(u8) { red, green, blue };

// Integer arithmetic: add/sub/mul/shl_with_overflow, sub_wrap, sub_sat, mul_sat, shl_sat,
// shl, shl_exact, shr_exact, div_exact, xor.
export fn addOverflow(a: u32, b: u32) u32 {
    const r = @addWithOverflow(a, b);
    return r[0] ^ r[1];
}
export fn subOverflow(a: u32, b: u32) u32 {
    const r = @subWithOverflow(a, b);
    return r[0] ^ r[1];
}
export fn mulOverflow(a: u32, b: u32) u32 {
    const r = @mulWithOverflow(a, b);
    return r[0] ^ r[1];
}
export fn shlOverflow(a: u32, n8: u8) u32 {
    const n: u5 = @truncate(n8);
    const r = @shlWithOverflow(a, n);
    return r[0] ^ r[1];
}
export fn subWrap(a: u32, b: u32) u32 {
    return a -% b;
}
export fn subSat(a: u32, b: u32) u32 {
    return a -| b;
}
export fn mulSat(a: u32, b: u32) u32 {
    return a *| b;
}
export fn shlSat(a: u32, n8: u8) u32 {
    const n: u5 = @truncate(n8);
    return a <<| n;
}
export fn shlPlain(a: u32, n8: u8) u32 {
    const n: u5 = @truncate(n8);
    return a << n;
}
export fn shlExact(a: u32, n8: u8) u32 {
    const n: u5 = @truncate(n8);
    return @shlExact(a, n);
}
export fn shrExact(a: u32, n8: u8) u32 {
    const n: u5 = @truncate(n8);
    return @shrExact(a, n);
}
export fn divExact(a: u32, b: u32) u32 {
    return @divExact(a, b);
}
export fn xorBits(a: u32, b: u32) u32 {
    return a ^ b;
}

// Bit counting: clz, ctz, popcount, byte_swap, bit_reverse.
export fn leading(x: u32) u32 {
    return @clz(x);
}
export fn trailing(x: u32) u32 {
    return @ctz(x);
}
export fn population(x: u32) u32 {
    return @popCount(x);
}
export fn swapBytes(x: u32) u32 {
    return @byteSwap(x);
}
export fn reverseBits(x: u32) u32 {
    return @bitReverse(x);
}

// Many-pointer arithmetic and element reads: ptr_add, ptr_sub, ptr_elem_val.
export fn advance(p: [*]const u32, i: usize) [*]const u32 {
    return p + i;
}
export fn retreat(p: [*]const u32, i: usize) [*]const u32 {
    return p - i;
}
export fn manyElem(p: [*]const u32, i: usize) u32 {
    return p[i];
}

// Control: trap, ret (safety disabled), loop_switch_br + switch_dispatch.
export fn trapZero(x: u32) u32 {
    if (x == 0) @trap();
    return x;
}
export fn unsafeReturn(x: u32) u32 {
    @setRuntimeSafety(false);
    return x;
}
export fn dispatch(start: u32) u32 {
    var steps: u32 = 0;
    sw: switch (start) {
        0 => {
            steps += 1;
            continue :sw 1;
        },
        1 => {
            steps += 2;
            continue :sw 2;
        },
        else => return steps,
    }
}

// Call modifiers: call_always_tail, call_never_tail, call_never_inline.
fn tailTarget(x: u32) callconv(.c) u32 {
    return x +% 1;
}
fn helper(x: u32) u32 {
    return x +% 1;
}
export fn alwaysTail(x: u32) u32 {
    return @call(.always_tail, tailTarget, .{x});
}
export fn neverTail(x: u32) u32 {
    return @call(.never_tail, helper, .{x});
}
export fn neverInline(x: u32) u32 {
    return @call(.never_inline, helper, .{x});
}

// Errors and optionals: try_cold, try_ptr, try_ptr_cold, is_null, is_non_err_ptr,
// errunion_payload_ptr_set, error_name. The pointer forms follow try-pointers/try_pointers.zig.
pub fn coldTry(e: Failure!u8, on_error: *u32) Failure!u8 {
    errdefer {
        if (true) {
            @branchHint(.cold);
            on_error.* += 1;
        }
    }
    return try e;
}
pub fn tryPtr(cell: *Failure!u8) Failure!*u8 {
    return &(try cell.*);
}
pub fn tryPtrCold(cell: *Failure!u8, on_error: *u32) Failure!*u8 {
    errdefer {
        if (true) {
            @branchHint(.cold);
            on_error.* += 1;
        }
    }
    return &(try cell.*);
}
export fn isNull(p: ?*u32) bool {
    return p == null;
}
pub fn nonErrPtr(p: *Failure!u32) u32 {
    if (p.*) |*v| return v.* else |_| return 0;
}
pub fn setPayload(p: *Failure!Pair, a: u32) void {
    p.* = .{ .a = a, .b = a };
}
pub fn errorName(e: Failure) []const u8 {
    return @errorName(e);
}

// Booleans: bool_and (three runtime lengths), bool_or (slice alignment safety check).
pub fn threeWay(a: []const u32, b: []const u32, c: []const u32) u32 {
    var total: u32 = 0;
    for (a, b, c) |x, y, z| total +%= x +% y +% z;
    return total;
}
pub fn alignSlice(s: []u8) []align(4) u8 {
    return @alignCast(s);
}

// Floats: fptrunc, fpext, int_from_float (safety disabled), float_from_int.
export fn narrow(x: f64) f32 {
    return @floatCast(x);
}
export fn widen(x: f32) f64 {
    return x;
}
export fn truncUnsafe(x: f64) u32 {
    @setRuntimeSafety(false);
    return @intFromFloat(x);
}
export fn toFloat(x: u32) f64 {
    return @floatFromInt(x);
}

// Aggregates and pointers: struct_field_ptr, slice, ptr_slice_len_ptr, ptr_slice_ptr_ptr,
// slice_elem_ptr, array_to_slice, aggregate_init, tag_name.
export fn fieldPtr(s: *Wide) *u32 {
    return &s.f4;
}
pub fn subSlice(xs: []const u32, lo: usize, hi: usize) []const u32 {
    return xs[lo..hi];
}
pub fn setLen(p: *[]const u32, n: usize) void {
    p.len = n;
}
pub fn setPtr(p: *[]const u32, q: [*]const u32) void {
    p.ptr = q;
}
pub fn elemPtr(xs: []u32, i: usize) *u32 {
    return &xs[i];
}
pub fn arraySlice(arr: *const [4]u32) []const u32 {
    return arr;
}
pub fn makePair(a: u32, b: u32) [2]u32 {
    return .{ a, b };
}
pub fn colorName(c: Color) []const u8 {
    return @tagName(c);
}

// Vectors: splat, shuffle.
pub fn splatLanes(x: u32) @Vector(4, u32) {
    return @splat(x);
}
pub fn reverseLanes(v: @Vector(4, u32)) @Vector(4, u32) {
    return @shuffle(u32, v, undefined, [4]i32{ 3, 2, 1, 0 });
}

// Memory: memset (safety disabled), memset_safe, memcpy.
pub fn clearUnsafe(buf: []u8) void {
    @setRuntimeSafety(false);
    @memset(buf, 0);
}
pub fn clearSafe(buf: []u8) void {
    @memset(buf, 0);
}
pub fn copyBytes(dst: []u8, src: []const u8) void {
    @memcpy(dst, src);
}

// Atomics: cmpxchg_weak, cmpxchg_strong, atomic_load, atomic_store_{unordered,monotonic,
// release,seq_cst}, atomic_rmw.
export fn casWeak(p: *u32, old: u32, new: u32) bool {
    return @cmpxchgWeak(u32, p, old, new, .seq_cst, .seq_cst) == null;
}
export fn casStrong(p: *u32, old: u32, new: u32) bool {
    return @cmpxchgStrong(u32, p, old, new, .seq_cst, .seq_cst) == null;
}
export fn loadAcquire(p: *const u32) u32 {
    return @atomicLoad(u32, p, .acquire);
}
export fn storeUnordered(p: *u32, v: u32) void {
    @atomicStore(u32, p, v, .unordered);
}
export fn storeMonotonic(p: *u32, v: u32) void {
    @atomicStore(u32, p, v, .monotonic);
}
export fn storeRelease(p: *u32, v: u32) void {
    @atomicStore(u32, p, v, .release);
}
export fn storeSeqCst(p: *u32, v: u32) void {
    @atomicStore(u32, p, v, .seq_cst);
}
export fn fetchAdd(p: *u32, v: u32) u32 {
    return @atomicRmw(u32, p, .Add, v, .seq_cst);
}

// Force analysis of the non-C-ABI functions above.
comptime {
    _ = &coldTry;
    _ = &tryPtr;
    _ = &tryPtrCold;
    _ = &nonErrPtr;
    _ = &setPayload;
    _ = &errorName;
    _ = &threeWay;
    _ = &alignSlice;
    _ = &subSlice;
    _ = &setLen;
    _ = &setPtr;
    _ = &elemPtr;
    _ = &arraySlice;
    _ = &makePair;
    _ = &colorName;
    _ = &splatLanes;
    _ = &reverseLanes;
    _ = &clearUnsafe;
    _ = &clearSafe;
    _ = &copyBytes;
}
