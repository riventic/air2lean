//! T05: one source compiled for a native target (a shared library driven by Python ctypes) and
//! for wasm32-freestanding (driven by Node). Every export takes and returns `u64` words: signed
//! values and float bit patterns are `@bitCast` inside, so both drivers pass plain integers.
//! A safety panic is the observation `trap` (native: the process dies on a signal; wasm: the
//! `unreachable` trap). `relation.json` gives each export its observation class. The source
//! uses only language features that Zig 0.14.1 to 0.17.0 share.
const std = @import("std");
const pw = @import("pointer_width");

/// The error sentinel of the encodings below (`maxInt(u64)`).
const none: u64 = std.math.maxInt(u64);

// ---------------------------------------------------------------- discrete-event kernels (exact)

/// Flow's `addDuration` rule (case-studies/flow-time): the maximum value is reserved, so the
/// sum is representable only below it.
fn addDuration(comptime T: type, base: T, duration: T) error{TimeOverflow}!T {
    const r = @addWithOverflow(base, duration);
    if (r[1] != 0 or r[0] == std.math.maxInt(T)) return error.TimeOverflow;
    return r[0];
}

/// `addDuration(u32)`: the sum, or `none` for `error.TimeOverflow`.
export fn des_time_add32(base: u64, duration: u64) u64 {
    return addDuration(u32, @truncate(base), @truncate(duration)) catch none;
}

/// `addDuration(u64)`: the sum, or `none` for `error.TimeOverflow` (the reserved value).
export fn des_time_add64(base: u64, duration: u64) u64 {
    return addDuration(u64, base, duration) catch none;
}

/// Event order: earlier time first, then lower sequence number.
export fn des_event_before(t1: u64, s1: u64, t2: u64, s2: u64) u64 {
    return @intFromBool(t1 < t2 or (t1 == t2 and @as(u32, @truncate(s1)) < @as(u32, @truncate(s2))));
}

const Event = struct { time: u64, seq: u32 };

fn before(a: Event, b: Event) bool {
    return a.time < b.time or (a.time == b.time and a.seq < b.seq);
}

/// A binary-heap event queue: `n % 33` events with xorshift times are pushed, then popped in
/// order; the result folds the popped sequence (FNV-1a), or `none` if the order is violated.
export fn des_queue_drain(seed: u64, n: u64) u64 {
    var heap: [32]Event = undefined;
    var len: usize = 0;
    var x = seed | 1;
    const count: u32 = @intCast(n % 33);
    var seq: u32 = 0;
    while (seq < count) : (seq += 1) {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        // Few distinct times, so ties exercise the sequence order.
        heap[len] = .{ .time = x % 8, .seq = seq };
        var i = len;
        len += 1;
        while (i > 0) {
            const parent = (i - 1) / 2;
            if (!before(heap[i], heap[parent])) break;
            const t = heap[i];
            heap[i] = heap[parent];
            heap[parent] = t;
            i = parent;
        }
    }
    var hash: u64 = 0xcbf29ce484222325;
    var last: ?Event = null;
    while (len > 0) {
        const top = heap[0];
        len -= 1;
        heap[0] = heap[len];
        var i: usize = 0;
        while (true) {
            const l = 2 * i + 1;
            const r = l + 1;
            var m = i;
            if (l < len and before(heap[l], heap[m])) m = l;
            if (r < len and before(heap[r], heap[m])) m = r;
            if (m == i) break;
            const t = heap[i];
            heap[i] = heap[m];
            heap[m] = t;
            i = m;
        }
        if (last) |prev| if (before(top, prev)) return none;
        last = top;
        hash = (hash ^ (top.time << 32 | top.seq)) *% 0x100000001b3;
    }
    return hash;
}

// ---------------------------------------------------------------- integer kernels (exact)

/// Wrapping arithmetic, rotates, bit counts, byte swaps and a 128-bit product.
export fn int_mix(a: u64, b: u64) u64 {
    const lo: u32 = @truncate(a);
    const h: u16 = @truncate(b);
    const wide = @as(u128, a) * @as(u128, b);
    var r: u64 = @truncate(wide >> 64);
    r ^= std.math.rotl(u64, a, @as(u7, @truncate(b % 64))) +% (b *% 0x9e3779b97f4a7c15);
    r +%= @as(u64, @clz(a)) | @as(u64, @ctz(b)) << 8 | @as(u64, @popCount(a ^ b)) << 16;
    r ^= @as(u64, @byteSwap(lo)) << 24 ^ @bitReverse(b);
    r -%= @as(u64, @byteSwap(h)) *% @as(u64, @as(u7, @truncate(a)));
    return r;
}

/// Signed division and modulus (`i64`): division by zero and `minInt / -1` panic.
export fn int_divmod(a: u64, b: u64) u64 {
    const x: i64 = @bitCast(a);
    const y: i64 = @bitCast(b);
    const q = @divTrunc(x, y);
    const m = @mod(x, y);
    return @bitCast(q *% 31 +% m);
}

/// Checked `u64` addition: overflow panics.
export fn int_add_checked(a: u64, b: u64) u64 {
    return a + b;
}

/// Checked shift: a shift amount of at least 64 panics.
export fn int_shl_exact(a: u64, b: u64) u64 {
    return std.math.shl(u64, a, b) ^ (a << @intCast(b));
}

// ---------------------------------------------------------------- pointer-width kernels (target-specific)

/// `@bitSizeOf(usize)`: 64 natively, 32 on wasm32.
export fn usize_bits() u64 {
    return @bitSizeOf(usize);
}

/// `pointer_width.byteCount` (T02) on `n` as a `usize`: `none` when `n` does not fit a `usize`
/// or `4 * n` overflows it.
export fn pw_byte_count(n: u64) u64 {
    const u = std.math.cast(usize, n) orelse return none;
    return pw.byteCount(u) orelse none;
}

/// `pointer_width.succ` (T02) on `n` truncated to a `usize`: panics at `maxInt(usize)`.
export fn pw_succ(n: u64) u64 {
    return pw.succ(@truncate(n));
}

// ---------------------------------------------------------------- float kernels (tolerated)

fn f64of(x: u64) f64 {
    return @bitCast(x);
}

/// `a * b + a / b - b` in `f64` (separately rounded IEEE operations).
export fn f64_arith(a: u64, b: u64) u64 {
    const x = f64of(a);
    const y = f64of(b);
    return @bitCast(x * y + x / y - y);
}

/// `@sqrt` (correctly rounded).
export fn f64_sqrt(a: u64) u64 {
    return @bitCast(@sqrt(f64of(a)));
}

/// `@mulAdd` on `f32` (fused: one rounding).
export fn f32_fma(a: u64, b: u64, c: u64) u64 {
    const x: f32 = @bitCast(@as(u32, @truncate(a)));
    const y: f32 = @bitCast(@as(u32, @truncate(b)));
    const z: f32 = @bitCast(@as(u32, @truncate(c)));
    return @as(u32, @bitCast(@mulAdd(f32, x, y, z)));
}

/// `@sin`: a libm call whose implementation is the target's (not correctly rounded).
export fn f64_sin(a: u64) u64 {
    return @bitCast(@sin(f64of(a)));
}

/// `@intFromFloat` to `i64`: a NaN or out-of-range operand panics.
export fn f64_to_i64(a: u64) u64 {
    const r: i64 = @intFromFloat(f64of(a));
    return @bitCast(r);
}
