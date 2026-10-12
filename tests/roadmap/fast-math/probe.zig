// F03 probe: what @setFloatMode(.optimized) changes natively (docs/research/F03.md).
//
// Built as a shared library and driven by `scripts/fast-math-probe.py` (ctypes). Every case exists twice,
// `<name>.strict` and `<name>.fast`: the same function body, with `@setFloatMode(.strict)` or
// `@setFloatMode(.optimized)`. Operands are runtime values (a global the compiler cannot see
// through), so nothing is folded at comptime. The file builds with Zig 0.14.1 to 0.17.0.

var seed: u64 = 0;

fn opq(bits: u64) u64 {
    return bits ^ @as(*volatile u64, &seed).*;
}

fn f(bits: u64) f64 {
    return @bitCast(opq(bits));
}

fn bitsOf(x: f64) u64 {
    return @bitCast(x);
}

const nan: u64 = 0x7ff8000000000000;
const inf: u64 = 0x7ff0000000000000;
const neg_zero: u64 = 0x8000000000000000;

// reassoc: a reduction the vectorizer may reorder. 1e16 + 1.0 rounds to 1e16, so the strict
// left-to-right sum of [1e16, 1, 1, ..., -1e16] is 0; any other association gives another value.
fn sumCase(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    var xs: [64]f64 = undefined;
    for (&xs, 0..) |*x, i| x.* = if (i == 0) f(0x4341c37937e08000) else if (i == 63) f(0xc341c37937e08000) else f(0x3ff0000000000000);
    var s: f64 = 0;
    for (xs) |x| s += x;
    return bitsOf(s);
}

// reassoc, with small strict intermediates: [1e16, -1e16, 1, ..., 1] sums to 62 left to right (the
// partial sums are 0, 1, ..., 62). A reordering that adds the 1s to 1e16 or -1e16 first loses them,
// so a relation that bounds each result by the *operands of that operation* (here at most 62) is
// unsound: the leaves' magnitudes (1e16) are what bound every reassociation.
fn sumCancel(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    var xs: [64]f64 = undefined;
    for (&xs, 0..) |*x, i| x.* = if (i == 0) f(0x4341c37937e08000) else if (i == 1) f(0xc341c37937e08000) else f(0x3ff0000000000000);
    var s: f64 = 0;
    for (xs) |x| s += x;
    return bitsOf(s);
}

// contract: a*b + c with a = 1 + 2^-27, b = 1 - 2^-27, c = -1. a*b = 1 - 2^-54 is a tie that
// rounds to 1, so strict gives 0 and a fused multiply-add gives -2^-54.
fn fmaShape(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    const a = f(0x3ff0000002000000);
    const b = f(0x3feffffffc000000);
    const c = f(0xbff0000000000000);
    return bitsOf(a * b + c);
}

// nnan: a NaN test. Under nnan a NaN operand is poison, so `x != x` may be folded to false.
fn selfNe(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    const x = f(nan);
    return @intFromBool(x != x);
}

// nnan: `<` with a NaN operand.
fn nanLt(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    const x = f(nan);
    const y = f(0x3ff0000000000000);
    return @intFromBool(x < y);
}

// ninf: an infinity test. Under ninf an infinite operand is poison, so `x > max` may be folded.
fn gtMax(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    const x = f(inf);
    return @intFromBool(x > 1.7976931348623157e308);
}

// ninf: `x == inf`.
fn eqInf(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return @intFromBool(f(inf) == @as(f64, @bitCast(@as(u64, inf))));
}

// nsz: x * 0 for x = -1 is -0.0 strictly; with nsz (and nnan, ninf) it may fold to +0.0.
fn mulZero(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(0xbff0000000000000) * 0.0);
}

// nnan + ninf: the same fold changes the result for an infinite or NaN operand.
fn mulZeroNan(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(inf) * 0.0);
}

// nsz: x + 0.0 for x = -0.0: +0.0 strictly; the add may be removed under nsz.
fn addZero(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(neg_zero) + 0.0);
}

// arcp: x / 3.0 may become x * (1/3.0), one rounding more.
fn divThree(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(0x4059000000000000 + 0x0123456789) / 3.0);
}

// Division by zero: IEEE inf strictly; a safety panic for floats in optimized mode where
// safety is on (Sema addDivByZeroSafety), unspecified (nnan/ninf poison) in ReleaseFast.
fn divZero(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(0x3ff0000000000000) / f(0));
}

// 0/0: NaN strictly; with safety on, the same panic.
fn divZeroZero(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(f(0) / f(0));
}

// An operation with no `_optimized` AIR tag: @sqrt of a negative operand is NaN either way.
fn sqrtNeg(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(@sqrt(f(0xbff0000000000000)));
}

// @mulAdd is one fused operation in both modes: contraction cannot change it.
fn mulAddCase(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(@mulAdd(f64, f(0x3ff0000002000000), f(0x3feffffffc000000), f(0xbff0000000000000)));
}

// x - x for x = inf: NaN strictly; with ninf, may fold to 0.
fn subSelf(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    const x = f(inf);
    return bitsOf(x - x);
}

// @intFromFloat after a rounding division: the optimized tag changes the conversion's flags, not
// its domain.
fn divTrunc(comptime fast: bool) u64 {
    @setFloatMode(if (fast) .optimized else .strict);
    return bitsOf(@divTrunc(f(0x4059000000000000), f(0x4008000000000000)));
}

const Case = struct { name: [:0]const u8, run: *const fn () u64 };

fn mk(comptime func: fn (comptime bool) u64, comptime fast: bool) *const fn () u64 {
    return &struct {
        fn run() u64 {
            return func(fast);
        }
    }.run;
}

const names = .{
    .{ "sum", sumCase },
    .{ "sum_cancel", sumCancel },
    .{ "fma_shape", fmaShape },
    .{ "self_ne", selfNe },
    .{ "nan_lt", nanLt },
    .{ "gt_max", gtMax },
    .{ "eq_inf", eqInf },
    .{ "mul_zero", mulZero },
    .{ "mul_zero_nan", mulZeroNan },
    .{ "add_zero", addZero },
    .{ "div_three", divThree },
    .{ "div_zero", divZero },
    .{ "div_zero_zero", divZeroZero },
    .{ "sqrt_neg", sqrtNeg },
    .{ "mul_add", mulAddCase },
    .{ "sub_self", subSelf },
    .{ "div_trunc", divTrunc },
};

const cases = blk: {
    var arr: [names.len * 2]Case = undefined;
    for (names, 0..) |n, i| {
        arr[2 * i] = .{ .name = n[0] ++ ".strict", .run = mk(n[1], false) };
        arr[2 * i + 1] = .{ .name = n[0] ++ ".fast", .run = mk(n[1], true) };
    }
    break :blk arr;
};

export fn fm_count() usize {
    return cases.len;
}

export fn fm_name(i: usize) [*:0]const u8 {
    return @ptrCast(cases[i].name.ptr);
}

export fn fm_run(i: usize) u64 {
    return cases[i].run();
}
