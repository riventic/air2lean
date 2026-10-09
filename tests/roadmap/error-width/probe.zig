//! L10 native error-width probe. Built with `--error-limit N` by `native.py`, it prints what the
//! compiler does with errors at that width: the integer's size and alignment, the byte image of
//! `E`, `?E` and `E!T`, where an error union keeps its code and payload, and (as a subprocess,
//! one panic per run) which integers `@errorFromInt` accepts. `Model.lean` prints the same lines
//! from `ZigLean/Mem/ErrWidth.lean`.
//!
//! It uses no `std` beyond `std.debug.no_panic`: `std` itself names hundreds of errors, which
//! would not fit a narrow `--error-limit`, and every `error.X` named here counts against it.
//! `errs.zig` (written by `native.py`) declares `Failure` (the set `error{ Bad, Other }`, or
//! `error{ Bad }` when `single`), its two members `a` and `b`, and the extra errors that bring the
//! compilation to a chosen total, the last of them `top`.
const std = @import("std");
const errs = @import("errs.zig");

pub const panic = std.debug.no_panic;

extern "c" fn write(fd: c_int, buf: [*]const u8, n: usize) isize;

const Failure = errs.Failure;
/// `u<error_set_bits>`: the integer `@intFromError` returns and `@errorFromInt` takes.
const Code = @TypeOf(@intFromError(errs.a));
const code_bytes = @sizeOf(Failure);
/// Bytes that hold the error integer's bits. Beyond them (17 to 24 bits in a 4-byte integer) a
/// byte is padding, which a store does not write: the probe compares only these bytes.
const defined = (@bitSizeOf(anyerror) + 7) / 8;

var obuf: [512]u8 = undefined;
var olen: usize = 0;

fn flush() void {
    _ = write(1, &obuf, olen);
    olen = 0;
}

fn ch(c: u8) void {
    if (olen == obuf.len) flush();
    obuf[olen] = c;
    olen += 1;
}

fn str(s: []const u8) void {
    for (s) |c| ch(c);
}

fn num(x: u64) void {
    if (x == 0) return ch('0');
    var tmp: [20]u8 = undefined;
    var i: usize = tmp.len;
    var v = x;
    while (v > 0) : (v /= 10) {
        i -= 1;
        tmp[i] = '0' + @as(u8, @intCast(v % 10));
    }
    str(tmp[i..]);
}

fn field(label: []const u8, x: u64) void {
    str(label);
    ch(' ');
    num(x);
    ch(' ');
}

fn eol() void {
    ch('\n');
}

/// Defeats constant folding: the value goes through memory the compiler must assume changes.
fn rt(comptime T: type, value: T) T {
    var storage = value;
    const pointer: *volatile T = &storage;
    return pointer.*;
}

fn putCode(dst: []u8, c: u64) void {
    for (0..code_bytes) |i| dst[i] = @truncate(c >> @intCast(8 * i));
}

fn bytesOf(comptime T: type, value: *const T) [@sizeOf(T)]u8 {
    const view: *const volatile [@sizeOf(T)]u8 = @ptrCast(value);
    var out: [@sizeOf(T)]u8 = undefined;
    for (0..@sizeOf(T)) |i| out[i] = view[i];
    return out;
}

/// The first `defined` bytes agree.
fn same(comptime n: usize, a: [n]u8, b: [n]u8) bool {
    for (0..@min(n, defined)) |i| if (a[i] != b[i]) return false;
    return true;
}

/// The payload bytes of a union agree (all of them).
fn sameAll(comptime n: usize, a: [n]u8, b: [n]u8) bool {
    for (0..n) |i| if (a[i] != b[i]) return false;
    return true;
}

fn allZero(comptime n: usize, a: [n]u8) bool {
    for (0..@min(n, defined)) |i| if (a[i] != 0) return false;
    return true;
}

fn flag(label: []const u8, ok: bool) void {
    str("enc ");
    str(label);
    ch(' ');
    ch(if (ok) '1' else '0');
    eol();
}

fn leOf(c: u64) [code_bytes]u8 {
    var out: [code_bytes]u8 = undefined;
    putCode(&out, c);
    return out;
}

/// The bytes of `E`, `?E` and the code integer.
fn encoding() void {
    const bad: u64 = @intFromError(errs.a);
    const other: u64 = @intFromError(errs.b);
    const top: u64 = @intFromError(errs.top);
    var e_bad: Failure = rt(Failure, errs.a);
    var e_other: Failure = rt(Failure, errs.b);
    var e_top: anyerror = rt(anyerror, errs.top);
    var o_null: ?Failure = rt(?Failure, null);
    var o_bad: ?Failure = rt(?Failure, errs.a);
    var o_top: ?anyerror = rt(?anyerror, errs.top);
    str("enc size ");
    num(@sizeOf(Failure));
    ch(' ');
    num(@alignOf(Failure));
    eol();
    str("enc defined ");
    num(defined);
    eol();
    str("enc anyerror ");
    num(@sizeOf(anyerror));
    ch(' ');
    num(@alignOf(anyerror));
    ch(' ');
    num(@bitSizeOf(anyerror));
    eol();
    str("enc optional ");
    num(@sizeOf(?Failure));
    ch(' ');
    num(@alignOf(?Failure));
    eol();
    flag("nonzero", bad != 0 and other != 0 and top != 0);
    flag("distinct", errs.single or (bad != other and bad != top));
    flag("le_code", same(code_bytes, bytesOf(Failure, &e_bad), leOf(bad)) and
        same(code_bytes, bytesOf(Failure, &e_other), leOf(other)) and
        same(code_bytes, bytesOf(anyerror, &e_top), leOf(top)));
    flag("null_zero", allZero(@sizeOf(?Failure), bytesOf(?Failure, &o_null)));
    flag("some_eq_plain", @sizeOf(?Failure) == code_bytes and
        same(code_bytes, bytesOf(?Failure, &o_bad), bytesOf(Failure, &e_bad)) and
        @sizeOf(?anyerror) == code_bytes and
        same(code_bytes, bytesOf(?anyerror, &o_top), bytesOf(anyerror, &e_top)));
    flag("roundtrip", @errorFromInt(@as(Code, @intCast(bad))) == errs.a and
        @errorFromInt(@as(Code, @intCast(top))) == errs.top);
    str("code Bad ");
    num(bad);
    str(" Other ");
    num(other);
    str(" top ");
    num(top);
    eol();
}

/// Where `Failure!T` keeps its code and payload: place the bytes of a code, or of a payload,
/// at every offset of zeroed memory and read the memory as the union. Only the true offset
/// reads back as the error `errs.a`, or as the payload.
fn eu(comptime name: []const u8, comptime T: type) void {
    const EU = Failure!T;
    const size = @sizeOf(EU);
    const psize = @sizeOf(T);
    var buf: [64]u8 align(16) = undefined;
    var code_off: i64 = -1;
    var pay_off: i64 = -1;
    var eo: usize = 0;
    while (eo + code_bytes <= size) : (eo += 1) {
        @memset(&buf, 0);
        putCode(buf[eo..], @intFromError(errs.a));
        const view: *const volatile EU = @ptrCast(@alignCast(&buf));
        const v = view.*;
        if (v) |_| {} else |e| {
            if (e == errs.a) code_off = @intCast(eo);
        }
    }
    if (psize > 0) {
        var po: usize = 0;
        while (po + psize <= size) : (po += 1) {
            @memset(&buf, 0);
            for (0..psize) |i| buf[po + i] = 0xa5;
            const view: *const volatile EU = @ptrCast(@alignCast(&buf));
            const v = view.*;
            if (v) |x| {
                var xv = x;
                const got = bytesOf(T, &xv);
                var pat: [psize]u8 = undefined;
                @memset(&pat, 0xa5);
                if (sameAll(psize, got, pat)) pay_off = @intCast(po);
            } else |_| {}
        }
    }
    str("eu ");
    str(name);
    ch(' ');
    num(psize);
    ch(' ');
    num(@alignOf(T));
    ch(' ');
    num(size);
    ch(' ');
    num(@alignOf(EU));
    ch(' ');
    if (code_off < 0) ch('-') else num(@intCast(code_off));
    ch(' ');
    if (pay_off < 0) ch('-') else num(@intCast(pay_off));
    eol();
}

fn report() void {
    encoding();
    eu("void", void);
    eu("u8", u8);
    eu("u16", u16);
    eu("u32", u32);
    eu("u64", u64);
    eu("a3u8", [3]u8);
    eu("a2u16", [2]u16);
}

fn parse(arg: [*:0]const u8) u64 {
    var x: u64 = 0;
    var i: usize = 0;
    while (arg[i] != 0) : (i += 1) x = x * 10 + (arg[i] - '0');
    return x;
}

fn is(arg: [*:0]const u8, comptime word: []const u8) bool {
    for (word, 0..) |c, i| if (arg[i] != c) return false;
    return arg[word.len] == 0;
}

/// `from C`: `@errorFromInt(@intCast(C))`. A panic (SIGILL/SIGTRAP) for an integer that does
/// not fit `Code`, is 0, or names no error.
fn from(c: u64) void {
    const code: Code = @intCast(c);
    const e = @errorFromInt(code);
    str("from ");
    num(c);
    ch(' ');
    str(@errorName(e));
    eol();
}

fn table(lo: u64, hi: u64) void {
    var c = lo;
    while (c <= hi) : (c += 1) {
        const code: Code = @intCast(c);
        str("name ");
        num(c);
        ch(' ');
        str(@errorName(@errorFromInt(code)));
        eol();
    }
}

pub export fn main(argc: c_int, argv: [*][*:0]u8) c_int {
    if (argc >= 3 and is(argv[1], "from")) {
        from(parse(argv[2]));
    } else if (argc >= 4 and is(argv[1], "table")) {
        table(parse(argv[2]), parse(argv[3]));
    } else {
        report();
    }
    flush();
    return 0;
}
