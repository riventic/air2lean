//! G2 (docs/c-frontend.md): pointer casts through `*anyopaque`/byte views and self-referential
//! structs, in the shapes `zig translate-c` emits (`@ptrCast(@alignCast(p))`, `[*c]` pointers).
//! Every export takes `(a, b)` and returns `u32`; `native.zig` runs them natively.

const Node = extern struct { value: u32, next: ?*Node };
const Tree = extern struct { key: u32, left: [*c]Tree, right: [*c]Tree };
const Ctx = extern struct { sum: u32, scale: u32 };

/// A list built over a local pool, then odd values removed through a pointer to a link
/// (`struct node **link = &head`), then summed with weights.
pub export fn listSum(a: u32, b: u32) u32 {
    var pool: [6]Node = undefined;
    var head: ?*Node = null;
    var i: u32 = 0;
    while (i < 6) : (i += 1) {
        pool[i] = .{ .value = a +% i *% b, .next = head };
        head = &pool[i];
    }
    var link: *?*Node = &head;
    while (link.*) |n| {
        if (n.value & 1 != 0) link.* = n.next else link = &n.next;
    }
    var s: u32 = 0;
    var k: u32 = 1;
    var it = head;
    while (it) |n| : (it = n.next) {
        s +%= n.value *% k;
        k += 1;
    }
    return s;
}

fn treeSum(t: [*c]Tree, depth: u32) u32 {
    if (t == null) return 0;
    return t.*.key *% depth +% treeSum(t.*.left, depth + 1) +% treeSum(t.*.right, depth + 1);
}

/// A binary search tree with C pointers to its own type, inserted iteratively.
pub export fn treeInsert(a: u32, b: u32) u32 {
    var nodes: [5]Tree = undefined;
    var root: [*c]Tree = null;
    var i: u32 = 0;
    while (i < 5) : (i += 1) {
        const key = (a +% i *% b) % 97;
        nodes[i] = .{ .key = key, .left = null, .right = null };
        var slot: [*c][*c]Tree = &root;
        while (slot.* != null) {
            slot = if (key < slot.*.*.key) &slot.*.*.left else &slot.*.*.right;
        }
        slot.* = &nodes[i];
    }
    return treeSum(root, 1);
}

fn readThrough(ctx: ?*anyopaque) u32 {
    const p: [*c]u32 = @ptrCast(@alignCast(ctx));
    return p.*;
}

/// `void *` round trips: the pointer comes back with its block and offset, and the access
/// is checked against the original object.
pub export fn voidRoundTrip(a: u32, b: u32) u32 {
    var w: u32 = a ^ b;
    const vp: ?*anyopaque = @ptrCast(@alignCast(&w));
    const back: [*c]u32 = @ptrCast(@alignCast(vp));
    back.* +%= 7;
    var pair = [2]u32{ a, b };
    const second: ?*anyopaque = @ptrCast(@alignCast(&pair[1]));
    return readThrough(@ptrCast(@alignCast(&w))) +% readThrough(second) *% 3;
}

/// A `char *` view of a `u32` (little-endian bytes), written through and read back.
pub export fn byteView(a: u32, b: u32) u32 {
    var w: u32 = a +% b;
    const bytes: [*c]u8 = @ptrCast(@alignCast(&w));
    var s: u32 = 0;
    var i: usize = 0;
    while (i < 4) : (i += 1) s = s *% 31 +% bytes[i];
    bytes[1] = 0xAB;
    return s ^ w;
}

fn visit(ctx: ?*anyopaque, v: u32) void {
    const c: [*c]Ctx = @ptrCast(@alignCast(ctx));
    c.*.sum +%= v *% c.*.scale;
}

/// An opaque callback context (`void *user`), as C APIs pass it.
pub export fn opaqueContext(a: u32, b: u32) u32 {
    var c = Ctx{ .sum = 0, .scale = (b & 7) + 1 };
    var i: u32 = 0;
    while (i < 4) : (i += 1) visit(@ptrCast(@alignCast(&c)), a +% i);
    return c.sum;
}

/// Negative: a pointer's bytes read as an integer. The model keeps pointer bytes symbolic, so
/// the read is `.unspecified` (natively it is the address).
pub export fn pointerAsInt(a: u32, b: u32) u32 {
    var w: u32 = a ^ b;
    var p: *u32 = &w;
    _ = &p;
    const raw: *const u64 = @ptrCast(@alignCast(&p));
    return @truncate(raw.*);
}

/// Negative: a byte that is not 0 or 1 read as `bool` is illegal behaviour (`.illegal`).
pub export fn byteAsBool(a: u32, b: u32) u32 {
    var x: u8 = @truncate((a ^ b) | 2);
    const bp: *bool = @ptrCast(&x);
    return if (bp.*) 1 else 0;
}

/// Negative: `@alignCast` of a misaligned pointer. ReleaseSafe checks it (`incorrectAlignment`:
/// a panic, `.panic` in the model).
pub export fn misalignedChecked(a: u32, b: u32) u32 {
    var buf: [8]u8 align(4) = .{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const off: usize = (a & 1) | 1;
    const p: *u32 = @ptrCast(@alignCast(&buf[off]));
    return p.* +% b;
}

/// Negative: the same cast without the safety check. The access through the misaligned
/// pointer is illegal behaviour that ReleaseSafe does not check (`.illegal` in the model).
pub export fn misalignedUnchecked(a: u32, b: u32) u32 {
    @setRuntimeSafety(false);
    var buf: [8]u8 align(4) = .{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const off: usize = (a & 1) | 1;
    const p: *u32 = @ptrCast(@alignCast(&buf[off]));
    return p.* +% b;
}

/// A 16-byte copy through `@Vector(16, u8)` views of byte buffers, as compiler_rt's `memcpy`
/// copies: a `u8` vector has the bytes' layout (`Vec.encode_u8`). The sum of the copied bytes.
pub export fn byteVectorCopy(a: u32, b: u32) u32 {
    var src: [16]u8 align(16) = undefined;
    for (&src, 0..) |*x, i| x.* = @truncate(a +% b *% @as(u32, @intCast(i)));
    var dst: [16]u8 align(16) = undefined;
    const s: *const @Vector(16, u8) = @ptrCast(&src);
    const d: *@Vector(16, u8) = @ptrCast(&dst);
    d.* = s.*;
    var sum: u32 = 0;
    for (dst) |x| sum +%= x;
    return sum;
}
