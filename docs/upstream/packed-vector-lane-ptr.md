# Draft upstream bug: lane pointers into a vector field of a packed struct (Zig 0.14.1, 0.15.2)

Status: draft, not filed. Target: ziglang/zig (Sema `elemPtr` of a vector behind a bit-pointer,
LLVM lowering of `ptr_elem_ptr`/stores through a `*align(a:0:n:i) T`). Zig 0.16.0 made vector
fields of packed structs a compile error ("packed structs cannot contain fields of type
'@Vector(3, u4)'"), so only 0.14.1 and 0.15.2 are affected. The translator's mitigation
(`Air2Lean/Check.lean`): a lane pointer formed from a bit-pointer to a vector
(`CheckCtx.lanePtr`) or folded into a global that is not a vector (`checkLaneConstant`) is
rejected; vector fields used as whole values (`@bitCast`, field reads and writes of the whole
vector) are modelled (L08, `tests/roadmap/packed-casts`).

## Reproducer

```zig
const std = @import("std");
pub const VF = packed struct(u16) { t: u4, v: @Vector(3, u4) };
var vf: VF = undefined;
pub fn setLanes() u16 {
    vf.t = 0xA;
    vf.v = .{ 1, 2, 3 };
    return @bitCast(vf);
}
pub fn setOne(p: *VF) u16 {
    p.v[1] = 7;
    return @bitCast(p.*);
}
pub fn main() void {
    vf = @bitCast(@as(u16, 0));
    std.debug.print("{x}\n", .{setLanes()}); // expected 321a
    var x: VF = @bitCast(@as(u16, 0xFFFF));
    std.debug.print("{x}\n", .{setOne(&x)}); // expected f7ff
}
```

Observed (x86_64-linux-musl, run in Docker `linux/amd64`):

| Zig | mode | `setLanes` | `setOne` |
|---|---|---|---|
| 0.14.1 | ReleaseSafe | `321a` | `f7f` |
| 0.15.2 | ReleaseSafe | `321` | `f7f` |
| 0.15.2 | Debug | `201` | `7ff` |

The exported AIR (0.15.2) shows the cause: `&vf.v[i]` has the type `*align(2:0:3:i) u4`, a lane
pointer with bit offset 0, although `v` starts at bit 4 of its host; the field's bit offset is
lost when the vector pointer becomes a lane pointer. The language reference gives `vf.v[1] = 7`
the meaning "set lane 1 of the field `v`"; the field `t` must not change.
