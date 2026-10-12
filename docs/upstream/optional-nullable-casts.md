# Draft: `@ptrCast`/`@ptrFromInt` of `?*allowzero T` is miscompiled

Status: draft for the project issue board; not filed upstream (CLAUDE.md, maintainer decision).
Found by L05 (`docs/null-pointers.md`); the translator rejects these casts.

`?*allowzero T` (and `?[*c]T`) is not pointer-like: its payload can be address zero, so the
compiler gives it a separate flag byte (`@sizeOf(?*allowzero u8) == 16` on x86_64). Sema still
accepts a pointer cast between it and another pointer type and lowers it as a plain
`ptr_cast`/`bitcast`, and accepts `@ptrFromInt` into it. The backend then treats the 16-byte
`{ptr, i8}` value as a pointer.

```zig
var zero: usize = 0;
noinline fn castOpt(a: ?*allowzero u8) ?*u8 { return @ptrCast(a); }
pub fn main() void {
    const z = @as(*volatile usize, &zero).*;
    const some_zero: *allowzero u8 = @ptrFromInt(z);
    const none: ?*allowzero u8 = null;
    @import("std").debug.print("{} {}\n", .{ castOpt(some_zero) == null, castOpt(none) == null });
    const from_int: ?*allowzero u8 = @ptrFromInt(z); // flag byte left uninitialized
    @import("std").debug.print("{}\n", .{from_int == null});
}
```

Observed (ReleaseSafe, aarch64-macos):

| Zig | `castOpt(some 0) == null` | `castOpt(null) == null` | `@ptrFromInt(0)` as `?*allowzero u8` |
| --- | --- | --- | --- |
| 0.16.0 | `true` | `false` | varies between builds (`true`/`false`): the flag is not written |
| 0.17.0 | `false` | `false` | LLVM error `Invalid cast` (the program does not build) |

Expected: either a compile error (no pointer cast between a flagged optional and a pointer-like
type; `@ptrFromInt` cannot produce one) or explicit flag handling (`null` ↔ `null`, `some p` ↔
`p`). The coercion `?*u8` → `?*allowzero u8` is correct (Sema casts the payload and wraps it,
mapping `null` to `some` of address zero); only these casts are affected.
