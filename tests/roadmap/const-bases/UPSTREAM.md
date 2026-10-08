# Draft upstream issue (not filed)

Draft text for a Zig issue. It has not been filed; filing needs the maintainer's approval.

---

**Title:** LLVM backend: comptime pointer to an error-union payload of alignment 1 points at the error code

### Zig version

0.16.0 and 0.17.0. The same `lowerPtr` code is in 0.14.1 and 0.15.2.

### Steps to reproduce

```zig
const std = @import("std");
const Failure = error{Bad};
const Holder = struct { head: u64, res: Failure![3]u8 };
const frozen: Holder = .{ .head = 1, .res = .{ 20, 21, 22 } };
var mutable: Holder = frozen;

noinline fn launder(p: *const u8) *const u8 {
    const q: *const volatile *const u8 = &p;
    return q.*;
}

pub fn main() void {
    const constant = launder(&(frozen.res catch unreachable)[2]);
    const runtime = launder(&(mutable.res catch unreachable)[2]);
    std.debug.print("constant={d} runtime={d} constant_read={d} runtime_read={d}\n", .{
        @intFromPtr(constant) - @intFromPtr(&frozen),
        @intFromPtr(runtime) - @intFromPtr(&mutable),
        constant.*,
        runtime.*,
    });
}
```

`zig run repro.zig -fllvm -OReleaseSafe` (this file is `llvm_probe.zig` here; the IR names below use that name)

### Expected behavior

`constant=10 runtime=12 constant_read=22 runtime_read=22`. The comptime-known pointer
`&(frozen.res catch unreachable)[2]` addresses payload element 2. The payload of
`error{Bad}![3]u8` follows the 2-byte error code.

### Actual behavior

On aarch64-macos, stock 0.16.0 and 0.17.0, with `-fllvm` in ReleaseSafe or Debug:

```
constant=10 runtime=12 constant_read=20 runtime_read=22
```

The comptime pointer is 2 bytes too low and reads element 0. On x86_64-linux-musl the LLVM IR
(`-femit-llvm-ir`) contains `getelementptr (i8, @llvm_probe.frozen, i64 10)` for the constant and
`@llvm_probe.mutable + 12` for the runtime projection. The global's LLVM type is
`{ i64, { i16, [3 x i8], [1 x i8] }, [2 x i8] }`, so offset 10 is the `i16` error code.
Stock 0.16.0 on x86_64-linux-musl, baseline CPU, ReleaseSafe, gives the same result. The
self-hosted backend is correct:

```
-fllvm:                  constant=10 runtime=12 constant_read=20 runtime_read=22
-fno-llvm (x86_64):      constant=12 runtime=12 constant_read=22 runtime_read=22
```

### Cause

In `src/codegen/llvm.zig`, `Object.lowerPtr`, the `.eu_payload` arm reads:

```zig
.eu_payload => |eu_ptr| try o.lowerPtr(
    eu_ptr,
    offset + codegen.errUnionPayloadOffset(
        Value.fromInterned(eu_ptr).typeOf(zcu).childType(zcu),
        zcu,
    ),
),
```

`childType` of the base pointer type is the error-union type, not the payload type. The
error union's alignment is always at least `anyerror`'s, so `errUnionPayloadOffset`
returns 0. The generic `src/codegen.zig` `lowerPtr` used by the self-hosted backends
passes `.childType(zcu).errorUnionPayload(zcu)`, which is correct.

Suggested fix: add `.errorUnionPayload(zcu)` in `codegen/llvm.zig`.

Affected shape: any comptime-known pointer whose base chain contains `eu_payload` for a
payload with runtime bits and alignment below `@alignOf(anyerror)`, such as `u8`, `bool`
or `[N]u8`. Payloads with alignment 2 or more start at offset 0 and are unaffected.
