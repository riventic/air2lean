# Draft upstream bug: a runtime sentinel check on a zero-bit element type breaks codegen (Zig 0.14.1 to 0.17.1)

Status: draft, not filed (a row for the issue #131 table). Target: ziglang/zig (the safety check
emitted for `ptr[0..n :s]` / `allocSentinel`, in the LLVM backend and in the self-hosted x86_64
backend). Found as a compiler crash on `std.mem.Allocator.allocSentinel(u0, n, 0)`. It is not an
air2lean exporter-patch bug: the stock compilers fail the same way. air2lean is affected only
as a Zig program that cannot be built: it cannot be compiled to a native binary for a differential
run, and the AIR exporter (a patch on the compiler) crashes the same way on 0.16.0 and 0.15.2
(0.17.1 and 0.14.1 export it); no translation result is produced, so nothing is mis-modelled.

## Summary

Slicing a many-item pointer with a sentinel, `p[0..n :0]`, where the element type has no bits
(`u0`, `void`-like integers), is accepted by Sema, but in the safe build modes (Debug,
ReleaseSafe) the sentinel check reads and compares an element of that type, and code generation
fails:

- LLVM backend (`-fllvm`, the default for these targets and modes): the module is invalid and
  LLVM's bitcode reader rejects it with
  `error: Bitwidth for integer type out of range (Producer: 'zig <v>' Reader: 'LLVM <n>')`.
- Self-hosted x86_64 backend (`-fno-llvm -fno-lld`): the compiler itself dies with a signal
  (SIGSEGV on 0.14.1, 0.15.2, 0.17.1, SIGBUS/SIGILL on 0.16.0) with no diagnostic.

ReleaseFast (no safety check) compiles. The standard library hits it through
`Allocator.allocSentinel(u0, n, 0)` -> `allocWithOptionsRetAddr` (`ptr[0..n :sentinel]`).

## Reproducer

```zig
noinline fn f(p: [*]u0, n: usize) [:0]u0 {
    return p[0..n :0];
}
var buf: [4]u0 = undefined;
pub fn main() void {
    _ = f(&buf, 3);
}
```

```
zig build-exe e6.zig -ODebug       -target x86_64-linux -fllvm
zig build-exe e6.zig -OReleaseSafe -target x86_64-linux -fllvm
zig build-exe e6.zig -ODebug       -target x86_64-linux -fno-llvm -fno-lld
```

The library form (also fails on all four versions, `-ODebug` and `-OReleaseSafe`, native
aarch64-macos and `-target x86_64-linux`/`aarch64-linux`):

```zig
const std = @import("std");
pub fn main() !void {
    const a = std.heap.page_allocator;
    const s = try a.allocSentinel(u0, 3, 0);
    a.free(s);
}
```

## Observed and expected

Stock compilers, `-fllvm`: all of 0.14.1, 0.15.2, 0.16.0 and 0.17.1 print
`error: Bitwidth for integer type out of range (Producer: 'zig 0.17.1' Reader: 'LLVM 22.1.8')`
(LLVM 19.1.7, 20.1.2, 21.1.0, 22.1.8 respectively), exit 1, on Debug and ReleaseSafe, for
x86_64-linux, aarch64-linux and aarch64-macos. With `-fno-llvm -fno-lld` (x86_64-linux): exit 139
(0.14.1, 0.15.2, 0.17.1) or 138 (0.16.0), no message. With `u8` instead of `u0`, and with
`-OReleaseFast`, every version compiles.

Expected: the program compiles (the check compares zero bits and is trivially true), or Sema
rejects a sentinel on a zero-bit element type with a compile error.

## Evidence

Run on Apple silicon with the stock compilers of `scripts/cas.py host-zig <version>`; matrix
recorded in the PR that added this draft. The lane that saw it first reported the same failure
("Generating function `mem.Allocator.allocWithOptionsRetAddr`", reached unreachable) on the
patched 0.16.0 and 0.15.2 compilers; the patched compilers do nothing here that the stock ones
do not.
