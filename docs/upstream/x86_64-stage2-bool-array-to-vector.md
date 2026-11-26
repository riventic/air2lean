# Draft upstream bug: `[N]bool` to `@Vector(N, bool)` coercion drops lanes on the self-hosted x86_64 backend (Zig 0.14.1)

Status: draft, not filed (a row for the issue #131 table). Target: ziglang/zig (self-hosted
x86_64 backend, `array_to_vector` lowering of a bool array). Only observed under emulation, not on
x86_64 hardware: confirmed under two emulators (Rosetta for Linux and `qemu-x86_64` 11.0.3), and
the LLVM backend of the same compiler gives the right bytes. Treat it as a compiler bug that has
not yet been seen on hardware. Zig 0.15.2, 0.16.0 and 0.17.1 are correct. air2lean fails closed:
the translator does not admit bool vectors on the self-hosted x86_64 profile
(`tests/roadmap/vector-layouts/probe_strided.zig` avoids the coercion).

## Summary

With `-fno-llvm -fno-lld -target x86_64-linux -mcpu=baseline`, `const v: @Vector(N, bool) = arr;`
(arr: `[N]bool`) produces a vector whose memory image has (almost) all lanes false, for N >= 14 with
the pattern below (N = 8 is right). For N = 16 and the pattern `0xc70d` the image is `00 80`
instead of `0d c7`: only the top lane survives. (The handoff observation `00 80` for `2d 80` was a
different pattern.) Building the vector lane by lane is not an available comparison: 0.14.1 reports
`TODO implement vector_store_elem` for `v[i] = x` on such a vector.

## Reproducer

```zig
const std = @import("std");

// lane i is true when bit i of this pattern is set
const pat: u64 = 0x9a5b_36d2_81e4_c70d;

fn arrN(comptime N: usize) [N]bool {
    var a: [N]bool = undefined;
    for (&a, 0..) |*x, i| x.* = (pat >> @intCast(i)) & 1 != 0;
    return a;
}

noinline fn coerce(comptime N: usize, a: [N]bool) @Vector(N, bool) {
    const v: @Vector(N, bool) = a;
    return v;
}

fn show(comptime N: usize) void {
    const v = coerce(N, arrN(N));
    std.debug.print("N={d:>2} image:", .{N});
    for (std.mem.asBytes(&v)) |b| std.debug.print(" {x:0>2}", .{b});
    // expected on the LLVM backend: lane i is bit i (little endian), padding bits clear
    const mask: u64 = if (N == 64) ~@as(u64, 0) else (@as(u64, 1) << N) - 1;
    std.debug.print("   pattern {x:0>16}\n", .{pat & mask});
}

pub fn main() void {
    show(8);
    show(14);
    show(15);
    show(16);
    show(17);
    show(32);
}
```

```
zig build-exe bv.zig -O<Debug|ReleaseSafe> -target x86_64-linux -mcpu=baseline -fno-llvm -fno-lld
zig build-exe bv.zig -O<Debug|ReleaseSafe> -target x86_64-linux -mcpu=baseline -fllvm
```

Run in `docker run --platform linux/amd64` (Rosetta; add `-z norelro` to the build for ReleaseSafe,
[rosetta.md](../rosetta.md)) and in `qemu-x86_64` (an `alpine:3` `linux/arm64` container with
`apk add qemu-x86_64`).

## Observed and expected

Zig 0.14.1, `-fno-llvm -fno-lld`, Debug and ReleaseSafe, identical under Rosetta and qemu:

```
N= 8 image: 0d   pattern ...0d
N=14 image: 00 00   pattern ...070d
N=15 image: 00 40   pattern ...470d
N=16 image: 00 80   pattern ...c70d
N=17 image: 00 00 00 00   pattern ...c70d
N=32 image: 00 00 00 80   pattern ...81e4c70d
```

Same compiler with `-fllvm` (Rosetta and qemu agree): `0d`, `0d 07`, `0d 47`, `0d c7`,
`0d c7 00 xx` (the byte of lane 16 and up: `00` in ReleaseSafe, `01` in Debug, which is
uninitialised padding), `0d c7 e4 81`. Zig 0.15.2, 0.16.0 and 0.17.1 with `-fno-llvm -fno-lld`
(ReleaseSafe, Rosetta): `0d`, `0d 07`, `0d 47`, `0d c7`, `0d c7 00 00`, `0d c7 e4 81`.

Expected: lane i of the vector is `arr[i]`, i.e. the image `pat & mask`.

## Not established

Not run on x86_64 hardware. Two emulators with different instruction translators agree, which
makes an emulator artefact unlikely but does not exclude a CPU-feature dependence of the generated
code; confirm on hardware before filing.
