# Parameterized pointer width (T02)

One source, `pointer_width.zig`, exported with the repository's patched Zig 0.16.0 for
`wasm32-freestanding`, `wasm32-wasi` (`-target`) and `x86_64-linux -mcpu=baseline`
(`air/0.16.0/<target>/`). The wasm32 profiles record `pointer_bits: 32` and the
exporter's real wasm32 layouts: 4-byte pointers, 8-byte slices, a 12-byte `View`
(`{ *u32, []u32 }`) with its slice at offset 4. The x86_64 export keeps the 64-bit
layouts (8, 16, 24 bytes). `reject.zig` holds wasm32 operations that remain 64-bit only.

The translator selects `Zig.PtrWidth` from the profile (`docs/generated-code.md`
§Pointer width). `PointerWidth/<Wasm32|Wasi|X64>/Gen.lean` are the retained
translations; the x86_64 one uses the unchanged 64-bit runtime terms.

`PointerWidth/Proofs.lean` proves, for the wasm32 and the x86_64 translation of the same
functions: `byteCount` (`@mulWithOverflow(n, 4)`) is null exactly when `4 * n ≥ 2 ^ bits`;
`succ` overflows exactly at `2 ^ bits - 1`; `at` is bounds-checked against the slice length;
`zeros` (`alloc(u32, n)`) is `error.OutOfMemory` with memory unchanged when `4 * n ≥ 2 ^ bits`
(`Allocator.allocOf_overflow`), so `n = 2 ^ 30` fails only on wasm32; and a stored `View`
has 12 (wasm32) or 24 (x86_64) bytes, with `restLen` and `setFirst` reading the slice length
and the pointer at their target offsets. `ZigLean/Mem/WidthLemmas.lean` proves the encodings
of both widths round-trip and that every `.w64` definition is the 64-bit model.

`names.zig` (`@tagName` of an exhaustive and a non-exhaustive enum, `@errorName`, a byte read
through a name) is declared in `exports.json` for Zig 0.17.1 and 0.16.0 and the same three
targets (`air/<version>/names/<target>/`, pinned by `exports.lock.json`). A name is a
`[:0]const u8` into a static block of `mem0`: `Zig.Slice32` on wasm32, `Zig.Slice` on x86_64.
`PointerWidth/Names/V0_17_1/Proofs.lean` proves for all three translations that the returned
length is the name's byte count, the bytes read through the slice are the name, index `len`
reads the sentinel and `len + 1` is out of bounds, and an unnamed non-exhaustive value panics;
`V0_16_0/Proofs.lean` is the same file for the 0.16.0 translations (`scripts/fixtures.py
instance`).

`test_cli.py` checks the translations' runtime names, that an exported pointer layout of
the other width is rejected (the model's sizes come from the profile), that
`pointer_bits` must match the triple, that the name functions use the profile's slice type,
and the rejections of atomics and `Allocator.dupe` on wasm32.

Run under the serialized build queue:

```sh
lake build ZigLean Air2Lean air2lean ZigLean.Mem.WidthLemmas
bash tests/roadmap/pointer-width/check.sh                 # translate, compare, prove, reject
AIR2LEAN_ZIG_NATIVE=<stock zig 0.16.0 or 0.17.1> bash tests/roadmap/pointer-width/check.sh --native
AIR2LEAN_ZIG_AIR=<patched zig 0.16.0> bash tests/roadmap/pointer-width/check.sh --export DIR
python3 -B scripts/fixture-exports.py verify pointer-width   # names.zig, every version
```

`--native` runs each source's layout, `usize`-boundary and name tests on the host, evaluates the
comptime layout asserts for wasm32-freestanding, and runs the wasm32-wasi test binary under
Node's WASI (`run-wasi.mjs`). This qualifies the recorded layouts and the boundary
behavior on those targets; it is not a binary correspondence claim for the generated model.
