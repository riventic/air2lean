# NaN bits observed through memory

The regression of [`docs/architecture-audit/nan-bits.md`](../../../docs/architecture-audit/nan-bits.md).
A NaN that an operation makes has target-specific sign and payload bits; the model's canonical
NaN stands for every NaN, so wherever a NaN's bits become an integer the model gives
`.unspecified` (`Float.detMask`, `docs/floats.md` §NaN in memory). A NaN constant keeps its
exact bits, and so does every float that is not a NaN.

| File | Role |
|---|---|
| `nan_bits.zig` | The cases: a store read back through `*const u32`/`*const u64`, an `extern union`, `@bitCast` of an array and a vector, an `extern struct` read as one integer, `@memcpy` into an integer, a finite quotient, NaN constants stored and in a global initializer, and a stored NaN read back as a float. Compiles on 0.14.1, 0.15.2, 0.16.0 and 0.17.0 |
| `air/<version>/nan_bits/` | Patched-compiler exports (x86_64-linux, baseline, ReleaseSafe; `check.sh --export`) |
| `gen/<version>/NanBits.lean` | Their retained translations |
| `Model.lean` | Kernel-checked results (`decide +kernel`) of each translation, then `main` prints `native.zig`'s lines |
| `native.zig`, `expected/<version>-<arch>.txt` | The native program (volatile operands) and its output on x86_64-linux-musl and aarch64-linux-musl, ReleaseSafe and Debug |

```sh
lake build ZigLean Air2Lean air2lean
bash tests/roadmap/nan-bits/check.sh                    # every version: translate, compare, prove, model = both targets
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/nan-bits/check.sh --native V
AIR2LEAN_ZIG_AIR=<patched zig V> bash tests/roadmap/nan-bits/check.sh --export V DIR
```

`--native` runs in Docker `linux/amd64` and `linux/arm64`; `AIR2LEAN_X86_64_RUN` and
`AIR2LEAN_AARCH64_RUN` replace the runner (empty: the host; CI uses the host and
`qemu-aarch64-static`). A model line `unspecified` matches any native value; every other line must
be equal on both targets.

`reloadIsNaN` is `unspecified` in the model and `1` natively: a stored NaN read back as a float is
an over-approximation (the bytes do not say which NaN they hold).
