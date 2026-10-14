# Encode/decode exactness

The regressions of [`docs/architecture-audit/enc-exactness.md`](../../../docs/architecture-audit/enc-exactness.md)
(BUG-1, integers with padding bits) and
[`docs/architecture-audit/model-handle-bytes.md`](../../../docs/architecture-audit/model-handle-bytes.md)
(BUG-2, the bytes of a `std.mem.Allocator`). Every value <-> bytes pair of the model is exact or
`.unspecified`: the model never reads a value from bits that native code leaves open.

| File | Role |
|---|---|
| `enc_exactness.zig` | Integers with padding bits (`i10`, `u24`, `i24`, an `enum(u24)`) read from bytes their own store did not write, stored over other bytes, and round-tripped; a `bool` byte. Compiles on 0.14.1, 0.15.2, 0.16.0 and 0.17.0 |
| `opaque_bytes.zig` | An allocator's `vtable` word read as a `u64` |
| `air/<version>/{enc_exactness,opaque_bytes}/` | Patched-compiler exports (x86_64-linux, baseline, ReleaseSafe; `check.sh --export`) |
| `gen/<version>/{EncExactness,Opaque}.lean` | Their retained translations |
| `Model.lean` | Kernel-checked results (`decide +kernel`) of each version's translations, then `main` prints `native.zig`'s lines |
| `Rows.lean` | One kernel-checked row per value kind of the memory model: exact round trip, undetermined bits `.unspecified` |
| `native.zig`, `expected/<version>-<arch>-<mode>.txt` | The native program (volatile operands) and its output on x86_64-linux-musl and aarch64-linux-musl, ReleaseSafe and Debug |

```sh
lake build ZigLean Air2Lean air2lean
bash tests/roadmap/enc-exactness/check.sh                  # every version: translate, compare, prove, model = both targets
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/enc-exactness/check.sh --native V
AIR2LEAN_ZIG_AIR=<patched zig V> bash tests/roadmap/enc-exactness/check.sh --export V DIR
```

`--native` runs in Docker `linux/amd64` and `linux/arm64`; `AIR2LEAN_X86_64_RUN` and
`AIR2LEAN_AARCH64_RUN` replace the runner (empty: the host; CI uses the host and
`qemu-aarch64-static`). A model line `unspecified` matches any native value; every other line
must equal the ReleaseSafe output of both targets. The Debug outputs are evidence: on x86_64 from
0.15.2 Debug is the self-hosted backend, which stores a padded integer extended and loads the whole
ABI integer (`Dialect.intExtOrder?`).

`allocatorWordIsZero` is `0x0` natively (the word is an address) and `unspecified` in the model;
before BUG-2 was fixed the model printed `0x1`.
