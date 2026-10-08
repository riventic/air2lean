# Byte order: a big-endian profile (T03)

One source, `big_endian.zig`, exported with the repository's patched Zig 0.16.0 for
`s390x-linux` (big endian) and `x86_64-linux -mcpu=baseline` (little endian)
(`air/0.16.0/<target>/`). The two exports are the same AIR except for their profile. Every
function observes byte order: `@bitCast` of integers, floats, packed structs and `extern`
structs to and from byte arrays, byte views of integers, floats and vectors in memory, an
`extern union` read through another field, and bit-pointer loads and stores into a packed
struct whose bytes are read or written one by one. `reject.zig` holds s390x operations
outside the qualified big-endian model (`air/0.16.0/s390x-reject/`).

| File | Role |
|---|---|
| `BigEndian/S390x/Gen.lean`, `BigEndian/X64/Gen.lean` | Retained translations (profiles `abi64-be-v1`, `abi64-le-v1`) |
| `expected-gen.diff` | Their only differences: header, namespace, `open scoped Zig.BigEndian`, the `.big` bit-pointer accesses |
| `BigEndian/Proofs.lean` | Kernel-evaluated byte-level facts of both translations |
| `Diff.lean` | The model of either translation on `native.zig`'s inputs, in its output format |
| `native.zig` | The native program: the same 125 cases |
| `observed/<arch>-linux-musl-ReleaseSafe.txt` | Its output with stock Zig 0.16.0: s390x under qemu (Docker `--platform linux/s390x`), x86_64 under Docker `linux/amd64` |
| `test_cli.py` | Profile acceptance, mixed/contradictory endian metadata and the fail-closed rejections |

`ZigLean/Endian.lean` parameterizes the byte order; `ZigLean/EndianLemmas.lean` (proof-only)
proves the integer, float, slice, optional-slice and vector round trips at both orders and the
bit-pointer frame at both orders. The `.little` definitions are the existing model by `rfl`.

Run under the serialized build queue:

```sh
lake build ZigLean Air2Lean air2lean ZigLean.EndianLemmas
bash tests/roadmap/big-endian/check.sh          # translate, compare, prove, model = observed, reject
AIR2LEAN_ZIG_NATIVE=<stock zig 0.16.0> bash tests/roadmap/big-endian/check.sh --native
AIR2LEAN_ZIG_AIR=<patched zig> bash tests/roadmap/big-endian/check.sh --export DIR
```

`--native` builds `native.zig` for both targets, runs it (Docker by default; set
`AIR2LEAN_S390X_RUN=qemu-s390x-static` or `AIR2LEAN_X86_64_RUN=` for a direct runner), and
requires its output to equal the model's lines and the retained observations. 88 of the 125
lines differ between the two byte orders. These are bounded observations of one target,
backend (`stage2_llvm`) and mode (`ReleaseSafe`); they do not establish binary correspondence.
