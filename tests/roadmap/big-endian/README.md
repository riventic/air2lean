# Byte order: a big-endian profile (T03)

One source, `big_endian.zig`, exported with the repository's patched Zig 0.16.0 for
`s390x-linux` and `mips64-linux` (big endian; MIPS64 n64, `mips64r2` baseline) and
`x86_64-linux -mcpu=baseline` (little endian) (`air/0.16.0/<target>/`). The three exports are
the same AIR except for their profile, and the two big-endian translations are the same text
apart from the profile header and namespace. Every
function observes byte order: `@bitCast` of integers, floats, packed structs and `extern`
structs to and from byte arrays, byte views of integers and floats in memory, an
`extern union` read through another field, and bit-pointer loads and stores into a packed
struct whose bytes are read or written one by one. `reject.zig` holds s390x operations
outside the qualified big-endian model (`air/0.16.0/s390x-reject/`), and the two byte views
of a vector in memory (`vecByte`, `vecLane0FromBytes`): a `@ptrCast` between a vector and an
array is illegal behaviour (langref §Vectors, `docs/illegal-behavior.md`), rejected for every
profile.

| File | Role |
|---|---|
| `BigEndian/S390x/Gen.lean`, `BigEndian/Mips64/Gen.lean`, `BigEndian/X64/Gen.lean` | Retained translations (profiles `abi64-be-v1`, `abi64-le-v1`) |
| `expected-gen.diff` | Their only differences: header, namespace, `open scoped Zig.BigEndian`, the `.big` bit-pointer accesses |
| `BigEndian/Proofs.lean` | Kernel-evaluated byte-level facts of both translations |
| `Diff.lean` | The model of either translation on `native.zig`'s inputs, in its output format |
| `native.zig` | The native program: the same 115 cases |
| `observed/<arch>-linux-musl-ReleaseSafe.txt` | Its output with stock Zig 0.16.0: s390x under qemu (Docker `--platform linux/s390x`), mips64 (`mips64-linux-muslabi64`) under the Docker VM's qemu-mips64 binfmt handler, x86_64 under Docker `linux/amd64`. The s390x and mips64 outputs are identical |
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

`--native` builds `native.zig` for the three targets, runs it (Docker by default; set
`AIR2LEAN_S390X_RUN=qemu-s390x-static`, `AIR2LEAN_MIPS64_RUN=qemu-mips64-static` or
`AIR2LEAN_X86_64_RUN=` for a direct runner; `elf-abiversion.py` clears the mips64 executable's
EI_ABIVERSION byte, which the binfmt handler's magic does not match), and
requires its output to equal the model's lines and the retained observations. 88 of the 125
lines differ between the two byte orders. These are bounded observations of one target,
backend (`stage2_llvm`) and mode (`ReleaseSafe`); they do not establish binary correspondence.

## Concurrency and allocator models (`concurrency.zig`)

Atomics, futexes, threads and the allocator model on both byte orders. The atomic messages of
`ZigLean/Mem/Thread.lean` are the location's memory bytes, read and written as a little-endian
integer. At `.big`, `ZigLean/Conc/Endian.lean` conjugates every integer atomic op and every
futex compare by `byteSwap`:

- a load swaps the value it read;
- a store, and the operands of a `cmpxchg`, are swapped before the write or the comparison;
- an RMW applies the op to the swapped old value and writes the swapped result
  (`atomicRmwFnAt`).

The checker admits big-endian atomics on representations of at most 8 bits or of a whole number
of bytes. A `u12` atomic fails closed (`reject.zig`'s `atomicU12`). Pointer atomics keep their
symbolic bytes. The std allocator, thread and OS models read no integer from memory except the
futex word, so they are admitted on big-endian profiles.

Each function observes byte order: an atomic store read back through its bytes, plain bytes
read atomically, an RMW carry across a byte, a 64-bit `cmpxchg`, a signed `Max`, two threads
adding to one word, a heap word from `Allocator.create`, and a futex wait (0.15.2) whose
expected value is the word's bytes in the other order. That wait returns at once; under a
byte-order mistake the model would sleep forever.

| File | Role |
|---|---|
| `air/<version>/concurrency/<target>/` | Exports for Zig 0.17.0 and 0.15.2 (`std.Thread.Futex` exists only up to 0.15.2), for s390x-linux, mips64-linux and x86_64-linux |
| `conc-gen/<version>-<target>.lean` | Retained translations |
| `ConcRun.lean`, `ConcDiff.lean`, `ConcFutex.lean` | The model's lines. Each case runs under 24 scheduler oracles and must give the same result under all of them |
| `concurrency_native.zig`, `observed/concurrency-<version>-<target>.txt` | The native program and its output |

```sh
bash tests/roadmap/big-endian/concurrency.sh                  # translate, compare, model = observed
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/big-endian/concurrency.sh --native V
```

The model's lines equal the native output on all three targets and both versions. The two
big-endian targets give identical lines, and they differ from x86_64 on 5 of the 7 or 8 lines.
