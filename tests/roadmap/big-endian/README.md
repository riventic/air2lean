# Byte order: a big-endian profile (T03)

One source, `big_endian.zig`, exported with the repository's patched Zig 0.17.1 and 0.16.0 for
`s390x-linux` and `mips64-linux` (big endian; MIPS64 n64, `mips64r2` baseline) and
`x86_64-linux -mcpu=baseline` (little endian) (`air/<version>/<target>/`). The three exports of
one version are the same AIR except for their profile, and the two big-endian translations are
the same text apart from the profile header and namespace. Every function observes byte order
on 0.16.0: `@bitCast` of integers, floats, packed structs and `extern` structs to and from byte
arrays, byte views of integers and floats in memory, an `extern union` read through another
field, and bit-pointer loads and stores into a packed struct whose bytes are read or written one
by one. From 0.17 on, `@bitCast` is the logical bit order (`docs/bitcast-semantics.md`): those
casts give the same bytes on both targets, natively and in the model, and the byte order shows
through memory only. 0.17 has no `@bitCast` of an `extern struct`, so `externToBytes` reads its
bytes through a pointer there (one source line, selected by `zig_version`). `reject.zig` holds
s390x operations outside the qualified big-endian model (`air/<version>/s390x-reject/`), and
the two byte views of a vector in memory (`vecByte`, `vecFromBytes`): a `@ptrCast`
between a vector and an array is illegal behaviour (langref §Vectors,
`docs/illegal-behavior.md`), rejected for every profile. `vecLanes` accesses single lanes
of a vector in memory: a lane pointer from Zig 0.17.1 on, rejected at big endian
(`docs/profiles.md` §Byte order), and translated on 0.16.0.

| File | Role |
|---|---|
| `BigEndian/<version>/<target>/Gen.lean` | Retained translations (`<version>` as a name: `V0_17_1`, `V0_16_0`; `<target>` `S390x`, `Mips64`, `X64`; profiles `abi64-be-v1`, `abi64-le-v1`) |
| `expected-gen.diff` | Their only differences, on each version: header, namespace, `open scoped Zig.BigEndian`, the `.big` bit-pointer accesses |
| `BigEndian/Proofs.lean` | Kernel-evaluated byte-level facts of the translations of both versions |
| `BigEndian/Lines.lean`, `BigEndian/<version>/<target>/Diff.lean` | The model of one translation on `native.zig`'s inputs, in its output format. Written for 0.17.1 x86_64-linux; the other modules are that one with the version and target renamed (`scripts/fixtures.py instance ... --write` after an edit) |
| `native.zig` | The native program: the same 115 cases |
| `observed/<version>-<arch>-linux-musl-ReleaseSafe.txt` | Its output with stock Zig `<version>`: s390x under qemu (Docker `--platform linux/s390x`), mips64 (`mips64-linux-muslabi64`) under the Docker VM's qemu-mips64 binfmt handler, x86_64 under Docker `linux/amd64`. The s390x and mips64 outputs are identical |
| `test_cli.py` | Profile acceptance, mixed/contradictory endian metadata and the fail-closed rejections, on each version's exports |
| `names.zig`, `air/<version>/names/<target>/` | `@tagName` (an exhaustive enum and a non-exhaustive `enum(u16)`) and `@errorName`, and a name slice stored in memory read back byte by byte; its test is endian-aware |
| `BigEndian/Names/<version>/<target>/Gen.lean` | Their retained translations |
| `BigEndian/Names/<version>/Proofs.lean` | Kernel-evaluated facts on each target: the name's length and bytes, the sentinel at index `len`, out of bounds after it, no name for an unnamed tag, and the stored length's least significant byte (byte 7 at big endian, byte 0 at little endian). Written for 0.17.1; the 0.16.0 file is that one renamed (`scripts/fixtures.py instance ... --write` after an edit) |

`ZigLean/Endian.lean` parameterizes the byte order; `ZigLean/EndianLemmas.lean` (proof-only)
proves the integer, float, slice, optional-slice and vector round trips at both orders and the
bit-pointer frame at both orders. The `.little` definitions are the existing model by `rfl`.

Run under the serialized build queue:

```sh
lake build ZigLean Air2Lean air2lean ZigLean.EndianLemmas
bash tests/roadmap/big-endian/check.sh          # translate, compare, prove, model = observed, reject
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/big-endian/check.sh --native V
python3 scripts/fixture-exports.py verify big-endian
```

The AIR is declared in `exports.json` and pinned by `exports.lock.json`; every `check.sh` and
`concurrency.sh` run checks the lock, and `verify` re-exports with the patched compiler and
compares byte for byte.

`check.sh` requires the model's lines of each version and target to equal the retained
observation. `--native V` builds `native.zig` with stock Zig `V` for the three targets, runs it
(Docker by default; set `AIR2LEAN_S390X_RUN=qemu-s390x-static`,
`AIR2LEAN_MIPS64_RUN=qemu-mips64-static` or `AIR2LEAN_X86_64_RUN=` for a direct runner;
`elf-abiversion.py` clears the mips64 executable's EI_ABIVERSION byte, which the binfmt
handler's magic does not match), and requires its output to equal the retained observation; it
also runs `names.zig`'s test on the three targets. Of
the 115 lines, 82 differ between the two byte orders on 0.16.0 and 56 on 0.17.1. These are
bounded observations of one target, backend (`stage2_llvm`) and mode (`ReleaseSafe`); they do
not establish binary correspondence.

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

This fixture is a model-against-native comparison of byte order and contains no theorem.
s390x-linux and mips64-linux have no memory-model qualification (premise ORD-06,
`memory_model.unqualified` in `assurance/premises.json`): `scripts/premises.py` fails a
concurrency theorem about these translations, and `scripts/claims.py` rejects such a goal. The
observations below are schedule-independent results under qemu user-mode emulation; they are not
evidence about the hardware's memory ordering.

Each function observes byte order: an atomic store read back through its bytes, plain bytes
read atomically, an RMW carry across a byte, a 64-bit `cmpxchg`, a signed `Max`, two threads
adding to one word, a heap word from `Allocator.create`, and a futex wait (0.15.2) whose
expected value is the word's bytes in the other order. That wait returns at once; under a
byte-order mistake the model would sleep forever.

| File | Role |
|---|---|
| `air/<version>/concurrency/<target>/` | Exports for Zig 0.17.1 and 0.15.2 (`std.Thread.Futex` exists only up to 0.15.2), for s390x-linux, mips64-linux and x86_64-linux |
| `BigEndian/Conc/<version>/<target>/Gen.lean` | Retained translations (`<version>` as a name: `V0_17_1`; `<target>` `S390x`, `Mips64`, `X64`) |
| `BigEndian/Conc/<version>/<target>/{Run,Diff,Futex}.lean` | The model's lines. Each case runs under 24 scheduler oracles and must give the same result under all of them. Written for 0.17.1 x86_64-linux (`Futex`: 0.15.2); the other modules are those with the version and target renamed (`scripts/fixtures.py instance ... --write` after an edit) |
| `concurrency_native.zig`, `observed/concurrency-<version>-<target>.txt` | The native program and its output |

```sh
bash tests/roadmap/big-endian/concurrency.sh                  # translate, compare, model = observed
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/big-endian/concurrency.sh --native V
```

The model's lines equal the native output on all three targets and both versions. The two
big-endian targets give identical lines, and they differ from x86_64 on 5 of the 7 or 8 lines.
