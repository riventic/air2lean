# Pointer-try lifetimes and concurrent aliases (L04)

`try_lifetimes.zig` adds two cases to the alias and cleanup cases of `../try_pointers.zig` and
`../try_aliases.zig`: unions whose lifetime ends, and unions that threads share.

- **`freeOnError`.** The union lives on the heap (`Allocator.create`). The pointer try captures
  the error code, and then the `errdefer` frees the union. The error path still returns the
  original error, and no heap block stays live.
- **`readDangling`.** A payload pointer outlives its union, because `defer` freed the union.
  The read through it is a use after free, which the model reports as `.illegal`. This is
  illegal behaviour and is not run natively.
- **`concurrentReads`.** Two threads each take the payload pointer of the same union and read
  through it.
- **`concurrentWrites`.** Two threads write through the payload pointers of two different
  unions.
- **`racingAliases`.** One thread writes through the payload pointer while another reads it.
  This is a data race (`.illegal`, under every schedule) and is not run natively.

`try_payloads.zig` repeats the alias and cleanup functions of `../try_pointers.zig` and
`../try_aliases.zig` for every payload shape, because those are one-byte only (`u8`):

- **Payloads.** `u16`, `u32`, `u64` and the struct `Pair` (`extern struct { a: u32, b: u16 }`).
- **Error sets.** The declared set `Failure` (the finite-domain operations) and `anyerror` (the
  operations without a domain; `writeAliasAny`, `cleanupAny`).
- **Functions.** `writeAlias*` (two pointer-try results of one union; in `writeAliasSigned` the
  first is cast to `*i16`), `cleanup*` (`defer` and
  `errdefer`, with distinct counters and with one counter for both) and `resetOnError*` (the
  `errdefer` overwrites the whole union).

The rules are the general ones of `ZigLean/Sep/Full/Try.lean` and `Typed.lean`. No rule was added
for a payload type: each theorem of `Payloads.lean` is `fsym` on each shape of the union.

| File | Role |
|---|---|
| `air/<version>/`, `air-payloads/<version>/` | Patched-compiler exports of `try_lifetimes.zig` and `try_payloads.zig` for 0.14.1, 0.15.2, 0.16.0 and 0.17.1 (x86_64-linux, baseline, ReleaseSafe), declared in `../exports.json` and pinned by `../exports.lock.json` (`scripts/fixture-exports.py`) |
| `TryLifetimes/<version>/PayloadsGen.lean` | The retained translations of `air-payloads/<version>/`. They are identical apart from the profile header and the namespace |
| `TryLifetimes/<version>/Payloads.lean` | Written for 0.17.1 and renamed for the older versions, as `Lifetimes.lean`. Total full-state triples (`FTotalTriple`) for every function and payload shape, for both outcomes of the union. Its `main` runs the same functions on concrete memories and compares them with the values that the native tests assert |
| `TryLifetimes/<version>/Gen.lean` | Their retained translations (`<version>` as a name: `V0_17_1`). They are identical apart from the profile header and the namespace, except that 0.14.1 has one extra `unwrapPayload` read in `danglingPayload` |
| `TryLifetimes/<version>/Lifetimes.lean` | Written for 0.17.1; the older versions' modules are that one with the version renamed (`scripts/fixtures.py instance ... --write` after an edit). Kernel-checked results of `freeOnError` and `readDangling` (the memory ends with every heap block freed). The thread steps by `fsym`: `readPayload` on a read share and `writePayload` on an owned union, the spawn targets `reader` and `writer`, and a result location (`errunion_payload_ptr_set`, then the payload write) by a thread that owns the union. Then 32 scheduler oracles for each concurrent case: the native results, and `.illegal` for the race |

`check.sh --native VERSION` runs the tests of `try_pointers.zig`, `try_aliases.zig` (the alias
fixture), `try_lifetimes.zig` and `try_payloads.zig` on x86_64-linux-musl, ReleaseSafe and Debug,
in Docker `linux/amd64`. They pass with stock 0.14.1, 0.15.2, 0.16.0 and 0.17.1.

## What is not covered

- **A payload read or written at another element type.** A cast of the payload pointer that
  keeps the element size (`*u16` to `*i16`, `writeAliasSigned`) is the same typed access and is
  covered. An access at
  another type (`*u32` as `*[4]u8` or `*[2]u16`) translates, but `fsym` has no rule for it: the
  union is owned as one typed value (`pts p a (.ok x)`) and no view exposes its payload as a
  cell of its own.
- **Overlapping, unequal unions.** Two error unions that share some bytes exist only after a
  pointer cast that exposes the error code as bytes. The translator rejects that cast
  (`a pointer cast exposing symbolic error storage as numeric or opaque bytes requires finalized
  error ordinals`), so no such program is modelled.
- **General rules for the freed union.** `freeOnError` and `readDangling` are checked by kernel
  evaluation over the hand-written `Zig.Allocator` model. With `--allocator-model translated`
  (the allocator as an open interface, `tests/roadmap/interfaces`) the translator rejects
  `mem.Allocator.create(Failure!u8)` and `destroy`, in every version: `create` casts the
  allocated bytes to `*Failure!u8` and `destroy` casts the union back to bytes, and both casts
  expose the error code as bytes (the diagnostic above).
- **Spawn and join.** The concurrent functions are checked by schedules. `fsym` walks the thread
  bodies and the spawn targets (`reader`, `writer`) on what each thread is given. The
  composition is not proved. No `CTriple` holds across a spawn or a join
  (`tests/roadmap/sep-full/SoloSpawnCX.lean`), so it is a statement in the protocol logic
  (`Proto.WP` with the threads' parts, `docs/sep-threads.md`), and the library has no protocol
  for a plain fork and join, only for programs with a lock. `concurrentReads` also needs a join
  that gathers the two readers' shares into the whole union, which `FOwned.join` rejects
  (`tests/roadmap/sep-full/ShareRaceCX.lean`, `gather_not_ownsRes`).

```sh
lake build ZigLean Air2Lean air2lean
bash tests/roadmap/try-pointers/lifetimes/check.sh
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/try-pointers/lifetimes/check.sh --native V
python3 -B scripts/fixture-exports.py verify try-pointers   # fresh exports equal air/ (export: rewrite)
```

The exports of `try_pointers.zig` and `try_aliases.zig` for every version are in
`../air-fresh/<version>` and `../aliases/air-fresh/<version>`. They translate body-identically to
the retained modules (`../compiler-qualification.json`, `versions`).
