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

| File | Role |
|---|---|
| `air/<version>/` | Patched-compiler exports for 0.14.1, 0.15.2, 0.16.0 and 0.17.0 (x86_64-linux, baseline, ReleaseSafe; `check.sh --export`) |
| `gen/<version>.lean` | Their retained translations. They are identical apart from the profile header, except that 0.14.1 has one extra `unwrapPayload` read in `danglingPayload` |
| `TryLifetimes/Runtime.lean` | Kernel-checked results of `freeOnError` and `readDangling` (the memory ends with every heap block freed). Then 32 scheduler oracles for each concurrent case: the native results, and `.illegal` for the race |

`check.sh --native VERSION` runs the tests of `try_pointers.zig`, `try_aliases.zig` (the alias
fixture) and `try_lifetimes.zig` on x86_64-linux-musl, ReleaseSafe and Debug, in Docker
`linux/amd64`. They pass with stock 0.14.1, 0.15.2, 0.16.0 and 0.17.0.

```sh
lake build ZigLean Air2Lean air2lean
bash tests/roadmap/try-pointers/lifetimes/check.sh
AIR2LEAN_ZIG_NATIVE=<stock zig V> bash tests/roadmap/try-pointers/lifetimes/check.sh --native V
AIR2LEAN_ZIG_AIR=<patched zig V> bash tests/roadmap/try-pointers/lifetimes/check.sh --export V DIR
```

The exports of `try_pointers.zig` and `try_aliases.zig` for every version are in
`../air-fresh/<version>` and `../aliases/air-fresh/<version>`. They translate body-identically to
the retained modules (`../compiler-qualification.json`, `versions`).
