# Translated `ArenaAllocator` (allocator milestone 2)

`arena.zig` uses `std.heap.ArenaAllocator` (Zig 0.16.0, lock-free) over a `FixedBufferAllocator`
and over `page_allocator`, through `std.mem.Allocator`. In translated mode
([allocator-model.md](../../../docs/allocator-model.md)) everything it reaches is translated from
its AIR: the arena, its child allocators, the `mem.Allocator` wrappers and the vtable calls. Only
`posix.mmap`, `munmap` and `mremap` are trusted (OSM-01). Design, obstructions and what is
proved: [alloc-arena.md](../../../docs/alloc-arena.md).

| File | Content |
|---|---|
| `air/0.16.0/arena-<os>/` | Zig 0.16.0 AIR, x86_64-linux and aarch64-macos, `ReleaseSafe`: the closure of the exported `arena.*` functions, cut at the panic handlers and at the OS rows |
| `air/0.16.0/arena-fixed-linux/` | the same clients over the patched arena (`upstream/arena-fix.patch` applied to the compiler's `lib/zig`), x86_64-linux |
| `provenance.json`, `provenance.py` | source, compiler and per-file hashes (the P0 exporter, as for `alloc-translated`) |
| `AllocArena/Arena{Linux,Macos,FixedLinux}.lean` | the retained translations; `check.sh` requires the fresh ones to be byte-identical |
| `Eval.lean` | `#guard`s: on the one-thread schedule the clients equal the native results (`expected.txt`, `expected-fixed.txt`), except `arena_oom_free` on the stock arena: O-E from real runs, illegal where native code has undefined behaviour |
| `native.zig`, `expected.txt`, `expected-fixed.txt` | the native run with a stock Zig 0.16.0 (independent of the page size), and with the patched standard library |
| `ArenaObstruction.lean` | kernel-checked: O-A, a foreign `free` on an empty arena panics (`arena_foreign_free`); O-E, `free` in the state a failed `alloc` leaves is `.illegal` (`arena_oob_free`) |
| `ArenaSpec.lean` | the stock arena's `free`, `resize` and `remap` against `FAllocSpec` (`free_spec`, `resize_spec`, `remap_spec`) over the ghost-epoch invariant `inv CI γ e ctx`; O-A excluded by ghost tokens that name their regions, O-F by live-block disjointness |
| `mutant.sh` | an `alloc` that reserves nothing is rejected by `Eval.lean` (`arena_two` sees overlapping allocations) |
| `upstream/oob_gep.zig` | the reproducer of O-E ([draft note](../../../docs/upstream/arena-oob-gep.md)): `free` after a failed `alloc` forms an out-of-bounds `inbounds` pointer |
| `upstream/arena-fix.patch` | the proposed fix (not filed): `alloc` gives a reservation that does not fit back, and sizes that overflow `usize` fail instead of panicking |
| `test_cli.py` | std mode rejects the same AIR; a cyclic type graph with error storage and an `unordered` load of a `bool` stay rejected |

```sh
lake build ZigLean ZigLean.Sep.Full.Conc ZigLean.Sep.Full.AtomicRules ZigLean.Sep.Full.Ghost \
  ZigLean.Sep.Full.AllocSpec ZigLean.Sep.AllocSpec.Ops air2lean
bash tests/roadmap/alloc-arena/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.16.0/zig bash tests/roadmap/alloc-arena/check.sh   # also the native run
```

To re-export: `ZIG_AIR_JSON_DIR=<dir> zig build-obj -fno-emit-bin -OReleaseSafe
-fno-error-tracing -target <x86_64-linux|aarch64-macos> -mcpu=baseline arena.zig` with the P0
exporter, keep the closure of the `arena.*` functions, then run `provenance.py` and retranslate.
The patched arena: the same command with `--zig-lib-dir <lib/zig with upstream/arena-fix.patch applied>`
(`patch -p1` in the lib directory), x86_64-linux only.
