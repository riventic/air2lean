# Translated allocators (`--allocator-model translated`, P1)

`page.zig` and `fba.zig` use `std.heap.page_allocator` and `std.heap.FixedBufferAllocator`
through `std.mem.Allocator`: `alloc`/`free`, `create`/`destroy`, `resize` and (for the fixed
buffer) `reset`. In translated mode ([allocator-model.md](../../../docs/allocator-model.md))
everything they reach is translated from its AIR: the `mem.Allocator` wrappers, the vtable
calls (indirect calls), `FixedBufferAllocator` and `PageAllocator`. Only `posix.mmap`,
`munmap` and `mremap` are trusted calls of the page-mapping model `ZigLean/Os/Mmap.lean`
(premise OSM-01).

| File | Content |
|---|---|
| `air/0.16.0/<prog>-<os>/` | Zig 0.16.0 AIR, x86_64-linux and aarch64-macos, `ReleaseSafe`: the call/function-value closure of the exported functions, cut at the panic handlers and at `posix.mmap`/`munmap`/`mremap` |
| `provenance.json` | source, compiler and per-file hashes. The exporter is this repository's (`zig-patch`: vtable initializers, `VTable` fields, schema 12 module identity); exporters before P0 fail on these programs |
| `AllocTranslated/*.lean` | the retained translations; `check.sh` requires the fresh ones to be byte-identical |
| `Eval.lean` | `#guard`s: the `FixedBufferAllocator` clients evaluate to the native results on both targets, also with other `@returnAddress` values; the page clients (`page_sum`, `page_create`, `page_resize`) evaluate through the page-mapping model to the native results of their target's page size (on the schedule of the oracle `fun _ => 0`), a zero-length allocation returns without a mapping, and a failing mapping takes the `OutOfMemory` path; the page allocator under allocation policies (M03: failure lists, index and size oracles, a cap, a list policy and its oracle form), with several failures in one run |
| `native.zig`, `expected.txt`, `expected-linux.txt` | the native run of the same functions with a stock Zig 0.16.0 on aarch64-macos (16 KiB pages) and on x86_64-linux (4 KiB pages: `page_resize(10, 5000)` is `false`, `resize` never calls `mremap` on a stack-grows-down target); `check.sh` picks the file by the host's page size |
| `PageThread.lean` | `alloc` (its in-thread reading, `CTriple.toSoloThread`), `free`, `resize` and `remap` as thread triples (`FTTriple`), `fallocSpec`'s statements, and `cAllocSpec`: the page allocator as an environment of an open `std.mem.Allocator` (`CAllocSpec`) |
| `PageObstruction.lean` | kernel-checked: the translated `PageAllocator` satisfies `AllocSpec` for no invariant that holds at program start, and `alloc` has no triple after a `free` of the hinted block ([alloc-page.md](../../../docs/alloc-page.md)) |
| `test_cli.py` | std mode rejects the same AIR; flag spelling; and each admission's neighbouring case fails closed: a translated `posix.mmap`, an `mmap` error set without `OutOfMemory`, a weak pointer compare-exchange, an integer pointer constant at address 0 or misaligned, a non-`usize` `@returnAddress` |

```sh
lake build ZigLean ZigLean.Sep.AllocSpec air2lean
bash tests/roadmap/alloc-translated/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.16.0/zig bash tests/roadmap/alloc-translated/check.sh   # also the native run
```

To re-export: `ZIG_AIR_JSON_DIR=<dir> zig build-obj -fno-emit-bin -OReleaseSafe
-fno-error-tracing -target <x86_64-linux|aarch64-macos> -mcpu=baseline <prog>.zig` with the
P0 exporter, keep the closure from the `<prog>.*` functions, then refresh `provenance.json`
and the translations.
