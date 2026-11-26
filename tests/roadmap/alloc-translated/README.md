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
| `air/{0.16.0,0.17.1}/<prog>-<os>/` | Zig 0.16.0 and 0.17.1 AIR of both programs, x86_64-linux and aarch64-macos, `ReleaseSafe`: the call/function-value closure of the exported functions, cut at the panic handlers and at `posix.mmap`/`munmap`/`mremap` |
| `exports.json`, `exports.lock.json` | how the AIR is exported, and its pin (`scripts/fixture-exports.py`; the exporter is this repository's `zig-patch`) |
| `AllocTranslated/{Page,Fba}{Linux,Macos}.lean` | the retained translations (Zig 0.17.1's); `check.sh` requires the fresh ones to be byte-identical, and builds, audits and runs the same library over the 0.16.0 translations in a check tree (`scripts/check-tree.py`) |
| `AllocTranslated/Eval.lean` | `#guard`s: the `FixedBufferAllocator` clients evaluate to the native results on both targets, also with other `@returnAddress` values; the page clients (`page_sum`, `page_create`, `page_resize`) evaluate through the page-mapping model to the native results of their target's page size (on the schedule of the oracle `fun _ => 0`), a zero-length allocation returns without a mapping, and a failing mapping takes the `OutOfMemory` path; the page allocator under allocation policies (M03: failure lists, index and size oracles, a cap, a list policy and its oracle form), with several failures in one run; the growths by `remap` and `realloc` (M02, below) |
| `native.zig`, `expected.txt`, `expected-linux.txt` | the native run of the same functions with a stock Zig 0.16.0 or 0.17.1 on aarch64-macos (16 KiB pages) and on x86_64-linux (4 KiB pages: `page_resize(10, 5000)` is `false`, `resize` never calls `mremap` on a stack-grows-down target); `check.sh` picks the file by the host's page size |
| `PageTok.lean` | the page allocator's token and invariant for a page size `P` (`ptok`, `pinv`), and the allocator state of `alloc`, the hint word with the knowledge of its target (`hown P`): one text for both targets |
| `PageSpec.lean`, `PageSpecMacos.lean` | `free`, `resize` and `remap` against `FAllocSpec`, total, on x86_64-linux and aarch64-macos |
| `PageAlloc.lean`, `PageAllocMacos.lean` | `alloc` (`alloc_ct`, a `CTriple` by the invariant and `fsym`) and the whole vtable, `fallocSpec : FAllocSpec FLogic.partial`, for alignments up to a page, on x86_64-linux and aarch64-macos; the creation triple from the null hint word (`fallocSpec.creation`; its admission in the start memory: `PageCreation.lean` for x86_64-linux); open: total correctness of `alloc` and alignments above a page ([alloc-page.md](../../../docs/alloc-page.md)) |
| `PageThread.lean` | x86_64-linux: `alloc` (its in-thread reading, `CTriple.toSoloThread`), `free`, `resize` and `remap` as thread triples (`FTTriple`), `fallocSpec`'s statements, and `cAllocSpec`: the page allocator as an environment of an open `std.mem.Allocator` (`CAllocSpec`) |
| `ListsPage.lean` | the memory-safety tutorial's refuted clients: the page allocator as the environment of `Proofs/Lists/Open.lean`'s allocator parameter (`page_spec`), the precondition of the tutorial client's properties (`Proofs/Lists/Client.lean`: `NoIllegal`, `NoLeak`) held in the program's start memory (`start`), and kernel-evaluated runs from it in which a double free and a read after free throw `.illegal` and a missing free leaves a node no resource of the precondition owns (`controls`), also when the freed page's address is reused (`reuse_happens`); the right client is the library's `buildThenFree` of one item |
| `PageObstruction.lean` | kernel-checked counterexamples behind the retired heap-only `AllocSpec` obstruction: the same live heap with or without a dead block's address gives different `alloc` outcomes; mixed-size and ambiguous-hint regressions ([alloc-page.md](../../../docs/alloc-page.md)) |
| `test_cli.py` | std mode rejects the same AIR; flag spelling; and each admission's neighbouring case fails closed: a translated `posix.mmap`, AIR of a Zig version without a reviewed `posix.zig` (0.15.2, 0.14.1), an `mmap` error set without `OutOfMemory`, a weak pointer compare-exchange, an integer pointer constant at address 0 or misaligned, a non-`usize` `@returnAddress` |

The Lean files are the library `AllocTranslated` of the proof-fixture package
(`tests/roadmap/lakefile.toml`); `check.sh` builds it, and the modules it imports, with Lake
([build-cache.md](../../../docs/build-cache.md#proof-fixtures)).

```sh
lake build air2lean
bash tests/roadmap/alloc-translated/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.17.1/zig bash tests/roadmap/alloc-translated/check.sh   # also the native run
```

The AIR (`air/{0.16.0,0.17.1}/{page,fba}-{linux,macos}`) is the export of `exports.json`, pinned
by `exports.lock.json`: `python3 -B scripts/fixture-exports.py export alloc-translated`
re-exports it, then translate again (the command is in `check.sh`).

## Growth by `remap` and `realloc` against the native run (M02)

`page.zig`'s `page_grow`, `page_grow_blocked` and `page_grow_stale` grow a block through
`Allocator.remap` (`how = 0`) or `Allocator.realloc` (`how = 1`) and return what they observe as
one word: 1 the call returned a block, 2 it is at another address, 4 the kept bytes are the old
ones, 8 the block's last byte is writable, 16 a neighbouring live block kept its bytes. A failed
call gives 4 alone (the old block is live with its bytes; it is written and freed afterwards).
`native.zig` prints the words of the native run, and `Eval.lean`'s `growLinux` and `growMacos`
print the model's words in the same format. `check.sh` compares the model's lines with the
`page_grow` lines of `expected-linux.txt` and `expected.txt` on every host, and the native run
with the file of the host's page size: the model and the native run of a target are compared
with the same file.

| Call | x86_64-linux (`mremap`) | aarch64-macos (no `mremap`) |
|---|---|---|
| `page_grow(81920, 10, 49152)`: the pages behind the block are free | `remap` 13, `realloc` 13: grown in place | `remap` 4: fails, old block unchanged; `realloc` 15: new mapping, copy, old one freed |
| `page_grow(10, 10, 20)`: within the page | 13, 13 | 13, 13 |
| `page_grow(49152, 49152, 10)`: a shrink | 13, 13 (`mremap`) | 13, 13 (tail `munmap`) |
| `page_grow(10, 10, 2^47)`: more than the address space | 4, 4: `mremap` (and `realloc`'s `mmap`) fail, old block unchanged | 4, 4 |
| `page_grow_blocked(10)`: one byte into a live neighbour's pages | 31, 31: moved, neighbour unchanged | `remap` 20: fails; `realloc` 31 |
| `page_grow_stale(10)`: the old address read after the move | fault, fault | `remap` 0 (no move); `realloc` fault |

The native runs: stock Zig 0.16.0 and 0.17.1 `ReleaseSafe` (the same output), x86_64-linux
natively (Linux 6.6, 4 KiB pages) and aarch64-macos (16 KiB pages). The model's lines are those of
both versions' translations (`check.sh` runs them over the 0.16.0 ones in its check tree), each
run with an 8 MiB main-thread stack reserve (`Eval.stackBytes`): natively no mapping meets the
stack, and without the reserve a stack block of 0.17.1's `realloc` wrapper lies right behind the
block, so the model's `mremap` would move it where the kernel grows it in place. A native fault (`SIGSEGV`/`SIGBUS` of the child process that
reads the stale address) is the model's `.illegal`. Where the kernel has a choice the model has
an oracle, and `Eval.lean` also runs the choices the kernel did not take: a move with room in
place (`mremapMoves`, 15), a denied `mremap` (4), and on x86_64-linux `realloc`'s copying path
after a denied `mremap` (15). The comparison is of these calls only; the claim for every call is
the proof (`PageSpec.remap_spec`, `resize_spec`; the `realloc` wrapper's contract is proved for
every allocator that meets `FAllocSpec` in `alloc-fba` and `interfaces`, not for this program's
instance of it). Under Rosetta the native run is refused: Rosetta aborts on the `2^47`-byte
growth where a kernel returns `ENOMEM`.
