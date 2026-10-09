# The translated FixedBufferAllocator against `AllocSpec` (P4a)

`client.zig` uses `std.heap.FixedBufferAllocator` through `std.mem.Allocator`. In translated
mode (`--allocator-model translated`) everything it reaches is translated from its AIR: the
`std.mem.Allocator` wrappers, the vtable dispatch and the allocator. Nothing about the allocator
is modelled by hand.

| File | Content |
|---|---|
| `air/0.16.0/client-linux/` | Zig 0.16.0 AIR, x86_64-linux, `ReleaseSafe`: the call/function-value closure of the `client.*` exports, from the P0 exporter |
| `AllocFba/Gen.lean` | the retained translation; `check.sh` requires the fresh one to be byte-identical |
| `AllocFba/Bridge.lean` | every generated wrapper (`alloc`, `alignedAlloc`, `create`, `destroy`, `free` at alignments 1 and 4, `free` of a sentinel slice, `dupe`, `realloc`, `allocSentinel`, `allocBytesWithAlignment`) equals its `Wrap.*` over `dispatch impl fns a.vtable` |
| `AllocFba/Fba.lean` | `FBA.allocSpec : AllocSpec Logic.total impl ctx (FBA.inv ctx B)` for every struct and buffer; `grantSep`; `own_init`, `own_state`, `reset_spec` |
| `AllocFba/Client.lean` | `Client.client_spec`: `fba_client v` returns, without an error, `1`–`4` (out of memory) or `v + v + (v +% 1)`, proved from the contracts only |
| `Eval.lean` | `#guard`s: the translated functions evaluate to `expected.txt` from `mem0` |
| `mutant.sh` | an `alloc` that does not advance `end_index` fails the `FBA.allocSpec` proof |
| `native.zig`, `expected.txt` | the native run with a stock Zig 0.16.0 |
| `provenance.json`, `provenance.py` | source, compiler and AIR hashes |

```sh
lake build air2lean ZigLean.Sep.AllocSpec.Dispatch
bash tests/roadmap/alloc-fba/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.16.0/zig bash tests/roadmap/alloc-fba/check.sh   # also native
```

To re-export: `ZIG_AIR_JSON_DIR=<dir> zig build-obj -fno-emit-bin -OReleaseSafe
-fno-error-tracing -target x86_64-linux -mcpu=baseline client.zig` with the P0 exporter, keep
the closure of the `client.*` functions (stopping at `debug.FullPanic`), translate with
`--namespace AllocFba.Gen --prefix client. --allocator-model translated`, and run
`provenance.py <patched zig> <stock zig>`.

`client_spec` is stated for every memory in which the client owns the `buffer` global (any
address `A₀` with `A₀ + 16 ≤ 2^64`, the placement guarantee) and the vtable constant; the
`mem0` run is checked by `Eval.lean`.
