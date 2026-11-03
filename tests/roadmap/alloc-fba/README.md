# The translated FixedBufferAllocator against `FAllocSpec` (P4a)

`client.zig` uses `std.heap.FixedBufferAllocator` through `std.mem.Allocator`. In translated
mode (`--allocator-model translated`) everything it reaches is translated from its AIR: the
`std.mem.Allocator` wrappers, the vtable dispatch and the allocator. Nothing about the allocator
is modelled by hand.

| File | Content |
|---|---|
| `air/0.16.0/client-linux/` | Zig 0.16.0 AIR, x86_64-linux, `ReleaseSafe`: the call/function-value closure of the `client.*` exports, from the P0 exporter |
| `AllocFba/Gen.lean` | the retained translation; `check.sh` requires the fresh one to be byte-identical |
| `AllocFba/Impl.lean` | the translated entries as the raw vtable `impl` and the function pointers `fns` of the generated vtable constant |
| `AllocFba/Full.lean` | `FBA.fallocSpec : FAllocSpec FLogic.total impl ctx (FBA.finv ctx B γ e)` for every struct, buffer and epoch `e` of a reset ledger `γ` (`fsym` with the updates of the returns); `FBA.ledger` (the second `ResetLedger` instance), `FBA.freset_spec` (the whole epoch token for the next one), `FBA.fown_init` (a new ledger) |
| `AllocFba/Client.lean` | `Client.client_spec`: `fba_client v` returns, without an error, `1`–`4` (out of memory) or `v + v + (v +% 1)`, an `FTotalTriple` walked by `fsym` from the contracts only: the initialized FBA invariant (`fallocator_init`), the wrappers' contracts over `FBA.fallocSpec` and the reset contract (`freset_spec`) |
| `AllocFba/Eval.lean` | `#guard`s: the translated functions evaluate to `expected.txt` from `mem0` |
| `AllocFba/Wrappers.lean` | the generated `std.mem.Allocator` wrappers over `FAllocSpec`, for every allocator invariant (`fsym` walks their code; no `Wrap.*`) |
| `mutant.sh` | an `alloc` that does not advance `end_index` fails the `FBA.fallocSpec` proof |
| `native.zig`, `expected.txt` | the native run with a stock Zig 0.16.0 |
| `provenance.json`, `provenance.py` | source, compiler and AIR hashes |

The Lean files are the library `AllocFba` of the proof-fixture package
(`tests/roadmap/lakefile.toml`); `check.sh` builds it, and the modules it imports, with Lake
([build-cache.md](../../../docs/build-cache.md#proof-fixtures)).

```sh
lake build air2lean
bash tests/roadmap/alloc-fba/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.16.0/zig bash tests/roadmap/alloc-fba/check.sh   # also native
```

To re-export: `ZIG_AIR_JSON_DIR=<dir> zig build-obj -fno-emit-bin -OReleaseSafe
-fno-error-tracing -target x86_64-linux -mcpu=baseline client.zig` with the P0 exporter, keep
the closure of the `client.*` functions (stopping at `debug.FullPanic`), translate with
`--namespace AllocFba.Gen --prefix client. --allocator-model translated`, and run
`provenance.py <patched zig> <stock zig>`.

`client_spec` is stated for every state in which the client owns the `buffer` global's 16 bytes
(any address `A₀` with `A₀ + 16 ≤ 2^64`), a share of its block's extent with an untagged claim on
the allocator's 12 bytes, the vtable constant (`vtR`), and the running thread's stack token and
room for the client's 24-byte stack frame (`cur 0 ⋆ sp 0 S D`, `D + stackCharge 24 8 ≤ S`): the
stack room is an owned resource, not a premise. The `mem0` run is checked by
`AllocFba/Eval.lean`.
