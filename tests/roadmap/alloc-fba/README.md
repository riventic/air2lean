# The translated FixedBufferAllocator against `FAllocSpec` (P4a)

`client.zig` uses `std.heap.FixedBufferAllocator` through `std.mem.Allocator`. In translated
mode (`--allocator-model translated`) everything it reaches is translated from its AIR: the
`std.mem.Allocator` wrappers, the vtable dispatch and the allocator. Nothing about the allocator
is modelled by hand.

| File | Content |
|---|---|
| `air/{0.16.0,0.17.1}/client-linux/` | Zig 0.16.0 and 0.17.1 AIR, x86_64-linux, `ReleaseSafe`: the call/function-value closure of the `client.*` exports |
| `exports.json`, `exports.lock.json` | how the AIR is exported, and its pin (`scripts/fixture-exports.py`) |
| `AllocFba/Gen.lean` | the retained translation (Zig 0.17.1's); `check.sh` requires the fresh one to be byte-identical, and builds and audits the whole library again over 0.16.0's in a check tree (`scripts/check-tree.py`) |
| `AllocFba/Impl.lean` | the translated entries as the raw vtable `impl` and the function pointers `fns` of the generated vtable constant |
| `AllocFba/Full.lean` | `FBA.fallocSpec : FAllocSpec FLogic.total impl ctx (FBA.finv ctx B γ e)` for every struct, buffer and epoch `e` of a reset ledger `γ` (`fsym` with the updates of the returns); `FBA.ledger` (the second `ResetLedger` instance), `FBA.freset_spec` (the whole epoch token for the next one), `FBA.fown_init` (a new ledger); `FBA.fthread_alloc_at`: `alloc` exactly, for every request, over the state `FBA.fownAt` with `end_index` exposed (`some` and the new index when the padded request `ei + fpad B ei k + n` ends inside the buffer, else `null`), from which the contract's `alloc` is derived |
| `AllocFba/Client.lean` | `Client.client_spec`: `fba_client v` returns, without an error, `1`–`4` (out of memory) or `v + v + (v +% 1)`, an `FTotalTriple` walked by `fsym` from the contracts only: the initialized FBA invariant (`fallocator_init`), the wrappers' contracts over `FBA.fallocSpec` and the reset contract (`freset_spec`); `Client.client_start`: the same from the program's start memory `mem0` (the strength example) |
| `AllocFba/Eval.lean` | `#guard`s: the translated functions evaluate to `expected.txt` from `mem0` |
| `AllocFba/Wrappers.lean` | the generated `std.mem.Allocator` wrappers over `FAllocSpec`, for every allocator invariant (`fsym` walks their code; no `Wrap.*`); a wrapper that may push a result slot owns the stack token and room for it, one bound for every Zig version (`stackCharge 24 8`, `create`: `stackCharge 16 8`) |
| `mutant.sh` | an `alloc` that does not advance `end_index` fails the `FBA.fallocSpec` proof |
| `native.zig`, `expected.txt` | the native run with a stock Zig 0.16.0 or 0.17.1 (the same output) |

The Lean files are the library `AllocFba` of the proof-fixture package
(`tests/roadmap/lakefile.toml`); `check.sh` builds it, and the modules it imports, with Lake
([build-cache.md](../../../docs/build-cache.md#proof-fixtures)).

```sh
lake build air2lean
bash tests/roadmap/alloc-fba/check.sh
AIR2LEAN_NATIVE_ZIG=/path/to/zig-0.17.1/zig bash tests/roadmap/alloc-fba/check.sh   # also native
```

To re-export: `python3 -B scripts/fixture-exports.py export alloc-fba`, then translate again
(the command is in `check.sh`).

`client_spec` is stated for every state in which the client owns the `buffer` global's 16 bytes
(any address `A₀` with `A₀ + 16 ≤ 2^64`), a share of its block's extent with an untagged claim on
the allocator's 12 bytes, the vtable constant (`vtR`), and the running thread's stack token and
room for the client's 24-byte stack frame and, behind it, the slot of a wrapper it calls
(`cur 0 ⋆ sp 0 S D`, `D + stackCharge 24 8 + stackCharge 24 8 ≤ S`): the stack room is an owned
resource, not a premise. `Client.client_start` shows that this precondition is met at the
program's real start: for every placement with room for a stack of `S` bytes
(`stackCharge 24 8 + stackCharge 24 8 ≤ S`), the client run from `mem0` returns a result that
satisfies `Res` (`FTotalTriple.run_init_stack_claims`). The `mem0` run is checked by `AllocFba/Eval.lean`.

## Zig 0.16.0 and 0.17.1

One proof text holds over both translations: `check.sh` builds and audits the whole library over
0.17.1's (the retained one) and again over 0.16.0's in a check tree. The allocator's entries
(`heap_FixedBufferAllocator_*`) translate to the same code from both versions. The
`std.mem.Allocator` wrappers differ: 0.17.1's `alloc`, `reallocAdvanced`, `allocSentinel` and
`create` keep their result in a stack slot. Their contracts own the stack room for it (one
statement for both versions, engine ledger row `fba-0171-wrapper-stack`, option (a)); 0.16.0's
push none and frame the stack token. `fsym` evaluates `mem.Alignment.fromByteUnits` on its
literal in both (engine ledger row 21a).
