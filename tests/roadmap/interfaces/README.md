# Open interfaces (EXT-05)

Calls through an interface value that the caller passes in (docs/interfaces.md). Six programs:

- `lists`: `examples/lists/lists.zig` (`push`, `reverse`, `freeAll`, `sum`, `evens`), whose
  `std.mem.Allocator` parameter can be any allocator;
- `mix` (`mix.zig`): `make` takes an allocator, `withFba` passes the program's own
  `FixedBufferAllocator`, so one dispatch has both a closure arm and the environment arm;
- `rnd` (`rnd.zig`): `roll` reads a byte from a caller-supplied `std.Random` (the second
  interface);
- `callbacks`: E02's `callbacks.zig`, from `tests/roadmap/callbacks` (exports and the
  per-version registries of the foreign `ext_visit`), with the `interfaces` entry of
  `registry-callbacks-0.17.1.json` (that fixture's 0.17.1 registry plus the entry; `check.sh`
  checks the models agree) merged in: a bare callback type opened;
- `sentinel`: M04's `tests/roadmap/sentinel-realloc/source.zig` (`make`, `append`, `resize`,
  `release` of a `[:0]u8`), whose `std.mem.Allocator` parameter can be any allocator;
- `wide` (`wide.zig`): the same four operations on a `[:0]T` of an item type wider than a byte
  (`Buf(T)` at `u16`, `u32` and `u64`): `(len + 1) * @sizeOf(T)` bytes at `@alignOf(T)`;
- `kinds` (`kinds.zig`): the same four operations for other item kinds, `Buf(T, A, z)` at a
  non-zero sentinel (`[:0xff]u8`), an optional pointer item (`[:null]?*u8`), a float item
  (`[:0]f32`) and an over-aligned slice (`[:0]align(16) u16`, made by `allocWithOptions`), and
  `copy`, a sentinel copy of a slice (`dupeSentinel`, `dupeZ` before Zig 0.17).

`registry-alloc.json` opens `mem.Allocator.VTable` and `registry-random.json` opens `Random`
(the `interfaces` array of docs/external-models.md, premise EXT-05). `air/<version>/<program>`
are the patched-compiler exports for Zig 0.17.1, 0.16.0, 0.15.2 and 0.14.1, cut to the call
closure of each program's roots. `exports.json` declares them and `exports.lock.json` pins the
sources, the exporter and every file (`scripts/fixture-exports.py`,
[docs/coverage.md](../../../docs/coverage.md#fixture-exports)).

`check.sh` translates every program on every version, elaborates each translation, keeps the
0.17.1 translations byte for byte (`lists` as `Proofs/Lists/Open.lean`, the program of the
list proofs; the others as `Interfaces/{Mix,Rnd,Callbacks,Sentinel,Wide,Kinds}.lean`), and runs
`test_cli.py`:
an unused entry, a type opened twice, a struct without function-pointer fields, a non-EXT-05
premise and `--proof-api` are rejected; without the registry every call keeps the closed
`.illegal` arm. It then checks the proofs over the 0.17.1 translations (`fsym`, only the
standard axioms):

- `Proofs/Lists/Alloc.lean` (built with the `Proofs` library, not here): `push` and `freeAll` of
  `lists` for every allocator, from `CAllocSpec` of the environment's allocator at the vtable
  (`CVTable.env`);
- `MixSpec.lean`: `allocBytesAligned`, `create` and `make` of `mix` for every allocator, from
  `CAllocSpec` of the dispatch (`CVTable.dispatch`): one rule for the call whose arms are the
  FixedBufferAllocator and the environment;
- `ClosureCX.lean`: the dispatch through the FixedBufferAllocator's vtable is its translated
  code whatever the environment, and the counterexample to the unsound alternative: lifting the
  environment's contract to a vtable of the program would prove a double-issuing closure
  allocator correct;
- `RndSpec.lean`: `roll` returns 1 to 6 for every `std.Random` whose fill function meets the
  library's `std.Random` contract (`FnSpec` with `randomFillPre`/`randomFillPost`): the same
  `Table`/`EnvFn` mechanism with the second interface's contract;
- `CallbacksSpec.lean`: E02's `callbacks.zig` (`tests/roadmap/callbacks`, its exports and
  per-version registries) with the callback type `Visitor` opened:
  `evaluate` for every callback from the contract (`FnSpec` with `visitPre`/`visitPost`) of the
  function the call runs,
  and `sumVisit`'s dispatch meeting it by its translated code;
- `SentinelSpec.lean`: `make`, `append`, `resize` and `release` of `sentinel` for every
  allocator, from `CAllocSpec` of the environment's allocator (`CVTable.env`), through the
  generated `allocSentinel`, `realloc`/`reallocAdvanced` and `free` wrappers: a sentinel buffer
  of `len` items is a grant of `len + 1` bytes with the sentinel last, on success and on
  `error.OutOfMemory` (M04). It is also checked over the 0.16.0, 0.15.2 and 0.14.1 translations;
- `WideSpec.lean`: the same for `wide` (`make16_spec` … `release64_spec`). Also checked over the
  0.16.0, 0.15.2 and 0.14.1 translations;
- `KindsSpec.lean`: the same for the four item kinds of `kinds` (`makeFf_spec` …
  `releaseOver_spec`: the sentinels `0xff`, `null` and `+0.0`, and the grant at alignment 16),
  and `copy_spec`: the copy's grant holds the source's bytes and the sentinel after them. Also
  checked over the 0.16.0, 0.15.2 and 0.14.1 translations. A float has no `LawfulEnc` instance
  (a NaN's bytes are undefined), so its walk names the value-wise region rules of
  `ZigLean/Sep/Full/RegionEnc.lean`; the sentinel `+0.0` reads back because it is not a NaN.

The sentinel statements are generic (`ZigLean/Sep/Full/SentinelBuf.lean`): `made`, `appended`
and `resized` are stated once for every item size `sz`, log2 alignment `k` and sentinel bytes (a
buffer of `len` items is a grant of `(len + 1) * sz` bytes at alignment `2 ^ k`, the sentinel
item last), and `append_grant` and `resize_grant` are proved once from the shape of an instance's
code (`appendedAt`, `resizedAt`: the reallocated grant with the item and the sentinel written at
their byte offsets) and the size of its encoding. `SentinelSpec` is the instance `sz = 1`,
`k = 0`; `WideSpec` has `u16`, `u32` and `u64`; `KindsSpec` has `sz = 1, k = 0` with the sentinel
`0xff`, `sz = 8, k = 3` (`?*u8`, `null`), `sz = 4, k = 2` (`f32`) and `sz = 2, k = 4`
(`align(16) u16`). An instance supplies the walk of its own copy of the generated code and the
size of its encoding, nothing else. `copy_grant` is the same for a sentinel copy.

`check.sh` also runs the designated mutants of the translated allocator wrappers
(`tests/roadmap/callbacks/mutants.py`, root `sentinel`): the unchanged `SentinelSpec` and
`WideSpec` reject each one.

Re-export (needs the patched compilers): `scripts/fixture-exports.py export interfaces`.
