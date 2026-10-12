# Open interfaces (EXT-05)

Calls through an interface value that the caller passes in (docs/interfaces.md). Four programs:

- `lists`: `examples/lists/lists.zig` (`push`, `freeAll`, `evens`), whose `std.mem.Allocator`
  parameter can be any allocator;
- `mix` (`mix.zig`): `make` takes an allocator, `withFba` passes the program's own
  `FixedBufferAllocator`, so one dispatch has both a closure arm and the environment arm;
- `rnd` (`rnd.zig`): `roll` reads a byte from a caller-supplied `std.Random` (the second
  interface);
- `callbacks`: E02's `callbacks.zig`, from `tests/roadmap/callbacks` (exports and the
  per-version registries of the foreign `ext_visit`), with `registry-callbacks.json`'s
  `interfaces` entry merged in: a bare callback type opened.

`registry-alloc.json` opens `mem.Allocator.VTable` and `registry-random.json` opens `Random`
(the `interfaces` array of docs/external-models.md, premise EXT-05). `air/<version>/<program>`
are the patched-compiler exports for Zig 0.17.0, 0.16.0, 0.15.2 and 0.14.1, cut to the call
closure of each program's roots (`closure.py`); `provenance.json` records their digests.

`check.sh` translates every program on every version, elaborates each translation, keeps the
0.17.0 translations as `Interfaces/{Lists,Mix,Rnd,Callbacks}.lean` byte for byte, and runs `test_cli.py`:
an unused entry, a type opened twice, a struct without function-pointer fields, a non-EXT-05
premise and `--proof-api` are rejected; without the registry every call keeps the closed
`.illegal` arm. It then checks the proofs over the 0.17.0 translations (`fsym`, only the
standard axioms):

- `ListsSpec.lean`: `create`, `push` and `destroy` of `lists` for every allocator, from
  `CAllocSpec` of the environment's allocator at the vtable (`CVTable.env`);
- `MixSpec.lean`: `allocBytesAligned`, `create` and `make` of `mix` for every allocator, from
  `CAllocSpec` of the dispatch (`CVTable.dispatch`): one rule for the call whose arms are the
  FixedBufferAllocator and the environment;
- `ClosureCX.lean`: the dispatch through the FixedBufferAllocator's vtable is its translated
  code whatever the environment, and the counterexample to the unsound alternative: lifting the
  environment's contract to a vtable of the program would prove a double-issuing closure
  allocator correct;
- `RndSpec.lean`: `roll` returns 1 to 6 for every `std.Random` whose fill function meets the
  library's `RandomSpec`: the same `Table`/`EnvFn` mechanism with the second interface's
  contract;
- `CallbacksSpec.lean`: E02's `callbacks.zig` (`tests/roadmap/callbacks`, its exports and
  per-version registries) with the callback type `Visitor` opened by `registry-callbacks.json`:
  `evaluate` for every callback from the contract `VisitSpec` of the function the call runs,
  and `sumVisit`'s dispatch meeting it by its translated code.

Re-export (needs the patched compilers): `tests/roadmap/interfaces/export.sh`.
