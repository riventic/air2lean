This is the callable-address part of roadmap L11. Every function-pointer value resolves
through one table: the address-taken functions (`fnRefs`), each a 1-byte function block in
`mem0` with its function type. A call through a pointer of type `T` dispatches over exactly
the table's functions of type `T`, whatever the pointer's origin: a constant callee, a global
initializer, a struct field, a parameter or memory. Any other address throws `.illegal`.

Static rules (`Air2Lean/Check.lean`): a constant callee must be a function pointer; a fixed
callee address (`fixedGlobalOrigin?`, through casts and single-branch blocks) must be the
zero-offset block of a function of the callee's type, else it is rejected as an unknown
executable address or an incompatible signature. The program check validates every table
target of the callee's type against the call, also for a constant callee. A stored or cast
function pointer carries no data storage; a data view of a function block stays rejected.

Proofs. `ZigLean.External.Callback` proves the table rules for any table with distinct
addresses: `resolve_complete` (every declared target of the signature runs itself),
`resolve_incompatible` (a target of another signature throws `.illegal`), `resolve_unknown`
(an address outside the table throws `.illegal`) and `resolve_ok`. `Bridge.lean` proves,
against the fresh generated program, that the emitted `callOnce` equals
`dispatchIn (resolve table "fn (u32) u32" impl)` for every pointer, and derives
completeness, incompatible-signature and unknown-address rejection for it.

Run from the repository root, under the root's serialized compiler guard:

```sh
AIR2LEAN_INDIRECT_CALLS_ZIG_VERSION=0.16.0 \
AIR2LEAN_INDIRECT_CALLS_ZIG_AIR=/absolute/path/to/patched-0.16.0/zig \
AIR2LEAN_INDIRECT_CALLS_ZIG_STOCK=/absolute/path/to/stock-0.16.0/zig \
LEAN_NUM_THREADS=1 bash tests/roadmap/indirect-calls/check.sh
```

`--synthetic-only` runs the hand-written schema-11 AIR fixtures of `Pipeline.lean`: seven
static rejections, the program-level signature check of a constant callee, the table and
call-graph inventory, and 20 kernel-decided observations appended to the generated
`Calls.lean` (each table target through a constant table, a constant callee, a parameter,
a mutable global, a stack and a constant struct field, caller memory and an integer
address; `.illegal` for another signature, a data block, other addresses and no block).
It then proves `Bridge.lean` against the fresh `Calls.olean` and runs three strict semantic
mutations (a dropped table target, an admitted unknown address, a wrong target). Only a
located false `decide` assertion counts as a kill. `python3
tests/roadmap/indirect-calls/test_harness.py` checks the inventory and mutation gates offline.

Full qualification also runs the stock source test, exports fresh ReleaseSafe AIR with
`source.` as its filter, requires every indirect caller to keep a call through an
instruction and every target to stay address-taken, translates it and decides 36 observed
outputs. `AIR2LEAN_INDIRECT_CALLS_KEEP_WORK=1` retains the artifacts.

Status: the synthetic recipe and the stock Zig 0.16.0 source test (aarch64-macos) passed.
The patched-compiler export and the native observations have not been run for this slice.
Executable addresses produced outside the table (for example by a callee that is not
translated, or by `@ptrFromInt` of an address the model does not know) are not admitted:
they throw `.illegal`.
