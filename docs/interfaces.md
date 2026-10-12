# Interfaces: calls through a vtable the program does not define

A Zig interface is a value that carries function pointers: `std.mem.Allocator` (`ptr` and a
`*const VTable` of four entries), `std.Io`, `std.Random` (`ptr` and `fillFn`), the
`*std.Io.Writer`/`Reader` vtables, a user-defined vtable struct, or a bare callback
`*const fn (*anyopaque, …) …` (E02). A function that takes such a value as a parameter
(`push(a: Allocator, …)`, every std container) calls whatever implementation its caller passes.
This document is the one mechanism by which every such call is modelled and proved.

## The problem

The translator emits a call through a function pointer as a test of the pointer against every
address-taken function of the callee's type (the callable-address table, L11), in a fixed
order, and `throw .illegal` for any other pointer (`Air2Lean/Emit.lean`). That is exact for a
closed program, but a function whose interface value comes from its caller has no
implementation in its closure: every call is `.illegal`, so no theorem "for every allocator" can
be stated, let alone proved.

## Semantics: prove all variants

1. **A client is proved once, for every implementation.** Its theorem quantifies over the
   environment and the vtable: `∀ fns vtp ctx I, vtR vtp fns ⋆ … ⇒ spec`, assuming only the
   interface contract of the implementation that the call reaches (`CAllocSpec … ctx I` for
   `std.mem.Allocator`).
2. **An implementation in the closure runs its own translated code.** The emitted dispatch tests
   the closure's functions first, exactly as today. A call through a closure vtable selects its
   arm (`Table.Sel`), and the contract at that arm is a proof about the translated code
   (`FBA.fallocSpec`, `PageAlloc.fallocSpec`, the arena), never an assumption.
3. **An implementation outside the closure enters only through the contract.** The last arm of
   the dispatch, taken only for a pointer that is no function of the closure, calls the
   environment. A theorem about it has the contract as a hypothesis; a claim lists premise
   EXT-05.
4. **No contract, no call.** A function type that no registry entry declares open keeps the
   `throw .illegal` arm, byte for byte as before.

## Translator

* **One registry.** The model registry (`--model-registry`, [external-models.md](external-models.md))
  gets an optional `interfaces` array. An entry declares a set of function types open:
  `{"interface": "std.mem.Allocator", "struct": "mem.Allocator.VTable", "contract":
  "Zig.Full.CAllocSpec", "premise": "EXT-05"}` opens the type of every function-pointer field of
  the struct; `"function": "<fn type name>"` opens one function type (a bare callback). The
  contract is a Lean identifier for the report; the premise must be EXT-05. An entry that opens
  no indirect call of the program, a struct without function-pointer fields and a type opened
  twice are rejected.
* **The environment.** The generated module declares `class Ext` with one field per open
  function type, `call<i> : Zig.Ptr → <params> → Zig.ConcM Tgt <result>` (the function pointer
  first), and `Ext.closed`, whose every field throws `.illegal`. Every concurrent function and
  `dispatch` take `[Ext]`. Running the program with `Ext.closed` is today's closed semantics.
* **The open arm.** The dispatch of an open type ends in `Zig.extCall (Ext.call<i> f args)`
  instead of `throw .illegal`. `Zig.extCall` is the identity on `Zig.ConcM`: a marker for the
  proof rules and the premise token of EXT-05. An open call can run any code of the
  environment (sync operations included), so every function that reaches one is concurrent
  (`concFunctions`).
* **Fail closed.** `--proof-api` rejects a program with open interfaces (its generated lemmas do
  not carry `[Ext]` yet; `--air-certificate` already excludes every model registry). The
  `std` allocator model has no vtable calls, so an `std.mem.Allocator` entry there is unused and
  rejected. All four Zig versions take the same path: the entry names the struct, not the
  version's signatures.

## Proof side (`ZigLean/Sep/Full/Dispatch.lean`)

The proof side belongs to the full-state framework and lands with it (`codex/alloc-arena-proof`,
lane `codex/alloc-param`); this section is its design.

* `callIndirect f arms d`: the generated chain with its last arm `d` (`throw .illegal` for a
  closed type, the environment's call for an open one). The fold lemmas read either form; one
  set of `fsym` rules (`callIndirect_pos`/`_neg`/`_nil`) walks both.
* `Table.callOr t e f a` is the call through a table with the environment `e : EnvFn` (by
  function pointer); `Table.call` is the closed one. `callOr_of_sel` (a closure pointer runs
  its arm, whatever the environment) and `callOr_of_fresh` (a pointer no arm serves runs the
  environment) are the two readings.
* For an interface, its tables carry an environment: `AllocTables.env`, `CVTable.dispatch t
  fns` per entry. `CAllocSpec.dispatch` (the arm it selects meets its implementation's
  specification) is unchanged; `CAllocSpec.dispatch_env` lifts the environment's contract for a
  vtable whose four entries are fresh (`AllocTables.Fresh`). `CAllocSpec.dispatch_closure_env`
  shows the dispatch through a closure vtable does not depend on the environment, and
  `tests/roadmap/interfaces` has the counterexample to the unsound alternative: a design that
  used the environment's contract for a closure vtable would prove a double-issuing closure
  allocator correct.
* A client takes `CAllocSpec (CVTable.dispatch t fns) ctx I`: about the code that runs, so
  sound whichever arm it is; it is discharged by (2) or (3).
* Other interfaces use the same `Table`/`EnvFn`/`callOr` rules with their own contract:
  `std.Random`'s `fillFn` (a `CTriple` contract: it writes the slice and nothing else) is the
  second instance in `tests/roadmap/interfaces`. E02's call sites take the same translator path
  (a `"function"` entry); its MemM `Contract.Holds.dispatch` is the closed reading
  (`dispatch []` is `.illegal`).

## Premise

EXT-05 (trusted): an implementation of an open interface that the environment supplies meets
the interface contract that the theorem assumes for it; the environment's functions are fixed
for the run (one `Ext`). Token: `Zig.extCall`.
