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

The proof side belongs to the full-state framework (on main since the arena landing,
[#279](https://github.com/riventic/air2lean/pull/279)).

* `callIndirect f arms d`: the generated chain with its last arm `d` (`throw .illegal` for a
  closed type, the environment's call `callC (extCall …)` for an open one). `fsym` folds either
  form (`callIndirect_fold_one`/`_ext`/`_cons`); one set of rules (`callIndirect_pos`/`_neg`/
  `_nil`) walks both.
* `Table.callOr t e f a` is the call through a table with the environment `e : EnvFn` (by
  function pointer); `Table.call` is the closed one (`EnvFn.closed`). `callOr_of_sel` (a closure
  pointer runs its arm, whatever the environment: `callOr_env_indep`) and `callOr_of_fresh` (a
  pointer no arm serves runs the environment) are the two readings, and
  `Table.contract_of_sel`/`contract_of_fresh` carry any contract `C` of the function that runs
  through them: the shared mechanism, which each interface instantiates.
* `std.mem.Allocator`: `AllocTables` carry an environment `env : AllocEnv` (one `EnvFn` per
  entry, closed by default), and `CVTable.dispatch t fns` is `callOr` per entry.
  `CVTable.dispatch_of_selects` (a vtable of the program is the implementation it selects) gives
  `CAllocSpec.dispatch`; `CVTable.dispatch_of_fresh` (a vtable none of whose entries is a
  function of the program is the environment's allocator `CVTable.env t.env fns`) gives
  `CAllocSpec.dispatch_env`. `CVTable.dispatch_closure_env`: the dispatch through a closure
  vtable does not depend on the environment, and `tests/roadmap/interfaces/Interfaces/ClosureCX.lean`
  has the counterexample to the unsound alternative: a design that used the environment's contract for
  a closure vtable would prove a double-issuing closure allocator correct.
* A client takes `CAllocSpec (CVTable.dispatch t fns) ctx I`: about the code that runs, so
  sound whichever arm it is; it is discharged by (2) or (3). A program without allocator
  functions takes `CAllocSpec (CVTable.env e fns) ctx I` (the same, by `dispatch_of_fresh`).
  The environment's entries are the generated `Ext.call<i>` for the entry types the program
  calls, and a parameter for the others (`Ext` has no field for a type the program never calls
  through an open pointer); a fixed `.illegal` there would make the assumption unsatisfiable,
  and the theorem vacuous. `Proofs/Lists/Alloc.lean` (`push`, `freeAll`),
  `tests/roadmap/interfaces/Interfaces/MixSpec.lean`.
* **One contract form for every interface function: `FnSpec P Q g := ∀ a, CTriple (P a) (g a)
  (Q a)`.** An interface states only its pre- and postcondition as plain assertions over the
  call's arguments (logical variables quantified outside: `∀ x, FnSpec (P x) (Q x) g`); there
  is no per-interface judgment. `CAllocSpec` is the allocator's four entries as four `CTriple`s
  with `FAllocSpec`'s pre- and postconditions; the one-thread reading `FAllocSpec` at every depth
  is derived (`CAllocSpec.solo`).
* **A proved allocator behind the open interface** (`ZigLean/Sep/Full/AllocBridge.lean`): a
  translated allocator's entries as thread triples (`FTTriple`, `FAllocSpec`'s pre- and
  postconditions; `fsym` proves them as it proves the sequential ones, each primitive local to
  the thread by its providers) give `CAllocSpec (CVTable.ofRaw vt)` (`CAllocSpec.ofRaw`), so an
  environment whose functions at `fns` run that code (`CVTable.env e fns = CVTable.ofRaw vt`)
  meets the contract a client assumes (`CAllocSpec.env_ofRaw`): EXT-05 discharged for that
  environment, for every allocator.
  `tests/roadmap/lists-fba` uses it to meet the premises of `append_spec` and `push_spec` with the
  translated `FixedBufferAllocator` at program start (their non-vacuity witnesses).
* Other interfaces use the same `Table`/`EnvFn`/`callOr` rules with their own `FnSpec`:
  `std.Random`'s `fillFn` is the second instance: `∀ A S K bs, FnSpec (randomFillPre ctx R A S K
  bs) (randomFillPost R A S K) fill` (with the generator's state `R`, it fills the slice with
  integer bytes and touches nothing else; `FnSpec.randomFill` is its `fsym` step), and
  `tests/roadmap/interfaces/Interfaces/RndSpec.lean` proves a die roll in 1..6 for every
  generator from it. E02's call sites take the same translator path (a `"function"` entry); its
  MemM `Contract.Holds.dispatch` is the closed reading (`dispatch []` is `.illegal`), and
  `Interfaces/CallbacksSpec.lean` is E02's `callbacks.zig` with its callback type opened:
  `evaluate` for every callback from the `FnSpec` (`visitPre`/`visitPost`) of the function the
  call runs.
* **A foreign function's arm** runs its registry model (`External.claim` of the footprint, then
  the model), whose evidence is a `MemM` contract (`External.Contract.Holds`).
  `FTriple.of_contract` reads that evidence as a sequential full-state triple, and
  `FTriple.claim`/`External.claim_run` is the access record. An interface contract (`FnSpec`, a
  `CTriple` in the calling thread) needs the arm as a thread triple, which needs the model to be
  local to the thread; EXT-02's evidence does not say so yet, so no interface proof uses a
  registry model's arm (open: extend EXT-02 so that a registered contract's `frame` bounds the
  model under concurrency, and derive `ThreadLocal` from it).

## Premise

EXT-05 (trusted): an implementation of an open interface that the environment supplies meets
the interface contract that the theorem assumes for it; the environment's functions are fixed
for the run (one `Ext`). Token: `Zig.extCall`.
