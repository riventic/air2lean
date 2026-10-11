# Formal AIR semantics and translation certificates (V01, V02)

Status: research. This page has two parts: the design of the semantics and of the
preservation proofs, which stays the plan until V01 and V02 close, and the state of the
implementation. Roadmap rows V01 (formal AIR semantics) and V02 (normalization and emission
preservation) remain open; [§Next fragments](#next-fragments) orders what is missing.

## Why

Today the translator (`Air2Lean/Air/Canon.lean`, `Normalize.lean`, `Check.lean`, `Emit.lean`,
about 10,000 lines) is trusted: a theorem about `Proofs/<Ex>/Gen.lean` is a theorem about the
Zig program only if the translator emitted the right Lean. The plan replaces that trust with a
small definition and kernel-checked evidence:

```
Zig ─ exporter ─▶ AIR JSON ─ parse ─▶ RawFunc ─ Canon ─▶ RawFunc ─ Normalize ─▶ Func ─ Check/Emit ─▶ Gen.lean
                                                                                │                    │
                                                                    Sem (V01) ──┘   certificate (V02)┘
```

* **V01** defines what a decoded AIR function means: `Air2Lean.Sem`, one interpreter over the
  translator's own `Func` and ZigLean's memory model.
* **V02** proves, per translated function, that the generated definition equals that meaning.
  For a certified function, `Check.lean` and `Emit.lean` (and later `Canon.lean`) leave the
  trusted base; the meaning itself is premise [SEM-06](premises.md#sem-06).

## Design

### The semantics (V01)

`Air2Lean/Sem.lean` is a **definitional interpreter** (a function, not a relation) over the
decoded AIR:

| Piece | Definition |
|---|---|
| Values | `Value.int (signed) (w) (BitVec w)`, `.bool`, `.void`, `.ptr (Zig.Ptr)`, `.slice (Zig.Slice)`, `.cell id` (the address of a register local); `.optNone`/`.optSome v` (an optional whose payload is not a pointer), `.errOk v`/`.errErr name` (an error union), `.errName name` (an error) |
| SSA environment | `Env : InstId → Option (TyId × Value)`: each value with its AIR type, so a memory access takes its alignment and pointee from the pointer operand's type, as AIR does |
| Straight-line ops | `evalPure : Func → Env → Inst → Result Value` (arithmetic, comparisons, casts) and `evalMem : … → MemM Value` (loads, stores, field pointers, pointer casts and comparisons) |
| Control flow | `execBody`/`execInst`/`execSwitch`/`execLoop : … → Zig.MM Frame Exit`, well-founded recursion over the nested bodies; `Exit` is `br target value`, `repeat target` or `ret value`; `loop` is `execLoop`, `Zig.loop` of the body |
| Memory | ZigLean's `Zig.Mem` (`Zig.MemM`); the state of a body is its `Frame`: the stack blocks it allocated (freed at `ret`) and its register locals' cells ([§Locals](#locals)) |
| Function | `execFunc call f args`: arguments checked against the parameter types (`argsOk`) |
| Program | `run p`: the least fixpoint (`partial_fixpoint`) of `execFunc` over a call oracle |
| Bottom | `stuck` (`Option.none`): non-termination and every out-of-fragment or ill-typed step |

Why a function: a decoded AIR function is deterministic given the memory, and ZigLean already
places every nondeterministic choice in `Zig.Mem` (block placement `Mem.place`, SEM-07) or in
the scheduler (`ZigLean/Conc`). The generated code runs over the same `Zig.MemM`, so the
semantics and the code share one memory model and their primitive operations (`Zig.add`,
`Zig.load`, `Zig.ptrProject`, …); the semantics fixes the meaning of the *program structure*
(SSA dataflow, operand typing, signedness, control flow, frames, calls) over them. A
concurrent function needs a step relation over ZigLean's scheduler instead (`Zig.ConcM`,
[§Next fragments](#next-fragments)); it stays outside until then.

Fail closed: an operation, type or shape outside the fragment is `stuck`, never a guess. A
certificate never holds for a stuck function, because the generated definition is defined.

### Emission preservation (V02): a certificate per function

Two ways to prove emission correct: a **verified emitter** (prove `Emit.lean` once, for a fixed
fragment) or **translation validation** (check each translation). `Emit.lean` is a 4,000-line
string generator with many strategies per construct; proving it would mean re-implementing it
in a provable form. Translation validation keeps the emitter as it is and makes it untrusted:
`--air-certificate` writes, beside `Gen.lean`, a Lean file that the kernel checks.

For each function `f` in the certificate fragment the file contains the decoded AIR `air_f`
(printed term, checked to be the decoded golden AIR) and:

* `f_step`: `(execFunc call air_f [args]).run m` equals the generated definition's result:
  `(fun v => (enc v, m)) <$> Gen.f args` for a function in `Zig.Result`, or
  `(fun r => (enc r.1, r.2)) <$> (Gen.f args).run m` for a function in `Zig.MemM` (same memory
  before and after). With certified callees, the generated program (`gen`) answers the calls.
* `f_fix`, `gen_fixpoint`, `run_le_gen`: the generated program satisfies every certified
  function's equation, so the program semantics is below it.
* `f_run` (no certified calls) or `f_sound` + `f_complete` + `f_eq` (calls, recursion):
  **equality** of `run` (the least fixpoint of the AIR program) and the generated definition.

The proofs are generic: one `simp only` with the `air_sem` simp set (`Air2Lean/SemAttr.lean`)
after one unfolding of the generated definition, and fixpoint induction over a generated
`partial_fixpoint` clique for completeness. Nothing in a certificate is chosen per function
by hand: the generator emits the same proof script for every function in the fragment, and a
function the script cannot normalize fails `lake build`, it is not silently skipped.

Per instruction family, the emission strategy and its proof obligation:

| Family | AIR | Emission (`Emit.lean`) | Certificate | Status |
|---|---|---|---|---|
| Integer arithmetic and safety | `add`/`sub`/`mul` (checked, wrapping, saturating), division, `rem`/`mod`, `min`/`max`, bitwise, `not`, comparisons, `bool_and`/`bool_or`, `intcast`, `trunc`; panic-handler calls | `let i ← Zig.<op> s a b` / `pure (…)`; `throw .<error>` | normalization: both sides reduce to the same ZigLean primitive | **done** |
| Blocks and branches | `block`/`br`, `cond_br`, `switch_br` on an integer, `ret`, `unreach`, `trap` | `match ← … with \| .br<n> …`, `if`, `if`-chain | normalization (the exits are literal constructors) | **done** |
| Memory through pointers | `load`/`store` of integers, `bool`, pointers; `struct_field_ptr` of a non-`packed` struct; pointer `bitcast`; pointer `==`/`!=`/order | `Zig.load`/`Zig.store`, `Zig.ptrProject p (·.add off)` (`pure p` at offset 0), `Zig.ptrEqAddr` | normalization over the same `Zig.MemM` (equal memory) | **done** (plain single/many pointers; not `allowzero`, `volatile`, bit-pointers) |
| Pointer arithmetic and slices | `ptr_add`/`ptr_sub`, `ptr_elem_ptr`/`slice_elem_ptr`, `ptr_elem_val`, `slice_elem_val`, `slice_len`, `slice_ptr`; slice parameters | `Zig.ptrProject p (·.elem size i)` (`·.elemSub`), `Zig.load … (p.elem size i)`, `Zig.checkIndex` then the item load; `Zig.Slice` | normalization; an item projection by zero bytes is `pure p` (`ptrProject_elem_zero`) | **done** for functions in `Zig.MemM` (plain slices: no sentinel, `volatile`, `allowzero`); not slicing (`slice`, whose bounds the translator checks from the operand's definition), `for`-length checks, `array_to_slice`; `slice_elem_ptr`, and items of an array or vector pointer, check their index against the item count on both sides (`Zig.checkIndex`; `Sem.checkCount`, which a constant in-range index normalizes away, as the translator omits it) |
| Pure-function slices | a `[]const T` parameter of a function without memory | an `Array` that the caller read (`Zig.readSlice`); `Zig.index`, `Zig.len` | a view ([§Pure-function slices](#pure-function-slices)): `_view` by normalization, `_step` up to read entries | **done** for integer and `bool` items, a function that reads memory only through its slices and calls only panic handlers; its callers are excluded |
| Optionals and error unions | `is_null`/`is_non_null`, `optional_payload`, `wrap_optional`, `is_err`/`is_non_err`, `unwrap_errunion_payload`/`_err`, `wrap_errunion_payload`/`_err`, `try`; their constants | `Option α`, `Except Zig.ErrName α`; `Zig.optPayload`, `Zig.isErr`, `Zig.unwrapPayload`, `Zig.unwrapErr`; `try` a `match` | normalization: the generated value encoded (`Value.ofOpt`, `Value.ofExcept`) and one lemma per operation (`optGet_ofOpt`, …) | **done** as values (registers, returns, calls) for payloads that are integers, `bool` or `void`; not pointer optionals, not in memory (`is_null_ptr`, `optional_payload_ptr`, …), not as parameters yet |
| Direct calls | `call` of a function in the program | `Zig.call`/`Zig.callM`/`Zig.callR`; a recursion clique is `mutual … partial_fixpoint` | fixpoint: `gen_fixpoint`; completeness by `fixpoint_induct` | **done** for pure functions; memory callers get `_sound` only; a recursive memory clique is excluded (its frame charge `Zig.enterFrame`, STK-01, is not AIR) |
| Loops | `loop`/`repeat` | a separate `f.loop<n>` definition under `Zig.loop` with an `f.again<n>` predicate | loop commutation ([§Loops](#loops)) | **done** (`loop_comm` in `Zig.MemM`, `loop_comm_pure` in `Zig.M`) |
| Escaping locals | `alloc` whose address is taken | `Zig.allocStack` at function entry, `Zig.free` at return, the pointer in a `Locals` field | normalization: the semantics allocates at the `alloc`, which is equal when only `arg`, `dbg_stmt` and other `alloc`s come before it ([§Locals](#locals)) | **done** (allocated before any effect, at the top level) |
| Register locals | `alloc` whose address is never taken | a field of the function's `Locals` structure | normalization: the semantics keeps the local in a frame cell too ([§Locals](#locals)) | **done** (at the top level, set right after the `alloc`, allocated before every loop) |
| Byte locals, aggregates, unions, enums, floats, vectors, globals, atomics, threads, external models, indirect calls, asm | — | — | each needs its values in `Sem.Value` first | outside |

### Loops

The semantics runs a loop as `execLoop c id body env`, which is `Zig.loop (execBody c body env)
(Exit.again id)` over the frame and `Exit`; the generated code runs `Zig.loop (f.loop<n>
captured…) f.again<n>` over its `Locals` state and its own exit type `fExit`. `execLoop` is a
definition of its own that the certificate's simp set does not unfold, so a whole loop is
rewritten by its lemma instead of being expanded. The machinery, in `Sem.lean` (proved once) and
generated per loop (`Certificate.loopCert`):

1. an **exit encoding** `enc_f : fExit → Exit` (`.br<n> v ↦ .br n (enc v)`, `.rep<n> ↦ .rep n`,
   `.ret v ↦ .ret (enc v)`), printed from the emitter's exit table (`CertShape`);
2. the **loop commutation lemma** `loop_comm`, proved by fixpoint induction in both directions:
   if one run of `b₁` from `F s` is `b₂`'s run from `s` with its exit encoded and its state
   mapped by `F`, and `again₁ ∘ enc = again₂`, then `Zig.loop b₁ again₁` from `F s` is
   `Zig.loop b₂ again₂` from `s`, mapped. `F` writes every register's cell from its `Locals`
   field (`Frame.setCell`, in increasing id order, the normal form of `Frame.setCell_comm`);
3. per loop, four lemmas: `f_loop<n>_body` (one iteration, for every environment that binds
   the loop's captured values and register addresses, by the same normalization as `f_step`,
   with the inner loops' lemmas in the simp set), `f_loop<n>_comm` (`loop_comm` of it),
   `f_loop<n>_exits` (below) and `f_loop<n>`, the rewrite used at the loop: the generated
   state and captured values decoded from the environment and the frame (`Env.val`,
   `Frame.cell`), with its side conditions discharged by `simp` at the use;
4. after a loop the continuation reads an opaque exit. The generated exit type also has the
   constructors of the loop's inner blocks and its own `repeat`, which a loop never returns but
   on which the two continuations differ (the semantics is stuck, the generated code panics).
   `wfBody` (every `br` and `repeat` targets an enclosing block or loop, decided on the decoded
   function) and `execBody_ok` (a well-formed body exits only to those), proved once, give
   `execLoop_ok`; `ok_transfer` carries it to the generated loop through `f_loop<n>_comm`.
   The step proof then splits on the generated exit (`bind_congr_ok`, `cases e`) and
   normalizes each possible case; the impossible ones close by their exit hypothesis.

### Locals

The semantics' `alloc` has two meanings, decided on the decoded AIR alone (`Sem.regAlloc`):

* a **register local**: every use of the `alloc` is the pointer of a `load` or `store`, or debug
  information (`regUse` lists the operations that may use it; any other operation counts as
  taking the address). It is a cell of the frame (`Frame.cells`, `none` while undefined): a
  `load` reads it (`.unspecified` if undefined, as undefined bytes are), a `store` writes it.
  These are Clight's non-addressable temporaries;
* otherwise an **addressable local**: a `Zig.Mem` stack block (`Zig.allocStack`), freed at
  `ret`.

The emitter keeps a non-escaping local in a `Locals` field and allocates an escaping one at
function entry. A function certifies only if the two agree: every register local is a field and
every escaping local a block (`Certificate.localsReason`, from the emitter's own `CertShape`);
otherwise it is excluded with the reason.

**Why not a memory extension.** The first design kept every `alloc` a block and related the
two memories by a block-id injection (`Mem.Ext`, as CompCert's `Mem.inject`). That relation is
not preserved by a later allocation. ZigLean's placement oracle proposes an address by block id
(SEM-07), and its fallback `Mem.top` lies past every block, dead or alive. An extra block for a
promoted local therefore shifts the id, and with it the address, of every later block. Values
differ, not just memories. From the same memory, with a placement that puts block 1 high and
block 2 low, `allocStack 4 4; q ← allocStack 4 4; ptrLt q g` gives `true`, and
`q ← allocStack 4 4; ptrLt q g` gives `false` (checked by `decide +kernel` in
`tests/roadmap/air-semantics/PlacementCounterexample.lean`). Only a statement
"for every `σ` there is a `σ'`", with `σ'` built from the semantics' own run (a prophecy
placement), would hold. That needs a whole-program simulation, not one normalization per
function.

**Why register cells are faithful.** A register local's address is unobservable: no operation
other than its own `load`s and `store`s receives it. A block for it could only change the
addresses of other blocks, and every theorem holds for every placement `σ` (SEM-07). So any
native address assignment of the remaining blocks is the one of some `σ`. Accesses to a cell
need no race check: no other thread can name it. The choice is part of SEM-06.

Escaping locals are blocks on both sides. The semantics allocates at the `alloc` and the
emitter at entry. These are equal when nothing with an effect runs before the last escaping
`alloc` (only `arg`, `dbg_stmt` and `alloc`), and when the order is the emitter's. Frees follow
the allocation order on both sides. A register local's field starts at its default, and its
cell starts undefined, so a register must be set by the instruction after its `alloc`. The
loop lemmas map every register into the frame, so registers must also be allocated before
every loop.

### Pure-function slices

The translator passes a `[]const T` parameter of a function without memory as an `Array`: the
caller reads every item (`Zig.readSlice`) and the callee indexes the array (`Zig.index`). In AIR the
callee reads each item from memory itself (`slice_elem_val`, a `Zig.load` that records a footprint
entry). The relation goes at the call boundary (`Air2Lean/SemView.lean`, proved once):

* **The view.** `Ctx.view` maps the `arg` instruction of a slice parameter to its items;
  `slice_elem_val` of a viewed slice then takes `Zig.index items k` instead of reading memory.
  `execFunc` has no view, so the hook is not part of the meaning of AIR. `execFuncV` runs a function
  with a view; a certificate proves `f_view`, that this run is the generated definition, by the same
  normalization as any function without memory.
* **The simulation** `execFunc_view`: for a function that reads memory only through viewed slices
  (`roBody`: register locals only, no item or slice pointers, `slice_elem_val` only of a viewed
  parameter, only panic-handler calls), from a memory in which each viewed slice holds the view's
  items (`Holds`), `execFunc` has the view's values and errors, and its memory is the starting
  memory up to read entries of the running thread (`UpToReads`: the same blocks, threads and every
  other field; only more read entries in the footprint and a larger own clock).
* **The materialization** `holds_of_readSlice`: the items that `Zig.readSlice` reads are such a
  view. Its read covers every item under the running thread before the call, so a concurrent
  writer is still caught as a race. It needs `Mem.ClockWf`: no recorded access has observed an
  access of the running thread that it has not made yet. Every memory that a run reaches has this
  property (a thread's own clock component only grows, another thread learns it only through a
  fork, join or release edge); the theorem states it as a hypothesis.

So `f_step` reads: if `Zig.readSlice` of each slice parameter succeeds from `m`, then
`execFunc` from `m` and the generated definition on the read items have the same values and
errors, and the semantics' memory is `m` up to read entries (`RelR`). A failing materialization
(an undefined byte in an item the function never reads, a range past the block) makes the generated
caller panic where AIR may not: the conservative direction ([CLAUDE.md](../CLAUDE.md), fail closed).

Out of range, `Zig.index` (and `Zig.vindex`) throw `.illegal`, as `Zig.checkIndex` does in memory
(`docs/illegal-behavior.md` row 2): the model of the item read checks its own illegal behaviour.

A function with a viewed slice has no fixpoint equation (`_fix`), so its callers are excluded
until a caller's step relates its materialization to the callee's view. With several slice
parameters, the step states each `Zig.readSlice` from the same `m`; the generated caller reads
them one after another, and memories after a read differ from `m` only in read entries, so that
caller step also has to carry `UpToReads` across the reads (the composition is not proved yet).

### Canonicalization (V02)

`Canon.lean`'s rewrites run before decoding, so the semantics today starts at canonical AIR
(Canon is trusted). The statement to prove, per rewrite `R` of the raw function `r`:

```
decode (R r) = c  →  decode r = d  →  (execFunc o d args).run m  ≈  (execFunc o c args).run m
```

where `decode` is `normalizeCanonical ∘ argRanks ∘ versionTags` (tag vocabulary and parameter
ranking are decoding, not rewriting) and `≈` is:

| Rewrite | Relation | Proof |
|---|---|---|
| 0 `versionTags`, 4 `argRanks` | part of `decode` | — |
| 6 `renumber` | equality | per function: both sides normalize to the same term |
| 3 `dropTrueChecks` | equality | needs the dropped condition's truth (`x ≤ x + y` after a checked add): a lemma per pattern, used by the normalization |
| 2 `itemReads` | equality | `ptr_elem_ptr` + `load` vs `ptr_elem_val`: one lemma over `Zig.ptrProject`/`Zig.load` (needs pointer arithmetic in the semantics) |
| 5 `dropDeadAllocPlaceholders` | equality | an `alloc` without uses is a register local ([§Locals](#locals)): no block on either side |
| 1 `forwardReadOnlyCopies` | memory extension up to placement | the raw function's copy is an extra block. A memory extension is not preserved by later allocations under ZigLean's placement ([§Locals](#locals)); this needs a "for every `σ` there is a `σ'`" statement with a prophecy placement, and stays future work |

The certificate then embeds the decoded **raw** AIR, and the round-trip check compares it with
`decode` of the golden JSON; `Canon.lean` leaves the trusted base for that function.

### How SEM-06 shrinks

[SEM-06](premises.md#sem-06) states that `Air2Lean.Sem` is the meaning of a decoded AIR
function. It is a premise because the meaning of AIR is Zig's compiler, not a document. It
shrinks in three steps:

1. **Now**: for a certified function, the trusted part is `Sem`'s definitions (about 750 of its
   lines, most of them a table of AIR operations to ZigLean primitives; the rest are proofs), `Canon`, `Normalize` and `printFunc` (checked
   by the round trip) — not `Check.lean`/`Emit.lean`.
2. **Raw-AIR certificates** ([§Canonicalization](#canonicalization-v02)) remove `Canon.lean`:
   SEM-06 then speaks of the decoded raw AIR.
3. **Conformance of `Sem` itself**: `execFunc` with a concrete oracle is executable. Running it
   on the differential corpus (`tests/diff`) against native results gives the semantics the same
   evidence the generated code has today (V03), so SEM-06 rests on a small executable definition
   that is tested directly, instead of on the translator.

Each step is per function: a function outside the certificate fragment keeps the old trust
(the whole translator, TRU-02).

## Implementation state

### Certified functions

`--air-certificate` runs on every example whose committed `Proofs/<Ex>/Gen.lean` is the
translation of its golden AIR (`tests/golden/<ex>/air`); the certificate is committed as
`Proofs/<Ex>/AirCert.lean` and CI checks that it is current and kernel-checks it. `layout`,
`threadsync` and `floatops` are not covered: their committed `Gen.lean` comes from other AIR.

| Example | Certified | Theorem |
|---|---|---|
| `basic` | `scale`, `clampAdd`, `absDiff`, `tardiness`, `classify`; `sum` (a slice parameter, a loop in `Zig.M`) | `_run`; `sum`: `_view`, `_step` up to reads |
| `errors` | `parseDigit` (an error-union return), `digitOrZero` (a call, `is_non_err`, both unwraps) | `_eq` |
| `options` | `find` (a slice parameter, an optional return) | `_view`, `_step` up to reads |
| `recursion` | `gcd`, `fact` (self-recursive), `isEven`, `isOdd` (mutually recursive) | `_eq` |
| `pointers` | `addTo`, `swap`, `delay`, `dueOf`, `same` (memory); `sumTo` (memory, register and escaping locals, a loop, a call) | `_run`; `sumTo`: `_sound` |
| `threads` | `writeFlag` (memory) | `_run` |
| `vectors` | `sMod`, `sRem` | `_run` |
| `iogroup` | `debug.assert` | `_run` |
| `asm`, `atomics`, `floatconv`, `floats`, `variants` | — | — |

23 of the 124 functions of these 13 examples certify (phase 2: 19; `basic.sum`, `errors.parseDigit`,
`errors.digitOrZero` and `options.find` are new). Every other function is listed in its certificate
with the first reason found:

| Reason | Functions |
|---|---|
| a parameter that is not an integer, `bool`, plain pointer or slice (structs, optionals, enums, floats, vectors, …) | 55 |
| a concurrent function (`Zig.ConcM`) | 25 |
| a return type outside the fragment (enums, unions, floats, …) | 7 |
| an instruction outside the fragment | 5 |
| a slice parameter whose items are not integers or `bool` (structs, floats) | 3 |
| a function with a slice parameter that calls a function (`errors.sumDigits`, `options.findOr`, `options.firstIndexPlusOne`) | 3 |
| an operand outside the fragment (`asm.divmod`: a local whose address is taken by an `asm` output) | 1 |
| a load of a type outside the fragment (a struct) | 1 |
| a recursive function that uses memory (`Zig.enterFrame`) | 1 |

The slices example has no committed certificate (its golden AIR mixes Zig versions); its Zig
0.15.2 files certify `at`, `bumpAt`, `prevItem`, `second` (pointer arithmetic, item loads),
`sumZ` (a loop over a many-pointer with register locals) and `sumSlice` (a pure function's slice)
in `test_lean.py`.

### Checks (CI step "AIR semantics certificates")

* `tests/roadmap/air-semantics/test_cli.py`: the certificate flag leaves `Gen.lean`
  byte-identical; each committed certificate equals a fresh one; the certified set is the
  expected one and every other function is listed; flag misuse is rejected; no `sorry`,
  `admit` or `native_decide`; a certified memory function with calls has `_sound`.
* `lake build Proofs/<Ex>/AirCert` for every committed certificate.
* `tests/roadmap/air-semantics/test_lean.py`: the round trip (`RoundTrip.lean`: every
  embedded `Func` is the decoded golden AIR); ten one-operator mutations (arithmetic, a
  comparison, a returned constant, a field offset, a store's value, a pointer comparison, a
  loop's increment) each break exactly their function's `_step` (the loop's: its iteration
  lemma); a hand-written caller fixture gets `_eq`; the Zig 0.15.2 slices goldens certify their
  expected functions and the fresh certificate checks.

### Cost

Measured by `lake build` (elaboration of the certificate only; Apple M-series):

| Certificate | Functions | Lines | Bytes | Theorems | Check time |
|---|---|---|---|---|---|
| `Proofs/Basic/AirCert.lean` | 5 | 310 | 19,851 | 22 | 1.7 s |
| `Proofs/Pointers/AirCert.lean` | 6 (one with a loop) | 517 | 39,440 | 34 | 7.1 s |
| `Proofs/Recursion/AirCert.lean` | 4 | 486 | 30,541 | 27 | 6.0 s |
| `Proofs/Vectors/AirCert.lean` | 2 | 174 | 11,613 | 11 | 1.8 s |
| `Proofs/Threads/AirCert.lean` | 1 | 95 | 6,639 | 6 | 1.4 s |

A function without calls costs one normalization; a function with calls adds an oracle-abstracted
normalization and its callees' argument inversions (completeness), so recursion costs more per
instruction. Each theorem unfolds only its own function.

### Trusted base of a certificate

* the exporter and the compiler (V03); JSON parsing, `Canon.lean` and `Normalize.lean`;
* `printFunc`, checked by the round trip (it prints every field, so equal prints are equal
  values);
* `Sem` itself and ZigLean's primitives and memory model, shared with the generated code
  (SEM-06, and the premises of `docs/premises.md` for the primitives);
* `Sem.panicOf?`, the literal panic-handler table (the translator's `panicErrorFor?` for the
  same names).

`Check.lean` and `Emit.lean` are not trusted for a certified function.

## Next fragments

Ordered by the functions they unlock in the committed examples:

1. **Calls at the slice boundary**: a view function that calls (`errors.sumDigits` calls
   `parseDigit`, then `try`; the simulation needs the oracle memory-free on its callees), and a
   caller of a view function (`options.findOr`, `options.firstIndexPlusOne`: its step relates its
   own materialization to the callee's view). `try` is in the semantics and the fragment, but no
   committed example certifies one yet.
2. **Optionals and error unions as parameters and in memory** (`pointers.setOpt`,
   `pointers.bumpOpt`: `is_null_ptr`, `optional_payload_ptr`, the `Zig.optEnc` layout), and
   pointer optionals `?*T` (an address, `Zig.ptrIsNull`).
3. **Aggregates and enums** (`struct_field_val`, `aggregate_init`, struct parameters, enum
   tags and `switch_br` on enums): `basic.weightedTardiness`, `variants`.
4. **Wider locals and loops**: registers allocated inside or after a loop, escaping locals
   allocated after an effect, nested loops in a function with escaping locals, slicing
   (`slice`) once the semantics states the bounds the translator checks.
5. **Raw-AIR certificates** ([§Canonicalization](#canonicalization-v02)), with the placement
   obstruction of [§Locals](#locals) for `forwardReadOnlyCopies`.
6. **Completeness for memory callers** and the stack budget for recursive memory cliques
   (`pointers.addDown`); `pointers.sumTo` has `_sound` only.
7. **Floats and vectors** (`Zig.Float` primitives, lane-wise operations).
8. **Concurrency**: a step relation over `Zig.ConcM` (atomics, threads, futex); then the
   `Thread.*` and `Io.*` functions that the 25 concurrent exclusions are.

Proposed classification: V01 and V02 stay **research**; this page is partial evidence for both.
