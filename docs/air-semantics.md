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
| Values | `Value.int (signed) (w) (BitVec w)`, `.bool`, `.void`, `.ptr (Zig.Ptr)` |
| SSA environment | `Env : InstId → Option (TyId × Value)`: each value with its AIR type, so a memory access takes its alignment and pointee from the pointer operand's type, as AIR does |
| Straight-line ops | `evalPure : Func → Env → Inst → Result Value` (arithmetic, comparisons, casts) and `evalMem : … → MemM Value` (loads, stores, field pointers, pointer casts and comparisons) |
| Control flow | `execBody`/`execInst`/`execSwitch : … → Zig.MM Frame Exit`, well-founded recursion over the nested bodies; `Exit` is `br target value`, `repeat target` or `ret value`; `loop` is `Zig.loop` |
| Memory | ZigLean's `Zig.Mem` (`Zig.MemM`); the state of a body is its stack frame (`Frame`, the blocks it allocated), freed at `ret` |
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
| Direct calls | `call` of a function in the program | `Zig.call`/`Zig.callM`/`Zig.callR`; a recursion clique is `mutual … partial_fixpoint` | fixpoint: `gen_fixpoint`; completeness by `fixpoint_induct` | **done** for pure functions; memory callers get `_sound` only; a recursive memory clique is excluded (its frame charge `Zig.enterFrame`, STK-01, is not AIR) |
| Loops | `loop`/`repeat` | a separate `f.loop<n>` definition under `Zig.loop` with an `f.again<n>` predicate | loop commutation ([§Loops](#loops)) | design |
| Escaping locals | `alloc` whose address escapes | `Zig.allocStack` at function entry, `Zig.free` at return, the pointer in a `Locals` field | frame simulation: entry allocation equals allocation at the `alloc` when nothing before it allocates ([§Locals](#locals)) | design |
| Promoted locals | `alloc` whose address does not escape | a field of the function's `Locals` structure | memory extension ([§Locals](#locals)) | design |
| Byte locals, aggregates, slices, optionals, error unions, unions, enums, floats, vectors, globals, atomics, threads, external models, indirect calls, asm | — | — | each needs its values in `Sem.Value` first | outside |

### Loops

The semantics runs a loop as `Zig.loop (execBody c body env) (Exit.again id)` over the frame
state and `Exit`; the generated code runs `Zig.loop (f.loop<n> captured…) f.again<n>` over its
`Locals` state and its own exit type `fExit`. The certificate needs:

1. an **exit encoding** `enc : fExit → Exit` (`.br<n> v ↦ .br n (enc v)`, `.rep<n> ↦ .rep n`,
   `.ret v ↦ .ret (enc v)`), printed by the generator from the same exit table the emitter uses;
2. a **loop commutation lemma**, proved once in `Sem.lean` by fixpoint induction in both
   directions: if `b₁ = encM b₂` (the body's run, its exit encoded, its state mapped) and
   `again₁ ∘ enc = again₂`, then `Zig.loop b₁ again₁ = encM (Zig.loop b₂ again₂)`;
3. per loop, a lemma `f_loop<n>` stated for every environment that binds the loop's free SSA
   values (hypotheses `env k = some (t, enc v)`, discharged by `simp` at the use), proved by the
   same normalization as `f_step` with the inner loops' lemmas in the simp set, used as a
   pre-rewrite (`simp only [↓f_loop<n>]`) before the body would be unfolded;
4. after a loop, the continuation reads an opaque exit: the step proof splits on the generated
   exit (`bind_congr`, `cases e`) and normalizes each case.

No committed example has a loop whose state lives outside promoted locals, so this lands with
the locals below.

### Locals

The semantics gives every `alloc` a `Zig.Mem` stack block; the emitter keeps a non-escaping
local as a structure field and allocates an escaping one at function entry. Both differ from
the semantics in memory: the semantics' memory has more blocks (shifting the ids of later
blocks), more footprint entries and bumped clocks. An equality certificate cannot hold; the
relation is a **memory extension**:

* `Mem.Ext ι m m'`: `m'` is `m` with extra blocks, related by a block-id injection `ι` (as in
  CompCert's `Mem.inject`), equal contents on the image of `ι`, extra footprint entries only on
  the extra blocks, and the current thread's clock only advanced;
* proved once: every ZigLean primitive in the fragment preserves `Mem.Ext` (loads, stores and
  projections through injected pointers give injected results; `alloc` extends `ι`), and
  `execBody` preserves it for a body whose extra blocks never reach an operand outside
  load/store (the emitter's own escape analysis, `Memory.escapingAllocs`, re-checked on the
  decoded `Func` by a decidable predicate);
* per function, the certificate relates the generated `Locals` fields to the extra blocks'
  contents (a definedness set computed by the generator: a field read before its first store
  is `.unspecified` in the semantics) and closes by `Mem.Ext` instead of equality.

The placement oracle is a function of block ids (SEM-07): the extension maps `σ` through `ι`,
so a theorem for every `σ` transfers.

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
| 1 `forwardReadOnlyCopies`, 5 `dropDeadAllocPlaceholders` | memory extension | the same `Mem.Ext` theory as promoted locals: the raw function's copy is an extra block |

The certificate then embeds the decoded **raw** AIR, and the round-trip check compares it with
`decode` of the golden JSON; `Canon.lean` leaves the trusted base for that function.

### How SEM-06 shrinks

[SEM-06](premises.md#sem-06) states that `Air2Lean.Sem` is the meaning of a decoded AIR
function. It is a premise because the meaning of AIR is Zig's compiler, not a document. It
shrinks in three steps:

1. **Now**: for a certified function, the trusted part is `Sem` (about 800 lines, most of it a
   table of AIR operations to ZigLean primitives), `Canon`, `Normalize` and `printFunc` (checked
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
| `basic` | `scale`, `clampAdd`, `absDiff`, `tardiness`, `classify` | `_run` |
| `recursion` | `gcd`, `fact` (self-recursive), `isEven`, `isOdd` (mutually recursive) | `_eq` |
| `pointers` | `addTo`, `swap`, `delay`, `dueOf`, `same` (memory) | `_run` |
| `threads` | `writeFlag` (memory) | `_run` |
| `vectors` | `sMod`, `sRem` | `_run` |
| `iogroup` | `debug.assert` | `_run` |
| `asm`, `atomics`, `errors`, `floatconv`, `floats`, `options`, `variants` | — | — |

18 of the 124 functions of these 13 examples certify. Every other function is listed in its
certificate with the first reason found:

| Reason | Functions |
|---|---|
| a parameter that is not an integer, `bool` or plain pointer (slices, structs, optionals, enums, floats, vectors, …) | 63 |
| a concurrent function (`Zig.ConcM`) | 25 |
| a return type outside the fragment | 8 |
| an instruction outside the fragment | 6 |
| a local (`alloc`) | 2 |
| a load of a type outside the fragment (a struct) | 1 |
| a recursive function that uses memory (`Zig.enterFrame`) | 1 |

### Checks (CI step "AIR semantics certificates")

* `tests/roadmap/air-semantics/test_cli.py`: the certificate flag leaves `Gen.lean`
  byte-identical; each committed certificate equals a fresh one; the certified set is the
  expected one and every other function is listed; flag misuse is rejected; no `sorry`,
  `admit` or `native_decide`.
* `lake build Proofs/<Ex>/AirCert` for every committed certificate.
* `tests/roadmap/air-semantics/test_lean.py`: the round trip (`RoundTrip.lean`: every
  embedded `Func` is the decoded golden AIR); nine one-operator mutations (arithmetic, a
  comparison, a returned constant, a field offset, a store's value, a pointer comparison) each
  break exactly their function's `_step`; a hand-written caller fixture gets `_eq`.

### Cost

Measured by `lake build` (elaboration of the certificate only; Apple M-series):

| Certificate | Functions | Lines | Bytes | Theorems | Check time |
|---|---|---|---|---|---|
| `Proofs/Basic/AirCert.lean` | 5 | 310 | 19,851 | 22 | 1.7 s |
| `Proofs/Pointers/AirCert.lean` | 5 | 311 | 23,144 | 22 | 1.7 s |
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

1. **Promoted and escaping locals, then loops** ([§Locals](#locals), [§Loops](#loops)):
   `Mem.Ext`, the frame simulation, exit encodings. Unlocks `pointers.sumTo` and, with
   slices, `basic.sum`.
2. **Slices and pointer arithmetic**: `Value.slice`, `slice_len`, `slice_elem_val`,
   `ptr_elem_val`, `ptr_add`; with (1) this covers the loops over slices in `basic`, `floats`,
   `slices`, `variants`.
3. **Optionals and error unions** (`is_non_null`, `optional_payload`, `wrap_optional`, `try`,
   `wrap_errunion_*`): `options`, `errors`, and the error paths of most std code.
4. **Aggregates and enums** (`struct_field_val`, `aggregate_init`, struct parameters, enum
   tags and `switch_br` on enums): `basic.weightedTardiness`, `variants`.
5. **Raw-AIR certificates** ([§Canonicalization](#canonicalization-v02)).
6. **Completeness for memory callers** and the stack budget for recursive memory cliques
   (`pointers.addDown`).
7. **Floats and vectors** (`Zig.Float` primitives, lane-wise operations).
8. **Concurrency**: a step relation over `Zig.ConcM` (atomics, threads, futex); then the
   `Thread.*` and `Io.*` functions that the 25 concurrent exclusions are.

Proposed classification: V01 and V02 stay **research**; this page is partial evidence for both.
