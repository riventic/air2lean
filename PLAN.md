# Plan

This file holds the design decisions, the version-support rules, the subset reference and the milestone history. For what is supported now, see the generated [support matrix](docs/support-matrix.md); for requirement classifications and remaining acceptance, see the [roadmap handoff](ROADMAP.md) and [remaining acceptance](remaining-acceptance.md).

## Historical milestones

Historical scope: each row records what that milestone delivered when it merged; the rows are not a current gap list. Later work supersedes some restrictions stated here. For example, M18's "`remap` always fails" precedes the bounded successful resize/remap model (M02); M22's integer-only atomics and its rejection of `.yield`, `.spinLoopHint`, `Futex.*`, `Mutex.*` and `Condition.*` precede T3–T5 and the yield/spin hint model (C03); M22's cut proof scope was closed by T4 (1) (`parallelCounter`); and M6/M13/M16b/M18/M19 input counts are the counts at merge time. The [support matrix](docs/support-matrix.md) and the [subset](#subset) describe the current scope.

| # | Milestone | State |
|---|---|---|
| M0 | Toolchain: patched Zig 0.15.2, Lean 4.34.0 | done |
| M1 | AIR JSON export (`zig-patch/`) | done |
| M2 | Semantics library (`ZigLean/`), incl. `loop_spec` | done |
| M3 | Parser + per-version normalizer | done |
| M4 | Translator: straight-line code, branches, calls | done |
| M5 | Translator: locals, loops, slices, structs | done |
| M6 | Differential tests: 4 examples, 18 functions × 300 inputs, 0 mismatches | done |
| M7 | Case study proofs (`Proofs/Basic/`) | 8 of 8 functions, incl. the loops `sum` and `totalWeightedTardiness` |
| M8 | CI, panic kinds in the diff test, `mutate.sh`, `no-sorry.sh` | done |
| M9 | Recursion: call groups → `mutual` + `partial_fixpoint` | done |
| M10 | Optionals and error unions (`?T`, `E!T`, `try`, `catch`, `orelse`, `.?`); JSON schema 2 | done |
| M11 | Zig 0.14.1: export patch, translator, CI job | done (Linux only) |
| M12 | Proofs for `recursion`, `options`, `errors` | done: 19 theorems over 18 functions, incl. mutual recursion, early-exit loops, `try` in a loop |
| M13 | Floats `f16`…`f128`: exact model (`ZigLean/Float/`), schema-3 export, translator, diff test (44,400 inputs, 0 mismatches on x86_64-linux), `compiler-rt` opt-in, proofs for `floats`/`floatconv` incl. rounding round trip and monotonicity | done |
| M14 | Zig 0.16.0 (default): one shared exporter (`Compat`), shared goldens and translation (`Canon.lean`), per-version float semantics (f128 `sqrt`, f128 `/` in `compiler-rt` mode), CI job | done |
| M15 | Enums (exhaustive and non-exhaustive) and tagged unions; places (a result built in `ret_ptr`, stores through field pointers of a local); JSON schema 4; `variants` example with proofs | done |
| M16a | Byte-level memory (`ZigLean/Mem/`: blocks, `Zig.Enc`, `Error.illegal`); single pointers `*T`, `?*T`; escaping locals as stack blocks; pure/memory function split; JSON schema 5 (sizes, alignments, field offsets); diff test with input buffers; `pointers` example with proofs (`swap` incl. `swap(p, p)`) | done |
| M16b | Slices `[]T`, many-pointers, sentinel pointers, arrays (`Vector`) in memory; `@memset`, `@memcpy`, `@memmove`; globals and string literals (`mem0`); `@tagName`, `@errorName`; `Zig.readSlice` for a pure callee; JSON schema 6 (pointer, slice and aggregate constants, globals table); `Canon.lean` item reads and always-true checks; `slices` example (20 functions, 6000 diff inputs) with proofs | done |
| M17 | Separation logic (`ZigLean/Sep/`): heaps, `∗`, `pts`, `arr`, `Triple` with the frame rule; rules for load, store, `@memmove`, `@memset`, `alloc`, `free`, loops (`loop_sep_spec`); `docs/proofs.md`; proofs `swap` (also `swap(p, p)`), `reverse` (a loop invariant), `copyWithin` (overlapping ranges), `fill`, the global counter. A tactic that reorders `∗` is not done: the proofs reorder heaps with `Heap.union_assoc` and `Heap.union_left_comm` | done |
| M18 | Allocator model (`ZigLean/Mem/Alloc.lean`: `create`, `destroy`, `alloc`, `alignedAlloc`, `free`, `dupe`, `remap`; allocation `failAt` fails; `remap` always fails); std code translated through `examples/<ex>/filter` (`ArrayListUnmanaged`); `docs/std-models.md`; `TestAllocator` in the diff test, with the live allocations after each call; JSON schema 7 (`ZIG_AIR_JSON_FILTER` list, `no_fields`); heap cells with the block kind; `loop_sep_ghost`; `lists` example (4 functions, 1200 diff inputs) with proofs `push`, `reverse` (a linked list), `freeAll` (no bytes owned after it). `append` (`Proofs/Lists/Append.lean`, T7): its `@memcpy` alias check holds because a new block lies above every live block (`Mem.AddrBelow`, part of `Triple`'s `Mem.Seq`) | done |
| M21 | Inline asm, register operands only, x86_64 (`docs/generated-code.md` §Inline asm): one `opaque` per distinct (source, ordered constraints, operand widths) (`Air2Lean/Emit.lean`'s `collectAsmOps`/`asmDefName`) — a proof gets only what it states about an op, no built-in axiom; JSON schema 8 (`assembly` instruction: source, volatile, clobbers, per-operand constraint/name/ref; `docs/air-json.md`); `Check.lean` rejects a memory or immediate constraint (an input may carry a matching constraint tying it to the sole output register, still a register operand). Diff test against a real archive implementation (`tests/diff/asm/asm.zig`), wired in with `@[csimp]` since the opaque has no defining equation and already lives in an imported module (`@[implemented_by]`/`@[extern]` cannot attach there); mutation (i) mutates the archive itself, the only diff-test mutation with no Lean-side equation to change. `asm` example (`bswap32`, `popcnt64`, `lzcnt64`) with proofs. Not in the 0.14.1 CI job: 0.14.1 has no inline-asm export support | done |
| M19 | SIMD `@Vector(N, T)` over integers and floats (`Zig.Vec`, `ZigLean/Vec.lean`): `splat`, `select`, `shuffle` (comptime mask, a `Zig.Vec` literal), `reduce` (`.Add`/`.Mul`/`.And`/`.Or`/`.Xor`/`.Min`/`.Max`, `Zig.Vec.reduce`/`reduceM`), lane-wise `add`/`sub`/`mul` (checked/wrapping/saturating, `Zig.Vec.map2`/`map2M`); JSON schema 9 (`vecLayout`); `vectors` example (17 functions: one or more per op above, a two-vector shuffle, `bool`-mask `@select`, float `.Min`/`.Max` reduce, a vector in memory; 5100 diff inputs, 0 mismatches) with proofs: `uDotWrap`'s full scalar spec (the explicit 4-term wrapping sum), `maxLane`'s domination property, `satAdd`'s per-lane spec, `reverse`'s exact shuffle, `fDot`'s scaffolding reduction only (float addition is not associative, so no scalar-sum claim), `interleave`'s exact two-vector shuffle, `pick`'s and `splatAdd`'s per-lane specs, `xorLanes`'s fold. `checkedAdd`: the lane-wise sum, or `.overflow` if a lane overflows (`checkedAdd_ok`, `checkedAdd_overflow`; `Vec.map2M_four` goes through `Vector.toArray_mapM`) | done |
| M22 | Atomics (`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`; JSON schema 10: `order`, `op`, `success_order`, `failure_order`) restricted to integer pointees; fork-join threads (`ZigLean/Mem/Thread.lean`: `Zig.Thread.spawn`/`join`, eager run, vector clocks, per-access footprint, race check giving `.illegal` for a non-atomic write race or `.nondet` for a non-commuting atomic race; `docs/std-models.md` §Thread model, `docs/generated-code.md` §Atomics and threads); rejects `Thread.detach`/`.yield`/`.spinLoopHint`/`Futex.*`/`Mutex.*`/`Condition.*` with a reason; `threads` example (`bump`, `parallelCounter`) with pinned `nondet`/`unspecified` counts for two racing functions (`tests/diff/threads/`); two new `mutate.sh` mutations, (k) and (l) (let `Xchg` commute; disable the race check). Proof: `Proofs/Threads/Proofs.lean`'s `bump_step` — one atomic-RMW step is race-free and keeps the counter invariant, sorry-free. The induction over `bump.loop4`'s variable iteration count and the 4-thread `spawn`/`join` composition needed for the full "counter = 4·n" theorem are not done: no proof in this repo reasons about a variable-bound loop over `Zig.MM` locals, and that induction is a bigger proof-engineering task than the rest of this milestone. The model itself is unaffected — it is checked by the diff test against real compiled/executed threaded Zig code, like every other example | done (proof scope cut, above) |
| M20 | Casts, layout and function pointers (`docs/generated-code.md` §Casts, layout and function pointers): `@intFromPtr`, `@ptrFromInt` (`castToNull`, `incorrectAlignment`), `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast`, `@fieldParentPtr`; packed structs (`Zig.Packed`, `ZigLean/Packed.lean`) with `@bitCast` to the backing integer and bit-pointers (`Zig.loadBits`/`storeBits`); `extern` structs; tagged unions in memory (`Check.lean`'s `unionLayout`); error unions in memory (`Zig.Enc (Except Zig.ErrName α)`, error codes as `Byte.errFrag`); function pointers (a 1-byte block per address-taken function, an indirect call dispatches on it); JSON schema 11 (`field_parent_ptr`, error-union pointer tags, a bit-pointer's `bit_offset`). bare unions (the exporter's `safety_tag`: a tagged union); `extern` and `packed` unions as bytes (`ZigLean/Union.lean`), with `union_init` and the 0.16.0 `bitcast` to a `packed` union; the padding bits of a `uN` with `N % 8 ≠ 0` undefined (`Byte.part`); `const` globals read-only (`Zig.BlockKind.constGlobal`: a write throws `.illegal`). `layout` example with proofs (packed round trip, `setMode`, `headerLen`, indirect calls; `Proofs/Layout/Mem.lean`: `Num` round trip, `setNum`, `numInt`, error-union `bump`, `writeTable` throws `.illegal`; in `ZigLean/Mem/Lemmas.lean` the error-union round trip and the `extern` union field read) and mutations (m), (n), (o), (p) | done |
| T1 | Threads that take turns (`ZigLean/Conc/`): the monad `ConcM` (a tree of sync ops with `CCPO`/`MonoBind`), the scheduler `Zig.Sched.run` over an oracle, concurrent functions in `Emit.lean` (`Tgt`, `dispatch`, a `yield` before each atomic op), the race rule (two atomic accesses never race; release/acquire clocks per location), the diff test's search over schedules. `Zig.Error.nondet` is gone. | done |
| T2 | RC11 (`ZigLean/Mem/Thread.lean`): per atomic location the writes in modification order; a read reads a message not older than its happens-before and its own reads; a write can go before newer messages; RMWs stay right after what they read; only acquire/release give happens-before edges (release sequences). `seq_cst` = `acq_rel` (no SC order: more results, never fewer). Each atomic op is one `pick` of the oracle. Example `atomics` (message passing, store buffering, 2+2W, a lock-free stack); proofs of the weak results under concrete schedules; mutations (w), (x) detected by the proof build. | done |
| T3 | Waits (0.16.0): `std.Io` is `Zig.Io`; `Io.futexWait`/`futexWaitUncancelable`/`futexWake` are sync ops of the scheduler (a wait blocks until a wake at its address); `Zig.Error.deadlock` when no thread can go on. `Io.Mutex` is translated from its std code (atomics on its `enum(u32)` state). Example `sync` (0.16.0 only, `examples/<ex>/zig-versions`): a counter under `Io.Mutex`, 4 in all 6,522 schedules. Mutations (y), (z) detected by the proof build. | done |
| T3b | `Io.Condition` and `Io.Event` translated from their std code (atomics on a packed struct; packed struct constants `.{ .f = v }`). `sync.handoff`: a hand-off through a condition and an event. | done |
| T3c (1) | `Io.Semaphore` and `Io.RwLock` translated from their std code, with no new model part. `sync.semaphoreCounter` (a semaphore with one permit guards a counter: 4), `sync.rwLockRead` (reads under the shared lock while a writer runs). | done |
| T4 (1) | Proofs over all schedules (`ZigLean/Conc/Logic.lean`): a protocol with a global invariant and a ghost value per thread (rely–guarantee), `run_sound` (partial correctness), `WP` rules for generated code and lemmas from a step's result back to the memory (`ZigLean/Conc/Lemmas.lean`). `parallelCounter n = 4 * n` under every schedule (`Proofs/Threads/Counter.lean`). | done |
| T4 (2) | Strict mode (`Proto.strict`): `run_safe`, no run gives an error; no deadlock for fork-join programs (`ready_ne`: a blocked join waits for a later thread). `parallelCounter` never errs under any schedule (`parallelCounter_safe`). | done |
| T4 (3) | Futex waits in strict mode: the futex queue is in `Mem` (`Thread.futexWait`, `futexWake`), a wait keeps `Live`, and `ready_ne` covers a chain of joins that ends at a sleeping thread. `mutexCounter` (the translated std `Io.Mutex`) gives 4 and never errs under every schedule (`Proofs/Sync/Mutex.lean`). Mutation (ac) detected by the proof build. | done |
| T4 (4) | Assertions on what a thread has seen, on the messages and clocks (`Proofs/Atomics/`): `mpRelAcq` gives 0 or 42 and never errs (release/acquire); every result of `mpRelaxed` is 0 (a relaxed read of 1 races); the lock-free `stackPush` loop gives 120 or 210 and never errs. Kit: atomic store results, one atomic location (`locIdx_single`), `Solo`, frames. Mutation (ad) detected by the proof build. | done |
| T3c (2) | 0.15.2's `std.Thread` sync primitives (`Thread.Mutex`, `Condition`, `ResetEvent`, `WaitGroup`) from their std code, example `threadsync`: `Thread.Futex` is the model; `Thread.Mutex` per OS (`Gen-darwin.lean`: `os_unfair_lock` as a model built from the model's ops). The golden check handles two instances of one generic function (content hash in the name). | done |
| T3c (3) | `Io.Group`: a task is a thread; `async`/`concurrent` a spawn that the group records (`Mem.groups`), `await`/`cancel` a join of each task. Example `iogroup`. The subset takes a `*anyopaque` as a value (`Io.Group`'s `token`). Mutation (ae) detected by the diff test. | done |
| T5 (1) | Concurrent separation logic (`ZigLean/Conc/Own.lean`, `ZigLean/Conc/Csl.lean`, `docs/proofs.md` §Concurrent separation logic): a clock owns a heap (`Mem.Owns`), thread triples (`TTriple`, the rules of `Triple` without `SingleThread`), the threads' parts (`Owned`) and their transfers at a step, a spawn and a join. `Proto.init` is a relation: the spawner picks the new thread's ghost value. Example `threads.disjoint` (two threads write two flags) with `disjoint_spec`/`disjoint_safe`. Mutation (af) detected by the proof build. | done |
| T5 (2) | A lock that owns a resource (`ZigLean/Conc/Lock.lean`, `ZigLean/Conc/LockRules.lean`, `docs/proofs.md` §A lock that owns a resource): the free lock owns the resource, `lock` gives it to the holder, `unlock` takes it back. The rules of the translated `Io.Mutex` (`wp_cas`, `wp_xchgLock`, `wp_wait`, `wp_xchgUnlock`, `wp_wake`) and of the steps outside its code are proved once, for every protocol with the lock (`Lock.Fits`). `mutexCounter` again with them (`Proofs/Sync/Mutex.lean`, 1037 lines, was 2166; 899 after T5 (3a)), and `groupCounter` (`Proofs/Iogroup/Counter.lean`, `WP.groupAsyncC`). Mutation (ac) detected by the proof build (`Inv.wake`). | done |
| T5 (3a) | More futex users with a lock, and shared atomic words (`ZigLean/Conc/Word.lean`, `docs/proofs.md` §A shared atomic word): a thread at another futex is `away` for the lock, and a lock step keeps the other futexes, the other atomic locations and the clocks before its newest message. `lock`/`unlock` of `Io.Mutex` for every protocol with the lock (`Proofs/Sync/Lock.lean`). `handoff` (`Io.Mutex`, `Io.Condition`, `Io.Event`): 7 under every schedule, no error (`Proofs/Sync/Handoff.lean`). | done |
| T5 (3b) (1) | `Thread.Mutex` (0.15.2): the lock's contended value is a parameter (`2` or `3`); rules for `tryLock`'s `or(1)`, a relaxed load and the move to the futex wait. `lock`/`unlock` of the translated `Thread.Mutex` for every protocol with the lock (`Proofs/Threadsync/Lock.lean`). `threadsync.mutexCounter`: 4 under every schedule, no error (`Proofs/Threadsync/Mutex.lean`). | done |
| T5 (3b) (2) | `Thread.ResetEvent`, `Thread.WaitGroup`: a shared atomic word has a width (`Word n nb`, `u32` or `u64`); the free lock's resource is owned below the clocks of the threads that are not `gone` (`Lock.LiveLe`), so a thread that is `gone` for the lock leaves it, and the only other thread can read the whole object (`Inv.readAll`). `threadsync.waitGroup`: 2 under every schedule, no error, `main`'s plain read of the `Tally` included (`Proofs/Threadsync/WaitGroup.lean`). Mutation (ac) detected by its proof build. | done |
| T5 (3b) (3) | `Thread.Condition` (0.15.2): `threadsync.handoff`: 7 under every schedule, no error (`Proofs/Threadsync/Handoff.lean`). `main`'s `Deadline` blocks are its own part of the heap, also while it holds the mutex. Mutation (ac) detected by proof build. | done |

Mutation check (`scripts/mutate.sh`, 5 CI jobs, one per line of `scripts/mutation-shards.txt`; each job checks that the lines name every mutation exactly once): each mutation must change a diff result or a pinned count, or break the proof build.

| # | Mutation | Detected by |
|---|---|---|
| (a) | `*` → `*%` in `scale` | 279 mismatches |
| (b) | `Zig.add` throws `.panic`, not `.overflow` | 166 mismatches |
| (c) | `orelse xs.len` → `orelse 0` in `findOr` | 144 mismatches |
| (d) | float rounding ties away from zero | 77 mismatches |
| (e) | `Light.ofInt?` accepts the unnamed value 3 | 1 mismatch |
| (f) | `Zig.store` writes one byte too few | 1101 mismatches |
| (g) | `Zig.memmove` writes one byte too few | 188 mismatches |
| (h) | an allocation never fails at `Mem.failAt` | 414 mismatches |
| (i) | the asm `bswap32` returns its input | 298 mismatches |
| (j) | `Zig.Vec.reduce` drops the last lane | 1083 mismatches |
| (k) | two atomic accesses race | 3 pinned counts |
| (l) | no data-race check | 1 pinned count |
| (m) | `Flags.ofBits` swaps two packed fields | 787 mismatches |
| (n) | no read-only check for a `const` global | 1 pinned count |
| (o) | every `Byte.part` rejected | 4 pinned counts |
| (p) | a set bit above an `N`-bit integer accepted | 2 pinned counts |
| (q) | `Zig.mod` throws `.panic` for a negative divisor | 387 mismatches |
| (r) | a `[3:0]u8` constant without its sentinel item | 32 mismatches |
| (s) | `Allocator.freeSentinel` frees `len` items, not `len + 1` | 1 pinned count |
| (t) | every `Mode` value is valid in a packed struct | 128 mismatches |
| (u) | a `bool` vector in memory has its lanes in reverse bit order | 220 mismatches |
| (v) | `cmpxchgAs` compares with the new value | 20 mismatches |
| (w) | an acquire read adopts no clock | proof build (`mp_sees_data`) |
| (x) | a write goes only at the end | proof build (`twoPlusTwoW_weak`) |
| (y) | a futex wait never blocks | proof build (`wait_alone_deadlock`) |
| (z) | no deadlock check | proof build (`wait_alone_deadlock`) |
| (aa) | an RMW can read a message with an RMW after it (a lost update) | proof build (`readOpts_chain`, which `parallelCounter_spec` needs) |
| (ab) | a spawned thread gets an empty clock (it does not happen after its spawner's writes) | proof build (`parallelCounter_safe`) |
| (ac) | a futex wake wakes no thread | proof build (`Inv.wake`, which `mutexCounter_safe` and `groupCounter_safe` need) |
| (ad) | a `cmpxchg` can succeed on a message with an RMW after it (a lost push) | proof build (`casOpts_pos`, which `stackPush_spec` needs) |
| (ae) | `Io.Group.await` does not join the last task | diff test (`iogroup`: the `unspecified` count) |
| (af) | `Thread.join` does not merge the joined thread's clock | proof build (`join_eq`; `Owned.join`, which `disjoint_safe` needs) |

## Current open work

Current open work is the incomplete part of the [requirement register](ROADMAP.md#requirement-register), summarized by area in the generated [support matrix](docs/support-matrix.md#requirement-register); the acceptance for each ID is in [remaining acceptance](remaining-acceptance.md). This section lists no finished work; `scripts/support-matrix.py check` rejects a `complete` ID or a finished item in this section.

The former T-series follow-ups now map to register IDs:

| Former item | Register | Remaining scope |
|---|---|---|
| T6 (docs, release tag) | Q08 | Q08: release record, gates and review ledger for one exact source/profile state. |
| T7 (theorem inventory) | D02, C14, F05 | D02: [docs/theorem-inventory.md](docs/theorem-inventory.md) (`scripts/theorem-inventory.py check`) gives each listed theorem a scope class, a precise domain and a current guarded check result per Zig version/target translation; an edit to a listed proof module or translation needs a new recorded build. C14: `snapshotPair_spec`/`snapshotPair_safe` hold for the restricted protocol only; reusable RwLock contracts remain. F05: `op128_spec` excludes the `f128` division-family and `@sqrt` selectors, which differ by version. |

Earlier T7 clauses whose proofs exist (`vectors.checkedAdd`, [docs/vector-proofs.md](docs/vector-proofs.md); `sync.semaphoreCounter`; `sync.rwLockRead`; 0.15.2 `Thread.Mutex` on macOS) are historical; their current check results are in docs/theorem-inventory.md.

## Decisions

| Topic | Decision | Reason |
|---|---|---|
| AIR source | A compiler patch writes one JSON file per function (`ZIG_AIR_JSON_DIR`). | A release build prints no AIR: `--verbose-air` on stock 0.15.2 exits 0 with no output. The text dump has no stable grammar. |
| JSON types | Type table: each type is written once, and uses refer to it by ID. | Inline types repeat deeply nested std types. One file grew too big to parse, and a run took 2.5 min. |
| Function filter | `ZIG_AIR_JSON_FILTER=<prefix>` | Skip std functions. |
| Build mode | `-OReleaseSafe -fno-error-tracing` | Safety checks stay explicit in AIR. `Debug` adds error-return-trace code to every function. |
| Translator language | Lean 4, no dependencies | One toolchain. Fast builds. |
| Integers | `BitVec n` + a signedness flag per operation | `bv_decide` and `BitVec` lemmas do the bit-level work. |
| Effects | `Zig.M σ α := StateT σ (ExceptT Error Option) α` | `throw` = safety panic. `none` = does not terminate. Lean core has `partial_fixpoint` support for this stack. |
| Locals | One generated `Locals` structure per function, held in the state. `load`/`store` = `get`/`modify`. | No SSA pass. It is sound because an `alloc` whose address escapes is a stack block in memory, not a `Locals` field (`Air2Lean/Memory.lean`). |
| Memory | Byte-level blocks (CompCert style); a pointer is a block and an offset; a function that uses memory returns `Zig.MemM α` (`docs/generated-code.md` §Memory) | Pointer bytes keep their block, so a stored pointer stays exact. A pure function keeps `Zig.Result`, so every v0 proof stays unchanged. |
| Control flow | One generated `Exit` type per function (`ret`, `br_k`, `rep_k`). A block is a `match` on the exit, and a loop is `Zig.loop`. | This maps AIR's structured `block`/`br`/`loop`/`repeat` directly. |
| Panics | A call to a `noreturn` function, `unreach` or `trap` becomes `throw`. | This is how Sema lowers safety checks. |
| Loop bodies | Each loop body is a named definition `f.loop<k>` that takes the values it reads as parameters. The repeat test is a named `f.again<k>`. | A proof can then name both and apply `Zig.loop_spec`. |
| Host compiler | `build.sh` requires a host `zig` of exactly the target version. | The Zig compiler source normally builds with the same release. Bootstrapping from source (`bootstrap.c`, CMake + LLVM) is out of scope. |

## Zig version support

The supported versions are in the generated matrix below. The design is meant to extend to later Zig releases (each `0.x` minor, later `1.x`), but each new version needs the steps below and its own qualification. The rule: one source for all versions; a version adds only its differences, each in one named place.

| Layer | Shared | Per version |
|---|---|---|
| Exporter | `zig-patch/air-json/json.zig` | its branch in `json.zig`'s `Compat`; `zig-patch/<version>/hook.patch` (the one-line call); URL + sha256 in `zig-patch/versions.toml` |
| JSON format | `docs/air-json.md`. Each file has `schema` and `zig_version`. AIR tags are written verbatim. | — |
| Canonical form | `Air2Lean/Air/Canon.lean`: rewrites the AIR patterns that differ between versions for the same code, and numbers instructions without debug instructions | — |
| Normalizer | `Air2Lean/Air/Normalize.lean`: one tag table → internal `Op` | a version case only for a subset tag that differs (none today) |
| Checker, emitter, `ZigLean` | work only on `Op` | the float ops whose result differs by version: `FCtx.zigVersion` in `Emit.lean` picks the def (`docs/floats.md` §Per-version differences) |
| AIR goldens | `tests/golden/<ex>/air/` | a file in `tests/golden/<version>/<ex>/air/` replaces the shared file of that name; a file in `tests/golden/<version>/<ex>/air-<os>/` replaces it on that host OS only (`std.Thread` is OS-specific std code) |
| Translation | `Proofs/<Ex>/Gen.lean` (the default version's, on Linux) | `tests/golden/<version>/<ex>/Gen.lean` where it differs; `tests/golden/<version>/<ex>/Gen-<os>.lean` where it differs on that host OS only (std code per OS, e.g. 0.15.2's `std.Thread.Mutex`). A proof holds for each translation (a `first` branch per translation, as `Proofs/Atomics/Stack.lean` has per version) |
| Proofs | `Proofs/<Ex>/*.lean`, built in each CI job (not the mutation job) against that version's translation | — |
| Float probe | `tests/floatprobe/expected.txt` | `expected.<version>.txt`: only the lines that differ |
| CI | one job per version (`.github/workflows/ci.yml`) | — |

Support matrix:

<!-- support-matrix:begin zig-versions (generated by scripts/support-matrix.py; do not edit by hand) -->
Supported: Zig **0.16.0** (default), **0.15.2** and **0.14.1**. Default example selection (`scripts/example-selection.sh` on x86_64; `asm` needs x86_64):

| Zig | CI | Examples | Not selected |
|---|---|---|---|
| 0.16.0 (default) | full job (pipeline, diff test, proofs); 5 mutation shards | `asm`, `atomics`, `basic`, `errors`, `floatconv`, `floatops`, `floats`, `iogroup`, `layout`, `lists`, `options`, `pointers`, `recursion`, `slices`, `sync`, `threads`, `variants`, `vectors` | `threadsync` |
| 0.15.2 | full job (pipeline, diff test, proofs) | `asm`, `atomics`, `basic`, `errors`, `floatconv`, `floatops`, `floats`, `layout`, `lists`, `options`, `pointers`, `recursion`, `slices`, `threads`, `threadsync`, `variants`, `vectors` | `iogroup`, `sync` |
| 0.14.1 | restricted job (translation and proofs; no diff harness) | `basic`, `errors`, `floatops`, `floats`, `layout`, `options`, `pointers`, `recursion`, `variants` | `asm`, `atomics`, `floatconv`, `iogroup`, `lists`, `slices`, `sync`, `threads`, `threadsync`, `vectors` |

Full matrix: [docs/support-matrix.md](docs/support-matrix.md).
<!-- support-matrix:end zig-versions -->

0.14.1 notes: of the examples it does not select, `floatconv` differs: 0.14.1 lowers the `@intFromFloat` check differently, `zig-patch/0.14.1/TAGS.md`; `slices` uses `@memmove`, which 0.14.1 does not have; `lists` uses `ArrayListUnmanaged`, another type in 0.14.1, `docs/std-models.md`; 0.14.1 has no inline-asm export support (M21); the other unselected examples' `zig-versions` files omit 0.14.1. The 0.14.1 compiler builds on Linux only: it cannot link on macOS 26. CI checks that its translation equals the committed one (or its `tests/golden/0.14.1/` override) and builds the proofs against it; its std cannot build the diff harness, so the diff test runs in the 0.16.0 and 0.15.2 jobs.

**To add a Zig version** (add only differences; never copy a shared file):
1. Add its source and host-zig URLs and sha256 to `zig-patch/versions.toml`.
2. Add `zig-patch/<version>/hook.patch` (the call after the function body is analysed in `src/Zcu/PerThread.zig`). Build with `zig-patch/build.sh <version>`; fix each compile error in a new `Compat` branch of `zig-patch/air-json/json.zig`.
3. Compare the AIR tag list in `src/Air.zig` with the previous version. Add the version to `supportedVersions` in `Normalize.lean`; add a tag case only if a subset tag differs.
4. `AIR2LEAN_ZIG_VERSION=<version> scripts/check.sh`. If the AIR of an example differs: if the same code gives a different AIR pattern, rewrite it in `Canon.lean` so that the translation stays shared; copy only the differing AIR files to `tests/golden/<version>/<ex>/air/`. Write each difference in `zig-patch/<version>/TAGS.md`.
5. Run `scripts/floatprobe.sh` with the version. Each changed float result is a model difference: a named def in `ZigLean/Float/`, picked in `Emit.lean` by `FCtx.zigVersion`, and a line in `tests/floatprobe/expected.<version>.txt`.
6. Add the version to the CI matrix, generate `coverage/<version>.json` (`docs/coverage.md`), then run `python3 scripts/support-matrix.py generate` and `check` to refresh the table above.

## Subset

| In | Out |
|---|---|
| integers of any width, `bool`, floats (`f16`…`f128`) | |
| checked, wrapping, saturating arithmetic | |
| `if`, `switch`, `while`, `for` | |
| local `var`, also one whose address escapes; a result built in `ret_ptr` | |
| read-only slices `[]const T` in a pure function; atomics on an integer, enum, `bool` or packed struct pointee (`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`); fork-join threads (`Thread.spawn`/`.join`) that take turns at sync ops, with a data-race check; futex waits and wakes; the std sync primitives translated from their std code (`Io.Mutex`, `Io.Condition`, `Io.Event`, `Io.Semaphore`, `Io.RwLock` in 0.16.0; `Thread.Mutex`, `Thread.Condition`, `Thread.ResetEvent`, `Thread.WaitGroup` in 0.15.2); `Io.Group` (a model: a task is a thread); yield and audited spin hints with no fairness guarantee ([model](docs/progress-hints.md)) | `Thread.detach`, `Io.futexWaitTimeout`, `Io.async`/`Future` |
| structs by value | `async` |
| calls, recursion; function pointers (an indirect call) | |
| `std.mem.Allocator` (a model with allocation failure), heap memory, translated std code (`ArrayListUnmanaged`) | a std function that is not translated and has no model |
| inline asm with register operands only, as an opaque function (x86_64); more than one output (lvalue outputs are stores) | asm with a memory operand, a read-write output (`+r`), or a `"memory"` clobber |
| `@Vector(N, T)` over integers, floats and `bool`: `splat`, `select`, `shuffle`, `reduce`, and every lane-wise op (arithmetic, division, `@min`/`@max`, `@addWithOverflow`, bitwise, shifts, comparisons, casts, float ops) | a pointer to a lane of a `bool` vector (the AIR file has no lane index) |
| optionals `?T`, error unions `E!T`, `try`, `catch`, `orelse` | |
| enums (also non-exhaustive), tagged unions `union(enum)` | |
| single pointers `*T`, `?*T`, aliasing; loads and stores of ints, `bool`, floats, pointers, optionals, enums and structs | `threadlocal` and `extern` globals |
| scalar nonoptional C/allowzero pointer null tests, casts and direct accesses; [scoped L05 gate](docs/null-pointers.md) | nullable-pointer storage, aggregates, optionals and projections remain outside the fragment; 0.16.0 macOS scoped gate passed; Linux CI rerun and other-version qualification pending |
| slices `[]T`, many-pointers `[*]T`, sentinel pointers, arrays in memory; `@memset`, `@memcpy`, `@memmove`; an array with a sentinel `[N:s]T` as one value (`N+1` items) | |
| globals (`var`, `const`; a write to a `const` global throws `.illegal`), string literals, `@tagName`, `@errorName` | |
| `@intFromPtr`, `@ptrFromInt`, `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast`, `@fieldParentPtr`; `packed` structs (also bit-pointers) and `extern` structs; tagged, bare, `extern` and `packed` unions and error unions in memory | a packed struct field other than an integer, `bool`, enum or packed struct; a `packed` union in a packed struct (a union value can have undefined bits, and a packed struct value is a `BitVec` without undefined bits) |

## Risks

| Risk | Mitigation |
|---|---|
| AIR changes each Zig release | Version-specific code only in the patch and the normalizer. Golden files show the exact change. |
| A safety check is lowered in a form the translator does not recognize, so the model is too optimistic | Differential tests on edge inputs (0, max, min, empty slice). |
| An escaping `alloc` makes the `Locals` model unsound | Any use of a place other than a `load`/`store`/field pointer makes the `alloc` a stack block (`Air2Lean/Memory.lean`). |
| The model's size rule for a type differs from the compiler's | `Check.lean` compares every type in memory with the exporter's `abi_size`/`abi_align` and rejects a difference. |
| Loop proofs are slow to write | Unfolding lemmas for `Zig.loop`. Prefer `for` over slices. |
